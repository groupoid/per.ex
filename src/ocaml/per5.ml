(* Copyright (c) 2016—2025 Groupoid Infinity *)

(* TYPE CHECKER CORE LANGUAGE *)

let trace: bool = false

type level = int
type name = string

type term =
  | Var of name | Universe of level
  | Pi of name * term * term | Lam of name * term * term | App of term * term
  | Sigma of name * term * term | Pair of term * term | Fst of term | Snd of term
  | Id of term * term * term | Refl of term | J of term * term * term * term * term * term  (* J A a b C d p *)
  | Inductive of inductive | Constr of int * inductive * term list | Ind of inductive * term * term list * term
and inductive = { name : string; params : (name * term) list; level : level; constrs : (int * term) list }

type env = (string * inductive) list
type context = (name * term) list
type subst_map = (name * term) list

let empty_env : env = []
let empty_ctx : context = []
let add_var ctx x ty = (x, ty) :: ctx

exception TypeError of string

let lookup_var ctx x =
    if (trace) then (Printf.printf "Looking up %s in context: [" x;
                 (*  List.iter (fun (n, ty) -> Printf.printf "(%s, " n; print_term ty; print_string "); ") ctx; *)
                     print_endline "]");
    try Some (List.assoc x ctx) with Not_found -> None

let rec subst_many m t =
    match t with
    | Var x -> (try List.assoc x m with Not_found -> t)
    | Pi (x, a, b) -> let m' = List.filter (fun (y, _) -> y <> x) m in Pi (x, subst_many m a, subst_many m' b)
    | Lam (x, d, b) -> let m' = List.filter (fun (y, _) -> y <> x) m in Lam (x, subst_many m d, subst_many m' b)
    | App (f, arg) -> App (subst_many m f, subst_many m arg)
    | Sigma (x, a, b) -> let m' = List.filter (fun (y, _) -> y <> x) m in Sigma (x, subst_many m a, subst_many m' b)
    | Pair (a, b) -> Pair (subst_many m a, subst_many m b)
    | Fst t -> Fst (subst_many m t)
    | Snd t -> Snd (subst_many m t)
    | Id (ty, a, b) -> Id (subst_many m ty, subst_many m a, subst_many m b)
    | Refl t -> Refl (subst_many m t)
    | Inductive d -> Inductive d
    | Constr (j, d, args) -> Constr (j, d, List.map (subst_many m) args)
    | Ind (d, p, cases, t') -> Ind (d, subst_many m p, List.map (subst_many m) cases, subst_many m t')
    | J (ty, a, b, c, d, p) -> J (subst_many m ty, subst_many m a, subst_many m b, subst_many m c, subst_many m d, subst_many m p)
    | _ -> t

let subst x s t = subst_many [(x, s)] t

let rec equal env ctx t1' t2' =
    let t1 = normalize env ctx t1' in
    let t2 = normalize env ctx t2' in
    equal' env ctx t1 t2

and equal' env ctx t1 t2 =
    match t1, t2 with
    | Var x, Var y -> x = y
    | Universe i, Universe j -> i <= j
    | Pi (x, a, b), Pi (y, a', b') -> equal' env ctx a a' && equal' env (add_var ctx x a) b (subst y (Var x) b')
    | Lam (x, d, b), Lam (y, d', b') -> equal' env ctx d d' && equal' env (add_var ctx x d) b (subst y (Var x) b')
    | Lam (x, d, b), t when not (is_lam t) -> let x_var = Var x in equal' env ctx b (App (t, x_var)) && (match infer env ctx t with | Pi (y, a, b') -> equal' env ctx d a | _ -> false)
    | t, Lam (x, d, b) when not (is_lam t) -> let x_var = Var x in equal' env ctx (App (t, x_var)) b && (match infer env ctx t with | Pi (y, a, b') -> equal' env ctx a d | _ -> false)
    | App (f, arg), App (f', arg') -> equal' env ctx f f' && equal' env ctx arg arg'
    | Sigma (x, a, b), Sigma (y, a', b') -> equal' env ctx a a' && equal' env (add_var ctx x a) b (subst y (Var x) b')
    | Pair (a, b), Pair (a', b') -> equal' env ctx a a' && equal' env ctx b b'
    | Fst t, Fst t' -> equal' env ctx t t'
    | Snd t, Snd t' -> equal' env ctx t t'
    | Id (ty, a, b), Id (ty', a', b') -> equal' env ctx ty ty' && equal' env ctx a a' && equal' env ctx b b'
    | Refl t, Refl t' -> equal' env ctx t t'
    | Inductive d1, Inductive d2 -> d1.name = d2.name && d1.level = d2.level && List.for_all2 (fun (n1, t1) (n2, t2) -> n1 = n2 && equal' env ctx t1 t2) d1.params d2.params
    | Constr (j, d1, args1), Constr (k, d2, args2) -> j = k && d1.name = d2.name && List.for_all2 (equal' env ctx) args1 args2
    | Ind (d1, p1, cases1, t1), Ind (d2, p2, cases2, t2) -> d1.name = d2.name && equal' env ctx p1 p2 && List.for_all2 (equal' env ctx) cases1 cases2 && equal' env ctx t1 t2
    | J (ty, a, b, c, d, p), J (ty', a', b', c', d', p') -> equal' env ctx ty ty' && equal' env ctx a a' && equal' env ctx b b' && equal' env ctx c c' && equal' env ctx d d' && equal' env ctx p p'
    | _ -> t1 = t2

and is_lam = function | Lam _ -> true | Pi _ -> true | _ -> false

and infer env ctx t =
    let res = match t with
    | Var x -> (match lookup_var ctx x with | Some ty -> ty | None -> raise (TypeError ("Unbound variable: " ^ x)))
    | Universe i -> if i < 0 then raise (TypeError "Negative universe level"); Universe (i + 1)
    | Pi (x, a, b) -> let i = check_universe env ctx a in let ctx' = add_var ctx x a in let j = check_universe env ctx' b in Universe (max i j)
    | Lam (x, domain, body) -> check env ctx domain (infer env ctx domain); let ctx' = add_var ctx x domain in let body_ty = infer env ctx' body in Pi (x, domain, body_ty)
    | App (f, arg) -> (match infer env ctx f with | Pi (x, a, b) -> check env ctx arg a; subst x arg b | ty -> Printf.printf "App failed: inferred "; print_term ty; print_endline ""; raise (TypeError "Application requires a Pi type"))
    | Sigma (x, a, b) -> let i = check_universe env ctx a in let ctx' = add_var ctx x a in let j = check_universe env ctx' b in Universe (max i j)
    | Pair (a, b) -> let a_ty = infer env ctx a in let b_ty = infer env ctx b in check env ctx b b_ty; Sigma ("x", a_ty, b_ty)
    | Fst p -> (match infer env ctx p with | Sigma (x, a, b) -> a | ty -> raise (TypeError ("Fst expects a Sigma type, got: " ^ (let s = ref "" in print_term_depth 0 ty; !s))))
    | Snd p -> (match infer env ctx p with | Sigma (x, a, b) -> subst x (Fst p) b | ty -> raise (TypeError ("Snd expects a Sigma type, got: " ^ (let s = ref "" in print_term_depth 0 ty; !s))))
    | Id (ty, a, b) -> check env ctx a ty; check env ctx b ty; Universe (check_universe env ctx ty)
    | Refl a -> let a_ty = infer env ctx a in Id (a_ty, a, a)
    | Inductive d -> 
      List.iter (fun (_, ty) -> match infer env ctx ty with | Universe _ -> () | _ -> raise (TypeError "Inductive parameters must be types")) d.params;
      let d_applied = Inductive { d with constrs = [] } in  (* Simplified self-reference *)
      List.iter (fun (j, ty) ->
        let rec check_return ty' =
            match ty' with
            | Pi (_, _, b) -> check_return b
            | Inductive d' when d'.name = d.name -> ()
            | _ -> raise (TypeError ("Constructor " ^ string_of_int j ^ " must return " ^ d.name))
        in check_return ty
      ) d.constrs;
      Universe d.level
    | Constr (j, d, args) -> let cj = List.assoc j d.constrs in let cj_subst = subst_many (List.combine (List.map fst d.params) (List.map snd d.params)) cj in infer_ctor env ctx cj_subst args
    | Ind (d, p, cases, t') -> infer_Ind env ctx d p cases t'
    | J (ty, a, b, c, d, p) -> infer_J env ctx ty a b c d p in normalize env ctx res

and infer_ctor env ctx ty args =
    let rec check_args ty args_acc = function
    | [] -> ty
    | arg :: rest ->
        (match ty with
         | Pi (x, a, b) -> check env ctx arg a; check_args (subst x arg b) (arg :: args_acc) rest
         | _ -> raise (TypeError "Too many arguments to constructor"))
    in check_args ty [] args

and infer_J env ctx ty' a b c d p =
    check env ctx ty' (Universe 0);
    check env ctx a ty';
    check env ctx b ty';
    let fresh_x = "x_" ^ string_of_int (List.length ctx) in
    let fresh_y = "y_" ^ string_of_int (List.length ctx) in
    let fresh_p = "p_" ^ string_of_int (List.length ctx) in
    let motive_ty = Pi (fresh_x, ty', Pi (fresh_y, ty', Pi (fresh_p, Id (ty', Var fresh_x, Var fresh_y), Universe 0))) in
    check env ctx c motive_ty;
    let refl_case_ty = Pi (fresh_x, ty', App (App (App (c, Var fresh_x), Var fresh_x), Refl (Var fresh_x))) in
    check env ctx d refl_case_ty;
    check env ctx p (Id (ty', a, b));
    let result_ty = App (App (App (c, a), b), p) in
    normalize env ctx result_ty

and infer_Ind env ctx d p cases t' =
    let t_ty = infer env ctx t' in
    let d_applied = apply_inductive d (List.map snd d.params) in
    if not (equal env ctx t_ty d_applied) then raise (TypeError "Elimination target type mismatch");
    let (x, a, b) = match p with
    | Pi (x, a, b) -> (x, a, b)
    | _ -> raise (TypeError ("Motive must be a Pi type, got: " ^ (let s = ref "" in print_term_depth 0 p; !s))) in
    let p_ty = infer env ctx p in (match p_ty with | Universe _ -> () | _ -> raise (TypeError "Motive must be a type (Universe)"));
    if not (equal env ctx t_ty a) then raise (TypeError "Target type does not match motive domain");
    let result_ty = subst x t' b in
    if (trace) then (print_Ind d p cases t' 0);
    if List.length cases <> List.length d.constrs then raise (TypeError "Number of cases doesn't match constructors");
    List.iteri (fun j case ->
      let j_idx = j + 1 in
      let cj = List.assoc j_idx d.constrs in
      let cj_subst = List.fold_left2 (fun acc (n, _) arg -> subst n arg acc) cj d.params (List.map snd d.params) in
      let rec compute_case_type ty ctx_acc =
        match ty with
        | Pi (x, a, b) ->
            let var = Var x in let ctx' = add_var ctx_acc x a in let b_ty = compute_case_type b ctx' in
            if equal env ctx a d_applied then Pi (x, a, Pi ("ih", App (p, var), b_ty)) else Pi (x, a, b_ty)
        | Inductive d' when d'.name = d.name -> b
        | _ -> raise (TypeError "Invalid constructor return type")
      in
      let expected_ty = compute_case_type cj_subst ctx in
      if (trace) then (Printf.printf "Checking case %d: " j; print_term case; Printf.printf " against: "; print_term expected_ty; print_endline "");
      check env ctx case expected_ty;
      if (trace) then Printf.printf "Case %d checked\n" j
    ) cases;
    result_ty

and apply_inductive d args =
    if List.length d.params <> List.length args then raise (TypeError "Parameter mismatch in inductive type");
    let subst_param t = List.fold_left2 (fun acc (n, _) arg -> subst n arg acc) t d.params args
    in Inductive { d with constrs = List.map (fun (j, ty) -> (j, subst_param ty)) d.constrs }

and check_universe env ctx t =
    match infer env ctx t with
    | Universe i -> if i < 0 then raise (TypeError "Negative universe level"); i
    | ty -> raise (TypeError (Printf.sprintf "Expected a universe, got: %s" (let s = ref "" in print_term ty; !s)))

and check env ctx t ty =
    if (trace) then (Printf.printf "Checking Term: "; print_term t; print_string "\nAgainst Type: "; print_term ty; print_endline "");
    match t, ty with
    | Universe i, Universe j -> if i < 0 then raise (TypeError "Negative universe level"); if i > j then raise (TypeError (Printf.sprintf "Universe level mismatch: %d > %d" i j));
    | Pi (x, a, b), Pi (y, a', b') -> if not (equal env ctx a a') then raise (TypeError "Pi domain mismatch"); let ctx' = add_var ctx x a in check env ctx' b (subst y (Var x) b')
    | Lam (x, domain, body), Pi (y, a, b) -> check env ctx domain (infer env ctx domain); let b_subst = subst y (Var x) b in check env (add_var ctx x domain) body b_subst
    | Constr (j, d, args), Inductive d' when d.name = d'.name -> let inferred = infer env ctx t in if not (equal env ctx inferred ty) then raise (TypeError "Constructor type mismatch")
    | Ind (d, p, cases, t'), ty -> let inferred = infer_Ind env ctx d p cases t' in if not (equal env ctx inferred ty) then raise (TypeError "Elimination type mismatch")
    | Pair (a, b), Sigma (x, a_ty, b_ty) -> check env ctx a a_ty; check env ctx b (subst x a b_ty)
    | Fst p, ty -> let p_ty = infer env ctx p in (match p_ty with | Sigma (x, a, _) -> if not (equal env ctx a ty) then raise (TypeError "Fst type mismatch") | _ -> raise (TypeError "Fst expects a Sigma type"))
    | Snd p, ty -> let p_ty = infer env ctx p in (match p_ty with | Sigma (x, a, b) -> if not (equal env ctx (subst x (Fst p) b) ty) then raise (TypeError "Snd type mismatch") | _ -> raise (TypeError "Snd expects a Sigma type"))
    | Refl a, Id (ty, a', b') -> let a_ty = infer env ctx a in if not (equal env ctx a_ty ty) then raise (TypeError "Refl argument type mismatch"); if not (equal env ctx a a') || not (equal env ctx a b') then raise (TypeError "Refl arguments mismatch")
    | _, _ ->
        let inferred = infer env ctx t in
        let ty' = normalize env ctx ty in
        match inferred, ty' with
        | Universe i, Universe j when i >= j -> () (* cumulativity *)
        | _ -> if not (equal env ctx inferred ty') then
          (let error = Printf.sprintf "Type Mismatch Error. Inferred: %s. Expected: %s."
           (let s = ref "" in print_term inferred; !s) (let s = ref "" in print_term ty'; !s)
           in raise (TypeError error))

and apply_case env ctx d p cases case ty args =
    let rec apply ty args_acc = function
      | Pi (x, _, b) :: arg :: rest -> apply (subst x arg b) (arg :: args_acc) rest
      | Pi (_, _, b) :: [] -> apply b args_acc []
      | _ -> List.fold_left (fun t a -> subst "_dummy" a t) case (List.rev args_acc)
    in apply ty [] args

and reduce env ctx t =
    if (trace) then (Printf.printf "Reducing: "; print_term t; print_endline "");
    match t with
    | App (Lam (x, domain, body), arg) -> subst x arg body
    | App (Pi (x, a, b), arg) -> subst x arg b
    | App (f, arg) -> let f' = reduce env ctx f in let arg' = reduce env ctx arg in App (f', arg')
    | Ind (d, p, cases, Constr (j, d', args)) when d.name = d'.name ->
      let case = List.nth cases (j - 1) in let cj = List.assoc j d.constrs in
      let cj_subst = subst_many (List.combine (List.map fst d.params) (List.map snd d.params)) cj in
      apply_case env ctx d p cases case cj_subst args
    | Ind (d, p, cases, t') -> let t'' = reduce env ctx t' in if t' = t'' then t else Ind (d, p, cases, t'')
    | Constr (j, d, args) -> let args' = List.map (reduce env ctx) args in if args = args' then t else Constr (j, d, args')
    | Fst (Pair (a, b)) -> a
    | Snd (Pair (a, b)) -> b
    | J (ty, a, b, c, d, Refl a') when equal' env ctx a a' && equal' env ctx b a' -> App (d, a)
    | J (ty, a, b, c, d, p) -> let p' = reduce env ctx p in if p = p' then t else J (ty, a, b, c, d, p')
    | Refl a -> let a' = reduce env ctx a in if a = a' then t else Refl a'
    | _ -> t

and normalize env ctx t =
    let t' = reduce env ctx t in
    if (trace) then (Printf.printf "One-step β-reductor: "; print_term t'; print_endline "");
    if equal' env ctx t t' then t else normalize env ctx t'

and print_J ty a b c d p depth =
    print_string "J ("; print_term_depth (depth + 1) ty; print_string ", "; print_term_depth (depth + 1) a; print_string ", "; print_term_depth (depth + 1) b;
    print_string ", "; print_term_depth (depth + 1) c; print_string ", "; print_term_depth (depth + 1) d; print_string ", "; print_term_depth (depth + 1) p; print_string ")"

and print_Ind d p cases t' depth =
    print_string (d.name ^ ".Ind "); print_term_depth (depth + 1) p;
    print_string " ["; List.iteri (fun i c -> if i > 0 then print_string "; "; print_term_depth (depth + 1) c) cases; print_string "] ";
    print_term_depth (depth + 1) t'

and print_term_depth depth t =
    if depth > 10 then print_string "<deep>"
    else match t with
    | Var x -> print_string x
    | Universe i -> print_string ("Type" ^ string_of_int i)
    | Pi (x, a, b) -> print_string ("Π(" ^ x ^ " : "); print_term_depth (depth + 1) a; print_string ")."; print_term_depth (depth + 1) b
    | Lam (x, _, body) -> print_string ("λ (" ^ x ^ "), "); print_term_depth (depth + 1) body
    | App (f, arg) -> print_string "("; print_term_depth (depth + 1) f; print_string " "; print_term_depth (depth + 1) arg; print_string ")"
    | Sigma (x, a, b) -> print_string ("Σ (" ^ x ^ " : "); print_term_depth (depth + 1) a; print_string "), "; print_term_depth (depth + 1) b
    | Pair (a, b) -> print_string "("; print_term_depth (depth + 1) a; print_string ", "; print_term_depth (depth + 1) b; print_string ")"
    | Fst t -> print_string "fst "; print_term_depth (depth + 1) t
    | Snd t -> print_string "snd "; print_term_depth (depth + 1) t
    | Id (ty, a, b) -> print_string "{"; print_term_depth (depth + 1) a; print_string " = "; print_term_depth (depth + 1) b; print_string " : "; print_term_depth (depth + 1) ty; print_string "}"
    | Refl t -> print_string "Id.refl "; print_term_depth (depth + 1) t
    | J (ty, a, b, c, d, p) -> print_J ty a b c d p depth
    | Inductive d -> print_string d.name
    | Constr (i, d, args) -> print_string d.name; print_string "."; print_string (string_of_int i); List.iteri (fun j c -> if j > 0 then print_string "; "; print_term_depth (depth + 1) c) args
    | Ind (d, p, cases, t') -> print_Ind d p cases t' depth

and print_term t = print_term_depth 0 t

(* TEST SUITE *)

let nat_def = {
  name = "Nat"; params = []; level = 0;
  constrs = [
    (1, Inductive { name = "Nat"; params = []; level = 0; constrs = [] });
    (2, Pi ("n", Inductive { name = "Nat"; params = []; level = 0; constrs = [] },
           Inductive { name = "Nat"; params = []; level = 0; constrs = [] }))]
}

let list_def (a : term) = {
  name = "List"; params = [("A", a)]; level = (match a with Universe i -> i | _ -> failwith "List param must be a type");
  constrs = [
    (1, Inductive { name = "List"; params = [("A", a)]; level = 0; constrs = [] }); (* nil *)
    (2, Pi ("x", a, Pi ("xs", Inductive { name = "List"; params = [("A", a)]; level = 0; constrs = [] },
                        Inductive { name = "List"; params = [("A", a)]; level = 0; constrs = [] }))) (* cons *) ]
}

let env = [("Nat", nat_def); ("List", list_def (Universe 0))]
let nat_ind = Inductive nat_def
let list_ind = Inductive (list_def (Universe 0))

let list_length =
  Lam ("l", list_ind,  (* l : List Type0 *)
    Ind ((list_def (Universe 0)),
          Pi ("_", list_ind, nat_ind),
          [Constr (1, nat_def, []);  (* nil -> zero *)
           Lam ("x", Universe 0,  (* x : Type0 *)
             Lam ("xs", list_ind,  (* xs : List Type0 *)
               Lam ("ih", nat_ind,  (* ih : Nat *)
                 Constr (2, nat_def, [Var "ih"]))))], (* succ ih *)
          Var "l"))

let sample_list =
  Constr (2, list_def (Universe 0),  (* cons *)
    [Constr (1, nat_def, []);        (* zero *)
     Constr (2, list_def (Universe 0),  (* cons *)
       [Constr (2, nat_def, [Constr (1, nat_def, [])]);  (* succ zero *)
        Constr (1, list_def (Universe 0), [])])])         (* nil *)

let plus =
  Lam ("m", nat_ind, Lam ("n", nat_ind,
    Ind (nat_def,
          Pi ("_", nat_ind, nat_ind),
          [Var "m"; Lam ("k", nat_ind, Lam ("ih", nat_ind, Constr (2, nat_def, [Var "ih"])))],
          Var "n")))

let plus_ty = Pi ("m", nat_ind, Pi ("n", nat_ind, nat_ind))

let nat_elim =
    Ind (nat_def,
          Pi ("x", nat_ind, Universe 0),
          [Inductive nat_def; Lam ("n", nat_ind, Lam ("ih", Universe 0, Var "ih"))],
          Constr (1, nat_def, []))

let succ = Lam ("n", nat_ind, Constr (2, nat_def, [Var "n"]))

let subst_eq =
  Lam ("a", nat_ind, Lam ("b", nat_ind, Lam ("p", Id (nat_ind, Var "a", Var "b"),
    Lam ("P", Pi ("z", nat_ind, Universe 0), Lam ("x", App (Var "P", Var "b"),
      J (nat_ind, Var "a", Var "b",
         Pi ("x", nat_ind, Pi ("y", nat_ind, Pi ("p", Id (nat_ind, Var "x", Var "y"), App (Var "P", Var "y")))),
         Lam ("x", nat_ind, Var "x"),  (* x : P a *)
         Var "p"))))))

let id_symmetry =  (* Symmetry: a = b → b = a *)
  Lam ("a", nat_ind, Lam ("b", nat_ind, Lam ("p", Id (nat_ind, Var "a", Var "b"),
    J (nat_ind, Var "a", Var "b",
       Pi ("x", nat_ind, Pi ("y", nat_ind, Pi ("p", Id (nat_ind, Var "x", Var "y"), Id (nat_ind, Var "y", Var "x")))),
       Lam ("x", nat_ind, Refl (Var "x")),
       Var "p"))))

let id_transitivity = (* Transitivity: a = b ∧ b = c → a = c *)
    Lam ("a", nat_ind, Lam ("b", nat_ind, Lam ("c", nat_ind,
    Lam ("p", Id (nat_ind, Var "a", Var "b"),
    Lam ("q", Id (nat_ind, Var "b", Var "c"),
    J (nat_ind, Var "a", Var "b",
      Pi ("x", nat_ind, Pi ("y", nat_ind, Pi ("_", Id (nat_ind, Var "x", Var "y"), Id (nat_ind, Var "b", Var "c")))),
      Lam ("_", nat_ind, Var "q"),
      Var "p"))))))

let test_equality_theorems () =
    let ctx = empty_ctx in
    let env = empty_env in
    let a = Universe 0 in
    (* Symmetry *)
    let sym_motive = Pi ("x", a, Pi ("y", a, Pi ("p", Id (a, Var "x", Var "y"), Id (a, Var "y", Var "x")))) in
    let sym_d = Lam ("x", a, Refl (Var "x")) in
    let sym = Lam ("x", a, Lam ("y", a, Lam ("p", Id (a, Var "x", Var "y"), J (a, Var "x", Var "y", sym_motive, sym_d, Var "p")))) in
    let sym_ty = Pi ("x", a, Pi ("y", a, Pi ("p", Id (a, Var "x", Var "y"), Id (a, Var "y", Var "x")))) in
    print_string "Sym Left: "; print_term (infer env ctx sym); print_endline "";
    print_string "Sym Right: "; print_term sym_ty; print_endline "";
    assert (equal env ctx (infer env ctx sym) sym_ty);
    (* Transitivity *)
    let trans_motive = Pi ("y", a, Pi ("z", a, Pi ("q", Id (a, Var "y", Var "z"), Id (a, Var "x", Var "z")))) in
    let trans_d = Lam ("y", a, Var "p") in
      let trans = Lam ("x", a, Lam ("y", a, Lam ("p", Id (a, Var "x", Var "y"), Lam ("z", a, Lam ("q", Id (a, Var "y", Var "z"), J (a, Var "y", Var "z", trans_motive, trans_d, Var "q")))))) in
    let trans_ty = Pi ("x", a, Pi ("y", a, Pi ("p", Id (a, Var "x", Var "y"), Pi ("z", a, Pi ("q", Id (a, Var "y", Var "z"), Id (a, Var "x", Var "z")))))) in
    print_string "Trans Left: "; print_term (infer env ctx trans); print_endline "";
    print_string "Trans Right: "; print_term trans_ty; print_endline "";
    assert (equal env ctx (infer env ctx trans) trans_ty);
    print_string "Identity System Equalities PASSED.\n"

let test_equal () =
    let ctx = empty_ctx in
    let env = empty_env in
    let ty1 = Pi ("x", Universe 0, Id (Universe 0, Var "x", Var "x")) in
    let ty2 = Pi ("y", Universe 0, Id (Universe 0, Var "y", Var "y")) in
    assert (equal env ctx ty1 ty2);
    print_string "Syntactic Equality PASSED.\n"

let test_eta () =
    let ctx = [("f", Pi ("x", Universe 0, Universe 0))] in
    let t1 = Lam ("x", Universe 0, App (Var "f", Var "x")) in
    let t2 = Var "f" in
    assert (equal empty_env ctx t1 t2);
    if trace then (Printf.printf "Eta test: "; print_term t1; print_string " = "; print_term t2; print_endline " (passed)");
    Printf.printf "Eta-expansion PASSED.\n"

let test_universe () =
    let ctx = [] in
    (* Test valid universe *)
    let t1 = Universe 0 in
    assert (equal empty_env ctx (infer empty_env ctx t1) (Universe 1));
    check empty_env ctx (Universe 0) (Universe 1);
    check empty_env ctx (Universe 0) (Universe 0);
    begin try let _ = check env ctx (Universe 1) (Universe 0) in assert false with TypeError _ -> () end;
    begin try let _ = infer empty_env ctx (Universe (-1)) in assert false with TypeError "Negative universe level" -> () end;
    if trace then (Printf.printf "Universe test: Type0 : Type1 (passed)\n");
    Printf.printf "Universe Consistency PASSED\n"

let test_non_lam_eta () =
    let ctx = [("x", nat_ind); ("f", Pi ("x", nat_ind, nat_ind)); ("g", Pi ("x", nat_ind, nat_ind));
               ("eq", Id (nat_ind, App (Var "f", Var "x"), App (Var "g", Var "x")))] in
    let env = [("Nat", nat_def)] in
    let motive = Pi ("a", nat_ind, Pi ("b", nat_ind, Pi ("_", Id (nat_ind, Var "a", Var "b"), 
                   Id (Pi ("x", nat_ind, nat_ind), Var "f", Var "g")))) in
    let refl_case = Lam ("z", nat_ind, Refl (Var "f")) in
    let proof = J (nat_ind, App (Var "f", Var "x"), App (Var "g", Var "x"), motive, refl_case, Var "eq") in
    assert (equal env ctx (infer env ctx proof) (Id (Pi ("x", nat_ind, nat_ind), Var "f", Var "g")));
    print_string "Non-Lam Eta-Equality PASSED.\n"

let test () =
    test_universe ();
    test_equal (); 
    test_equality_theorems ();
    test_eta ();
(*  test_non_lam_eta (); *)
    let ctx : context = [] in
    let zero = Constr (1, nat_def, []) in
    let one = Constr (2, nat_def, [zero]) in
    let two = Constr (2, nat_def, [one]) in
    let add_term = App (App (plus, two), two) in
    let pair_term = Pair (zero, one) in
    let pair_ty = Sigma ("x", nat_ind, nat_ind) in
    let fst_term = Fst pair_term in
    let snd_term = Snd pair_term in
    let id_term = Refl zero in
    let id_ty = Id (nat_ind, zero, zero) in
    let sym_term = normalize env ctx (App (App (App (id_symmetry, zero), zero), Refl zero)) in
    let _ = Printf.printf "sym_term PASSED\n" in
    let trans_term = App (App (App (App (App (id_transitivity, zero), zero), zero), Refl zero), Refl zero) in
    try let succ_ty = infer env ctx succ in
        let plus_ty = infer env ctx plus in
        let nat_elim_ty = infer env ctx nat_elim in
        let _ = check env ctx pair_term pair_ty in
        let fst_ty = infer env ctx fst_term in
        let snd_ty = infer env ctx snd_term in
        let sym_ty = infer env ctx sym_term in
        let _ = check env ctx id_term id_ty in
        let trans_ty = infer env ctx trans_term in
        let trans_norm = normalize env ctx trans_term in
        let subst_norm = normalize env ctx subst_eq in
        let add_normal = normalize env ctx add_term in
        let len_normal = normalize env ctx (App (list_length, sample_list)) in
        Printf.printf "eval Nat.add(2,2) = "; print_term add_normal; print_endline "";
        Printf.printf "eval List.length(list) = "; print_term len_normal; print_endline "";
        Printf.printf "Nat.Ind = "; print_term nat_elim; print_endline "";
        Printf.printf "Nat.succ : "; print_term succ_ty; print_endline "";
        Printf.printf "Nat.plus : "; print_term plus_ty; print_endline "";
        Printf.printf "Nat.Ind : "; print_term nat_elim_ty; print_endline "";
        Printf.printf "Sigma.pair = "; print_term pair_term; print_endline "";
        Printf.printf "Sigma.fst(Sigma.pair) : "; print_term fst_ty; print_endline "";
        Printf.printf "Sigma.snd(Sigma.pair) : "; print_term snd_ty; print_endline "";
        Printf.printf "id_symmetry : "; print_term sym_ty; print_endline "";
        Printf.printf "eval id_symmetry = "; print_term sym_term; print_endline ""; 
        Printf.printf "id_term : id_ty\n";
        Printf.printf "eval tran_term = "; print_term trans_norm; print_endline "";
        Printf.printf "eval subst_eq = "; print_term subst_norm; print_endline "";
        Printf.printf "id_transitivity : "; print_term trans_ty; print_endline "";
    with TypeError msg -> print_endline ("Type error: " ^ msg)

(* THEOREM PROVER TACTICS LANGUAGE *)

type goal = {
  ctx : context;          (* Current context *)
  target : term;          (* Type to prove *)
  id : int;               (* Goal identifier *)
}

type proof_state = {
  goals : goal list;      (* List of open goals *)
  solved : (int * term) list; (* Solved goals with their terms *)
}

let initial_state target = {
  goals = [{ ctx = empty_ctx; target; id = 1 }];
  solved = [];
}

let next_id state = 1 + List.fold_left (fun m g -> max m g.id) 0 state.goals

type tactic =
  | Intro of name                     (* Introduce a variable *)
  | Elim of term                      (* Eliminate a term (e.g., induction or case analysis) *)
  | Apply of term                     (* Apply a term or hypothesis *)
  | Assumption                        (* Use a hypothesis from context *)
  | Auto                              (* Simple automation *)
  | Exact of term                     (* Provide an exact term *)

exception TacticError of string

let print_goal g =
  Printf.printf "Goal %d:\nContext: [" g.id;
  List.iter (fun (n, ty) -> Printf.printf "(%s : " n; print_term ty; print_string "); ") g.ctx;
  print_endline "]";
  Printf.printf "⊢ "; print_term g.target; print_endline "\n"

let print_state state =
  List.iter print_goal state.goals;
  Printf.printf "%d goals remaining\n" (List.length state.goals)

let rec apply_tactic env state tac =
  match state.goals with
  | [] -> raise (TacticError "No goals to solve")
  | goal :: rest ->
      match tac with
      | Intro x ->
          (match goal.target with
           | Pi (y, a, b) ->
               let new_ctx = add_var goal.ctx x a in
               let new_target = subst y (Var x) b in
               let new_goal = { goal with ctx = new_ctx; target = new_target } in
               { state with goals = new_goal :: rest }
           | _ -> raise (TacticError "Intro expects a Pi type"))
      | Elim t ->
          let ty = infer env goal.ctx t in
          (match ty with
           | Inductive d ->
               let p = Var "P" in (* Motive placeholder *)
               let motive_ty = Pi ("x", Inductive d, Universe 0) in
               let cases = List.map (fun (j, cj) ->
                 let rec count_pis ty n =
                   match ty with
                   | Pi (x, a, b) -> count_pis b (n + 1)
                   | _ -> n
                 in
                 let arity = count_pis cj 0 in
                 let rec gen_lam n =
                   if n = 0 then Var ("case_" ^ string_of_int j)
                   else Lam ("x" ^ string_of_int n, Universe 0, gen_lam (n - 1))
                 in gen_lam arity
               ) d.constrs in
               let new_term = Ind (d, p, cases, t) in
               let new_goal = { goal with target = App (p, t); id = next_id state } in
               let motive_goal = { ctx = goal.ctx; target = motive_ty; id = goal.id } in
               { state with goals = motive_goal :: new_goal :: rest }
           | Id (ty', a, b) ->
               let c = Var "C" in
               let motive_ty = Pi ("x", ty', Pi ("y", ty', Pi ("p", Id (ty', Var "x", Var "y"), Universe 0))) in
               let d = Var "d" in
               let new_term = J (ty', a, b, c, d, t) in
               let new_goal = { goal with target = App (App (App (c, a), b), t); id = next_id state } in
               let refl_goal = { ctx = goal.ctx; target = Pi ("x", ty', App (App (App (c, Var "x"), Var "x"), Refl (Var "x"))); id = next_id state + 1 } in
               let motive_goal = { ctx = goal.ctx; target = motive_ty; id = goal.id } in
               { state with goals = motive_goal :: refl_goal :: new_goal :: rest }
           | _ -> raise (TacticError "Elim expects an inductive or identity type"))
      | Apply t ->
          let ty = infer env goal.ctx t in
          (match ty with
           | Pi (x, a, b) ->
               if equal env goal.ctx a goal.target then
                 { state with goals = rest; solved = (goal.id, t) :: state.solved }
               else
                 let new_goal = { goal with target = a; id = next_id state } in
                 { state with goals = new_goal :: rest }
           | _ ->
               if equal env goal.ctx ty goal.target then
                 { state with goals = rest; solved = (goal.id, t) :: state.solved }
               else raise (TacticError "Apply type mismatch"))
      | Assumption ->
          (match List.find_opt (fun (_, ty) -> equal env goal.ctx ty goal.target) goal.ctx with
           | Some (n, _) ->
               { state with goals = rest; solved = (goal.id, Var n) :: state.solved }
           | None -> raise (TacticError "No matching assumption"))
      | Auto ->
          let rec try_assumptions ctx =
            match ctx with
            | (n, ty) :: rest ->
                if equal env goal.ctx ty goal.target then
                  Some (Var n)
                else try_assumptions rest
            | [] -> None
          in
          (match try_assumptions goal.ctx with
           | Some t -> { state with goals = rest; solved = (goal.id, t) :: state.solved }
           | None -> state) (* Could extend with more automation *)
      | Exact t ->
          check env goal.ctx t goal.target;
          { state with goals = rest; solved = (goal.id, t) :: state.solved }

let parse_tactic input =
  let tokens = String.split_on_char ' ' (String.trim input) in
  match tokens with
  | ["intro"; x] -> Intro x
  | ["elim"; t] -> Elim (Var t) (* Simplified: assumes variable name *)
  | ["apply"; t] -> Apply (Var t) (* Simplified: assumes variable name *)
  | ["assumption"] -> Assumption
  | ["auto"] -> Auto
  | ["exact"; t] -> Exact (Var t) (* Simplified: assumes variable name *)
  | _ -> raise (TacticError ("Unknown tactic: " ^ input))

let rec console_loop env state =
  print_state state;
  if state.goals = [] then (
    Printf.printf "Proof complete!\n";
    let final_term = List.fold_left (fun acc (_, t) -> subst "P" t acc) (Var "P") state.solved in
    Printf.printf "Final term: "; print_term final_term; print_endline "";
    final_term
  ) else (
    Printf.printf "> ";
    let input = read_line () in
    try
      let tactic = parse_tactic input in
      let new_state = apply_tactic env state tactic in
      console_loop env new_state
    with
    | TacticError msg -> Printf.printf "Error: %s\n" msg; console_loop env state
    | TypeError msg -> Printf.printf "Type error: %s\n" msg; console_loop env state
  )

let main () =
  let nat =
      Inductive { name = "Nat"; params = []; level = 0;
                  constrs = [(1, Universe 0);
                             (2, Pi ("n", Inductive { name = "Nat";
                                                      params = [];
                                                      level = 0;
                                                      constrs = []}, Universe 0))] } in
  let env = [("Nat", nat)] in
  let target = Pi ("n", Inductive nat_def, Inductive nat_def) in (* Example: ∀n : Nat, Nat *)
  Printf.printf "Starting proof for: "; print_term target; print_endline "";
  let state = initial_state target in
  ignore (console_loop env state)

let help =
"https://per.groupoid.space/

  🧊 MLTT/CIC Theorem Prover version 0.4 (c) 2025 Groupoїd Infinity"

let () = 
  test ();
  print_endline ("\n" ^ help ^ "\n\nFor help type `help`.\n");
  main ()

