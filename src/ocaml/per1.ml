(* Copyright (c) 2016—2025 Groupoid Infinity *)

let trace: bool = false

type level = int
type name = string

type term =
  | Var of name | Universe of level
  | Pi of name * term * term | Lam of name * term * term | App of term * term
  | Sigma of name * term * term | Pair of term * term | Fst of term | Snd of term
  | Id of term * term * term | Refl of term
  | Inductive of inductive | Constr of int * inductive * term list | Elim of inductive * term * term list * term

and inductive = {
  name : string;
  params : (name * term) list;
  level : level;
  constrs : (int * term) list;
  mutual_group : string list
}

type env = (string * inductive) list
type context = (name * term) list

exception TypeError of string

let empty_env : env = []
let empty_ctx : context = []
let add_var ctx x ty = (x, ty) :: ctx

type subst_map = (name * term) list

let rec subst_many m t =
  match t with
  | Var x -> (try List.assoc x m with Not_found -> t)
  | Pi (x, a, b) -> let m' = List.filter (fun (y, _) -> y <> x) m in Pi (x, subst_many m a, subst_many m' b)
  | Lam (x, d, b) -> let m' = List.filter (fun (y, _) -> y <> x) m in Lam (x, subst_many m d, subst_many m' b)
  | App (f, arg) -> App (subst_many m f, subst_many m arg)
  | Inductive d -> Inductive d
  | Constr (j, d, args) -> Constr (j, d, List.map (subst_many m) args)
  | Elim (d, p, cases, t') -> Elim (d, subst_many m p, List.map (subst_many m) cases, subst_many m t')
  | _ -> t

let subst x s t = subst_many [(x, s)] t

let rec equal env ctx t1 t2 =
  match t1, t2 with
  | App (f, arg), App (f', arg') -> equal env ctx f f' && equal env ctx arg arg'
  | Var x, Var y -> x = y
  | Universe i, Universe j -> i = j
  | Pi (x, a, b), Pi (y, a', b') -> equal env ctx a a' && equal env (add_var ctx x a) b (subst y (Var x) b')
  | Inductive d1, Inductive d2 -> d1.name = d2.name && d1.level = d2.level && List.for_all2 (fun (n1, t1) (n2, t2) -> n1 = n2 && equal env ctx t1 t2) d1.params d2.params
  | Constr (j, d1, args1), Constr (k, d2, args2) -> j = k && d1.name = d2.name && List.for_all2 (equal env ctx) args1 args2
  | Elim (d1, p1, cases1, t1), Elim (d2, p2, cases2, t2) -> d1.name = d2.name && equal env ctx p1 p2 && List.for_all2 (equal env ctx) cases1 cases2 && equal env ctx t1 t2
  | _ -> false

and lookup_var ctx x =
  if (trace) then (Printf.printf "Looking up %s in context: [" x;
                   List.iter (fun (n, ty) -> Printf.printf "(%s, " n; print_term ty; print_string "); ") ctx;
                   print_endline "]");
  try Some (List.assoc x ctx) with Not_found -> None

and apply_inductive d args =
  if List.length d.params <> List.length args then 
    raise (TypeError "Parameter mismatch in inductive type");
  let subst_param t = 
    List.fold_left2 (fun acc (n, _) arg -> subst n arg acc) t d.params args
  in 
  Inductive { d with constrs = List.map (fun (j, ty) -> (j, subst_param ty)) d.constrs }

and infer env ctx t =
  if (trace) then (Printf.printf "Inferring: "; print_term t; Printf.printf " with ctx: ";
                   List.iter (fun (n, ty) -> Printf.printf "(%s, " n; print_term ty; print_string "); ") ctx;
                   print_endline "");
  match t with
  | Var x ->
      (match lookup_var ctx x with
       | Some ty -> ty
       | None -> raise (TypeError ("Unbound variable: " ^ x)))
  | Universe i -> Universe (i + 1)
  | Pi (x, a, b) ->
      let i = check_universe env ctx a in
      let ctx' = add_var ctx x a in
      let j = check_universe env ctx' b in
      Universe (max i j)
  | Lam (x, domain, body) ->
      check env ctx domain (infer env ctx domain);
      let ctx' = add_var ctx x domain in
      let body_ty = infer env ctx' body in
      Pi (x, domain, body_ty)
  | App (f, arg) ->
      let f_ty = infer env ctx f in
      (match f_ty with
       | Pi (x, a, b) ->
           check env ctx arg a;
           subst x arg b
       | _ -> raise (TypeError "Application requires a Pi type"))
  | Inductive d ->
      let param_tys = List.map (fun (_, ty) -> infer env ctx ty) d.params in
      List.iter (fun ty -> 
        match ty with 
        | Universe _ -> () 
        | _ -> raise (TypeError "Inductive parameters must be types")
      ) param_tys;
      Universe d.level
  | Constr (j, d, args) ->
      (try
         let cj = List.assoc j d.constrs in
         let cj_subst = List.fold_left2 
           (fun acc (n, _) arg -> subst n arg acc) 
           cj d.params (List.map snd d.params) in
         check_constructor_args env ctx cj_subst args
       with Not_found -> raise (TypeError ("Invalid constructor index: " ^ string_of_int j)))
  | Elim (d, p, cases, t') ->
      check_elim env ctx d p cases t'
  | _ -> Universe 0

and check_universe env ctx t =
  match infer env ctx t with
  | Universe i -> i
  | _ -> raise (TypeError "Expected a universe")

and check_constructor_args env ctx ty args =
  let rec check_args ty args_acc = function
    | [] -> ty
    | arg :: rest ->
        (match ty with
         | Pi (x, a, b) ->
             check env ctx arg a;
             check_args (subst x arg b) (arg :: args_acc) rest
         | _ -> raise (TypeError "Too many arguments to constructor"))
  in
  check_args ty [] args

and check_elim env ctx d p cases t' =
  if (trace) then (Printf.printf "Checking elim for %s with ctx: " d.name;
                   List.iter (fun (n, ty) -> Printf.printf "(%s, " n; print_term ty; print_string "); ") ctx;
                   print_endline "");
  let t_ty = infer env ctx t' in
  let d_applied = apply_inductive d (List.map snd d.params) in
  if (trace) then (Printf.printf "Target type: "; print_term t_ty; print_endline "");
  if not (equal env ctx t_ty d_applied) then raise (TypeError "Elimination target type mismatch");
  (* Check that p is a Pi type structurally *)
  let (x, a, b) = match p with
    | Pi (x, a, b) -> (x, a, b)
    | _ -> raise (TypeError ("Motive must be a Pi type, got: " ^ (let s = ref "" in print_term_depth 0 p; !s)))
  in
  if (trace) then (Printf.printf "Motive domain: "; print_term a; print_endline "");
  if (trace) then (Printf.printf "Motive codomain: "; print_term b; print_endline "");
  (* Verify the motive's type *)
  let p_ty = infer env ctx p in
  if (trace) then (Printf.printf "Motive type inferred: "; print_term p_ty; print_endline "");
  (match p_ty with
   | Universe _ -> ()  (* Motive should be a type *)
   | _ -> raise (TypeError "Motive must be a type (Universe)"));
  (* Check that the target's type matches the motive's domain *)
  if not (equal env ctx t_ty a) then raise (TypeError "Target type does not match motive domain");
  let result_ty = subst x t' b in
  if (trace) then (Printf.printf "Result type: "; print_term result_ty; print_endline "");
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
      | Inductive d' when d'.name = d.name -> b (* Return type is the motive's codomain *)
      | _ -> raise (TypeError "Invalid constructor return type")
    in
    let expected_ty = compute_case_type cj_subst ctx in
    if (trace) then (Printf.printf "Checking case %d: " j; print_term case; Printf.printf " against: "; print_term expected_ty; print_endline "");
    check env ctx case expected_ty;
    if (trace) then Printf.printf "Case %d checked\n" j
  ) cases;
  result_ty  (* Return the type of the elimination *)
and check env ctx t ty =
  if (trace) then (Printf.printf "Checking: "; print_term t; print_string " against "; print_term ty; print_endline "");
  match t, ty with
  | Lam (x, domain, body), Pi (y, a, b) ->
      check env ctx domain (infer env ctx domain);
      check env (add_var ctx x domain) body b
  | Constr (j, d, args), Inductive d' when d.name = d'.name ->
      let inferred = infer env ctx t in
      if not (equal env ctx inferred ty) then
        raise (TypeError "Constructor type mismatch")
  | Elim (d, p, cases, t'), ty ->
      let inferred = check_elim env ctx d p cases t' in
      if not (equal env ctx inferred ty) then
        raise (TypeError "Elimination type mismatch")
  | _, _ ->
      let inferred = infer env ctx t in
      let ty' = normalize env ctx ty in
      (if (trace) then (Printf.printf "Inferred: "; print_term inferred; print_string ", Expected: "; print_term ty'; print_endline ""));
      match inferred, ty' with
      | Universe i, Universe j when i >= j -> () (* cumulativity *)
      | _ ->
          if not (equal env ctx inferred ty') then
            raise (TypeError "Type mismatch")

and reduce env ctx t =
  if (trace) then (Printf.printf "Reducing: "; print_term t; print_endline "");
  match t with
  | App (Lam (x, domain, body), arg) ->
      if (trace) then (Printf.printf "Beta reducing: %s with " x; print_term arg; print_endline "");
      subst x arg body
  | App (Pi (x, a, b), arg) ->
      if (trace) then (Printf.printf "Reducing Pi application: "; print_term (Pi (x, a, b)); print_string " with "; print_term arg; print_endline "");
      subst x arg b
  | App (f, arg) ->
      if (trace) then (Printf.printf "Reducing function part: "; print_term f; print_endline "");
      let f' = reduce env ctx f in
      if equal env ctx f f' then
        let arg' = reduce env ctx arg in
        App (f, arg')
      else
        App (f', arg)
  | Elim (d, p, cases, Constr (j, d', args)) when d.name = d'.name ->
      let case = List.nth cases (j - 1) in
      let cj = List.assoc j d.constrs in
      let cj_subst = List.fold_left2
        (fun acc (n, _) arg -> subst n arg acc)
        cj d.params (List.map snd d.params) in
      apply_case env ctx d p cases case cj_subst args
  | Elim (d, p, cases, t') ->
      let t'' = reduce env ctx t' in
      if equal env ctx t' t'' then t
      else Elim (d, p, cases, t'')
  | Constr (j, d, args) ->
      Constr (j, d, List.map (reduce env ctx) args)
  | _ -> t

and apply_case env ctx d p cases case ty args =
  if (trace) then (Printf.printf "Applying case: "; print_term case; Printf.printf " to type: "; print_term ty; Printf.printf " with args: [";
                   List.iter (fun arg -> print_term arg; print_string "; ") args;
                   print_endline "]");
  let rec apply ty args_acc remaining_args =
    match ty, remaining_args with
    | Pi (x, a, b), arg :: rest ->
        let b' = subst x arg b in
        let rec_arg = 
          if equal env ctx a (Inductive d) then
            match arg with
            | Constr (j, d', sub_args) when d.name = d'.name ->
                let reduced = reduce env ctx (Elim (d, p, cases, arg)) in
                if (trace) then (Printf.printf "Recursive arg for %s: " x; print_term reduced; print_endline "");
                Some reduced
            | _ -> None
          else None
        in
        let new_args_acc = 
          match rec_arg with
          | Some r -> r :: arg :: args_acc
          | None -> arg :: args_acc
        in
        apply b' new_args_acc rest
    | _, [] -> 
        let rec apply_term t args =
          match t, args with
          | Lam (x, _, body), arg :: rest -> 
              apply_term (subst x arg body) rest
          | _, [] -> t
          | _ -> raise (TypeError "Case application mismatch")
        in apply_term case (List.rev args_acc)
    | _ -> raise (TypeError "Constructor argument mismatch")
  in
  apply ty [] args

and normalize env ctx t =
  let t' = reduce env ctx t in
  if (trace) then (Printf.printf "Reduced to: "; print_term t'; print_endline "");
  if equal env ctx t t' then t
  else normalize env ctx t'


and print_term_depth depth t =
  if depth > 10 then print_string "<deep>"
  else match t with
    | Var x -> print_string x
    | Universe i -> print_string ("Type" ^ string_of_int i)
    | Pi (x, a, b) ->
        print_string ("Π(" ^ x ^ " : ");
        print_term_depth (depth + 1) a;
        print_string ").";
        print_term_depth (depth + 1) b
    | Lam (x, _, body) ->
        print_string ("λ" ^ x ^ ".");
        print_term_depth (depth + 1) body
    | App (f, arg) ->
        print_string "(";
        print_term_depth (depth + 1) f;
        print_string " ";
        print_term_depth (depth + 1) arg;
        print_string ")"
    | Constr (i, d, args) ->
        print_string d.name;
        print_string ".";
        print_string (string_of_int i);
        List.iteri (fun j c ->
          if j > 0 then print_string "; ";
          print_term_depth (depth + 1) c
        ) args;
    | Elim (d, p, cases, t') ->
        print_string (d.name ^ ".elim ");
        print_term_depth (depth + 1) p;
        print_string " [";
        List.iteri (fun i c ->
          if i > 0 then print_string "; ";
          print_term_depth (depth + 1) c
        ) cases;
        print_string "] ";
        print_term_depth (depth + 1) t'
    | Inductive d -> print_string d.name
    | _ -> print_string "<term>"

and print_term t = print_term_depth 0 t

(* Example definitions *)
let nat_def = {
  name = "Nat";
  params = [];
  level = 0;
  constrs = [
    (1, Inductive { name = "Nat"; params = []; level = 0; constrs = []; mutual_group = ["Nat"] });
    (2, Pi ("n", Inductive { name = "Nat"; params = []; level = 0; constrs = []; mutual_group = ["Nat"] },
           Inductive { name = "Nat"; params = []; level = 0; constrs = []; mutual_group = ["Nat"] }))
  ];
  mutual_group = ["Nat"]
}

let list_def (a : term) = {
  name = "List";
  params = [("A", a)];
  level = (match a with Universe i -> i | _ -> failwith "List param must be a type");
  constrs = [
    (1, Inductive { name = "List"; params = [("A", a)]; level = 0; constrs = []; mutual_group = ["List"] }); (* nil *)
    (2, Pi ("x", a, Pi ("xs", Inductive { name = "List"; params = [("A", a)]; level = 0; constrs = []; mutual_group = ["List"] },
                        Inductive { name = "List"; params = [("A", a)]; level = 0; constrs = []; mutual_group = ["List"] }))) (* cons *)
  ];
  mutual_group = ["List"]
}

let env = [("Nat", nat_def); ("List", list_def (Universe 0))]
let nat_ind = Inductive nat_def
let list_ind = Inductive (list_def (Universe 0))

let list_length =
  Lam ("l", list_ind,  (* l : List Type0 *)
    Elim ((list_def (Universe 0)),
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
    Elim (nat_def,
          Pi ("_", nat_ind, nat_ind),
          [Var "m"; Lam ("k", nat_ind, Lam ("ih", nat_ind, Constr (2, nat_def, [Var "ih"])))],
          Var "n")))

let plus_ty = Pi ("m", nat_ind, Pi ("n", nat_ind, nat_ind))

let nat_elim = 
    Elim (nat_def,
          Pi ("x", nat_ind, Universe 0),
          [Inductive nat_def; Lam ("n", nat_ind, Lam ("ih", Universe 0, Var "ih"))],
          Constr (1, nat_def, []))

let succ = Lam ("n", nat_ind, Constr (2, nat_def, [Var "n"]))

let empty_ctx : context = []

let test () =
  let ctx = empty_ctx in
  let zero = Constr (1, nat_def, []) in
  let one = Constr (2, nat_def, [zero]) in
  let two = Constr (2, nat_def, [one]) in
  let add_term = App (App (plus, two), two) in
  let add_normal = normalize env empty_ctx add_term in
  Printf.printf "Nat.add: "; print_term add_normal; print_endline "";
  Printf.printf "List.length: "; print_term (normalize env empty_ctx (App (list_length, sample_list))); print_endline "";
  Printf.printf "Nat.Elim: "; print_term nat_elim; print_endline "";

  try
    let succ_ty = infer env ctx succ in
    Printf.printf "typeof(Nat.succ): "; print_term succ_ty; print_endline "";
    let plus_ty = infer env ctx plus in
    Printf.printf "typeof(Nat.plus): "; print_term plus_ty; print_endline "";
    let nat_elim_ty = infer env ctx nat_elim in
    Printf.printf "typeof(Nat.elim): "; print_term nat_elim_ty; print_endline ""
  with TypeError msg -> print_endline ("Type error: " ^ msg)

let _ = test ()
