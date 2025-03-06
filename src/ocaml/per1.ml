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

let fresh_name x used =
  let rec aux n =
    let candidate = x ^ string_of_int n in
    if List.mem candidate used then aux (n + 1) else candidate
  in if List.mem x used then aux 0 else x

let rec subst_many m t =
  match t with
  | Var x -> (try List.assoc x m with Not_found -> t)
  | Pi (x, a, b) ->
      let used = List.map fst m in
      let x' = fresh_name x used in
      let m' = List.filter (fun (y, _) -> y <> x) m in
      let a' = subst_many m a in
      let b' = subst_many ((x, Var x') :: m') b in
      Pi (x', a', b')
  | Lam (x, d, b) ->
      let used = List.map fst m in
      let x' = fresh_name x used in
      let m' = List.filter (fun (y, _) -> y <> x) m in
      let d' = subst_many m d in
      let b' = subst_many ((x, Var x') :: m') b in
      Lam (x', d', b')
  | App (f, arg) -> App (subst_many m f, subst_many m arg)
  | Sigma (x, a, b) ->
      let used = List.map fst m in
      let x' = fresh_name x used in
      let m' = List.filter (fun (y, _) -> y <> x) m in
      let a' = subst_many m a in
      let b' = subst_many ((x, Var x') :: m') b in
      Sigma (x', a', b')
  | Pair (a, b) -> Pair (subst_many m a, subst_many m b)
  | Fst t -> Fst (subst_many m t)
  | Snd t -> Snd (subst_many m t)
  | Id (ty, a, b) -> Id (subst_many m ty, subst_many m a, subst_many m b)
  | Refl t -> Refl (subst_many m t)
  | Inductive d -> Inductive d
  | Constr (j, d, args) -> Constr (j, d, List.map (subst_many m) args)
  | Elim (d, p, cases, t') -> Elim (d, subst_many m p, List.map (subst_many m) cases, subst_many m t')

let subst x s t = subst_many [(x, s)] t

(* Tail-recursive equality with normalization *)
let equal env ctx t1 t2 =
  let rec eq t1 t2 acc =
    let t1' = normalize env ctx t1 in
    let t2' = normalize env ctx t2 in
    match t1', t2' with
    | Var x, Var y -> acc && (x = y)
    | Universe i, Universe j -> acc && (i = j)
    | Pi (x, a, b), Pi (y, a', b') ->
        eq a a' (acc && eq b (subst y (Var x) b') true)
    | Lam (x, d, b), Lam (y, d', b') ->
        eq d d' (acc && eq b (subst y (Var x) b') true)
    | App (f, arg), App (f', arg') ->
        eq f f' (acc && eq arg arg' true)
    | Sigma (x, a, b), Sigma (y, a', b') ->
        eq a a' (acc && eq b (subst y (Var x) b') true)
    | Pair (a, b), Pair (a', b') ->
        eq a a' (acc && eq b b' true)
    | Fst t, Fst t' -> eq t t' acc
    | Snd t, Snd t' -> eq t t' acc
    | Id (ty, a, b), Id (ty', a', b') ->
        eq ty ty' (acc && eq a a' true && eq b b' true)
    | Refl t, Refl t' -> eq t t' acc
    | Inductive d1, Inductive d2 ->
        acc && d1.name = d2.name && d1.level = d2.level &&
        List.fold_left2 (fun acc (n1, t1) (n2, t2) -> acc && n1 = n2 && eq t1 t2 true) true d1.params d2.params
    | Constr (j, d1, args1), Constr (k, d2, args2) ->
        acc && j = k && d1.name = d2.name && List.fold_left2 (eq) true args1 args2
    | Elim (d1, p1, cases1, t1), Elim (d2, p2, cases2, t2) ->
        acc && d1.name = d2.name && eq p1 p2 true && List.fold_left2 (eq) true cases1 cases2 && eq t1 t2 true
    | _ -> false
  in eq t1 t2 true

and lookup_var ctx x =
  if trace then
    (Printf.printf "Looking up %s in context: [" x;
     List.iter (fun (n, ty) -> Printf.printf "(%s, " n; print_term ty; print_string "); ") ctx;
     print_endline "]");
  try Some (List.assoc x ctx) with Not_found -> None

and apply_inductive d args =
  if List.length d.params <> List.length args then raise (TypeError "Parameter mismatch in inductive type");
  let subst_param t = List.fold_left2 (fun acc (n, _) arg -> subst n arg acc) t d.params args in
  Inductive { d with constrs = List.map (fun (j, ty) -> (j, subst_param ty)) d.constrs }

and infer env ctx t =
  match t with
  | Var x -> (match lookup_var ctx x with | Some ty -> ty | None -> raise (TypeError ("Unbound variable: " ^ x)))
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
      let f_ty = normalize env ctx (infer env ctx f) in
      (match f_ty with
       | Pi (x, a, b) -> check env ctx arg a; subst x arg b
       | _ -> raise (TypeError ("Application requires a Pi type, got: " ^ string_of_term f_ty)))
  | Sigma (x, a, b) ->
      let i = check_universe env ctx a in
      let ctx' = add_var ctx x a in
      let j = check_universe env ctx' b in
      Universe (max i j)
  | Pair (a, b) ->
      let a_ty = infer env ctx a in
      let ctx' = add_var ctx "x" a_ty in
      let b_ty = infer env ctx b in
      let b_ty' = Pi ("x", a_ty, b_ty) in
      check env ctx b b_ty';
      Sigma ("x", a_ty, b_ty)
  | Fst p ->
      (match normalize env ctx (infer env ctx p) with
       | Sigma (x, a, b) -> a
       | ty -> raise (TypeError ("Fst requires a Sigma type, got: " ^ string_of_term ty)))
  | Snd p ->
      (match normalize env ctx (infer env ctx p) with
       | Sigma (x, a, b) -> subst x (Fst p) b
       | ty -> raise (TypeError ("Snd requires a Sigma type, got: " ^ string_of_term ty)))
  | Id (ty, a, b) ->
      check env ctx a ty;
      check env ctx b ty;
      Universe (check_universe env ctx ty)
  | Refl a ->
      let a_ty = infer env ctx a in
      Id (a_ty, a, a)
  | Inductive d ->
      List.iter (fun (_, ty) -> match infer env ctx ty with | Universe _ -> () | _ -> raise (TypeError "Inductive parameters must be types")) d.params;
      Universe d.level
  | Constr (j, d, args) ->
      let cj = List.assoc j d.constrs in
      let cj_subst = subst_many (List.combine (List.map fst d.params) (List.map snd d.params)) cj in
      check_constructor_args env ctx cj_subst args
  | Elim (d, p, cases, t') -> check_elim env ctx d p cases t'

and check_universe env ctx t =
  match infer env ctx t with
  | Universe i -> i
  | _ -> raise (TypeError ("Expected a universe, got: " ^ string_of_term t))

and check_constructor_args env ctx ty args =
  let rec check_args ty args_acc = function
    | [] -> ty
    | arg :: rest ->
        (match normalize env ctx ty with
         | Pi (x, a, b) -> check env ctx arg a; check_args (subst x arg b) (arg :: args_acc) rest
         | _ -> raise (TypeError "Too many arguments to constructor"))
  in check_args ty [] args

and check_elim env ctx d p cases t' =
  let t_ty = infer env ctx t' in
  let d_applied = apply_inductive d (List.map snd d.params) in
  if not (equal env ctx t_ty d_applied) then
    raise (TypeError ("Elimination target type mismatch, expected: " ^ string_of_term d_applied ^ ", got: " ^ string_of_term t_ty));
  let (x, a, b) = match p with
    | Pi (x, a, b) -> (x, a, b)
    | _ -> raise (TypeError ("Motive must be a Pi type, got: " ^ string_of_term p)) in
  let p_ty = infer env ctx p in
  (match p_ty with | Universe _ -> () | _ -> raise (TypeError "Motive must be a type (Universe)"));
  if not (equal env ctx t_ty a) then
    raise (TypeError ("Target type does not match motive domain, expected: " ^ string_of_term a ^ ", got: " ^ string_of_term t_ty));
  let result_ty = subst x t' b in
  if List.length cases <> List.length d.constrs then
    raise (TypeError "Number of cases doesn't match constructors");
  List.iteri (fun j case ->
    let j_idx = j + 1 in
    let cj = List.assoc j_idx d.constrs in
    let cj_subst = List.fold_left2 (fun acc (n, _) arg -> subst n arg acc) cj d.params (List.map snd d.params) in
    let rec compute_case_type ty ctx_acc =
      match normalize env ctx_acc ty with
      | Pi (x, a, b) ->
          let var = Var x in
          let ctx' = add_var ctx_acc x a in
          let b_ty = compute_case_type b ctx' in
          if equal env ctx a d_applied then Pi (x, a, Pi ("ih", App (p, var), b_ty)) else Pi (x, a, b_ty)
      | Inductive d' when d'.name = d.name -> b
      | _ -> raise (TypeError "Invalid constructor return type")
    in
    let expected_ty = compute_case_type cj_subst ctx in
    check env ctx case expected_ty
  ) cases;
  result_ty

and check env ctx t ty =
  if trace then
    (Printf.printf "Checking: "; print_term t; print_string " against "; print_term ty; print_endline "");
  let ty' = normalize env ctx ty in
  match t, ty' with
  | Lam (x, domain, body), Pi (y, a, b) ->
      check env ctx domain (infer env ctx domain);
      check env (add_var ctx x domain) body b
  | Constr (j, d, args), Inductive d' when d.name = d'.name ->
      let inferred = infer env ctx t in
      if not (equal env ctx inferred ty') then
        raise (TypeError ("Constructor type mismatch, expected: " ^ string_of_term ty' ^ ", got: " ^ string_of_term inferred))
  | Elim (d, p, cases, t'), _ ->
      let inferred = check_elim env ctx d p cases t' in
      if not (equal env ctx inferred ty') then
        raise (TypeError ("Elimination type mismatch, expected: " ^ string_of_term ty' ^ ", got: " ^ string_of_term inferred))
  | Pair (a, b), Sigma (x, a_ty, b_ty) ->
      check env ctx a a_ty;
      check env ctx b (subst x a b_ty)
  | Refl a, Id (ty, a', b') ->
      check env ctx a ty;
      if not (equal env ctx a a') || not (equal env ctx a b') then
        raise (TypeError ("Refl arguments mismatch, expected: " ^ string_of_term a' ^ " = " ^ string_of_term b' ^ ", got: " ^ string_of_term a))
  | _, _ ->
      let inferred = normalize env ctx (infer env ctx t) in
      (match inferred, ty' with
       | Universe i, Universe j when i >= j -> () (* cumulativity *)
       | _ ->
           if not (equal env ctx inferred ty') then
             raise (TypeError ("Type mismatch, expected: " ^ string_of_term ty' ^ ", got: " ^ string_of_term inferred)))

(* Tail-recursive normalization *)
and normalize env ctx t =
  let rec reduce_step t acc =
    match t with
    | App (Lam (x, _, body), arg) -> reduce_step (subst x arg body) acc
    | App (f, arg) ->
        let f' = normalize env ctx f in
        if equal env ctx f f' then reduce_step arg (fun arg' -> App (f, arg')) else reduce_step (App (f', arg)) acc
    | Elim (d, p, cases, Constr (j, d', args)) when d.name = d'.name ->
        let case = List.nth cases (j - 1) in
        let cj = List.assoc j d.constrs in
        let cj_subst = subst_many (List.combine (List.map fst d.params) (List.map snd d.params)) cj in
        reduce_step (apply_case env ctx d p cases case cj_subst args) acc
    | Elim (d, p, cases, t') ->
        let t'' = normalize env ctx t' in
        if equal env ctx t' t'' then acc t else reduce_step (Elim (d, p, cases, t'')) acc
    | Constr (j, d, args) ->
        let args' = List.map (fun arg -> normalize env ctx arg) args in
        acc (Constr (j, d, args'))
    | Fst (Pair (a, _)) -> reduce_step a acc
    | Snd (Pair (_, b)) -> reduce_step b acc
    | _ -> acc t
  in
  let rec normalize_loop t =
    let t' = reduce_step t (fun x -> x) in
    if equal env ctx t t' then t else normalize_loop t'
  in normalize_loop t

and apply_case env ctx d p cases case ty args =
  let rec apply ty args_acc remaining_args =
    match ty, remaining_args with
    | Pi (x, a, b), arg :: rest ->
        let b' = subst x arg b in
        let rec_arg =
          if equal env ctx a (Inductive d) then
            match arg with
            | Constr (j, d', sub_args) when d.name = d'.name ->
                Some (normalize env ctx (Elim (d, p, cases, arg)))
            | _ -> None
          else None
        in
        let new_args_acc = match rec_arg with | Some r -> r :: arg :: args_acc | None -> arg :: args_acc in
        apply b' new_args_acc rest
    | _, [] ->
        let rec apply_term t args =
          match t, args with
          | Lam (x, _, body), arg :: rest -> apply_term (subst x arg body) rest
          | _, [] -> t
          | _ -> raise (TypeError "Case application mismatch")
        in apply_term case (List.rev args_acc)
    | _ -> raise (TypeError "Constructor argument mismatch")
  in apply ty [] args

and string_of_term t =
  let buf = Buffer.create 16 in
  let rec print_term_depth depth t =
    if depth > 10 then Buffer.add_string buf "<deep>"
    else match t with
    | Var x -> Buffer.add_string buf x
    | Universe i -> Buffer.add_string buf ("Type" ^ string_of_int i)
    | Pi (x, a, b) ->
        Buffer.add_string buf ("Π(" ^ x ^ " : ");
        print_term_depth (depth + 1) a;
        Buffer.add_string buf ").";
        print_term_depth (depth + 1) b
    | Lam (x, _, body) ->
        Buffer.add_string buf ("λ" ^ x ^ ".");
        print_term_depth (depth + 1) body
    | App (f, arg) ->
        Buffer.add_string buf "(";
        print_term_depth (depth + 1) f;
        Buffer.add_string buf " ";
        print_term_depth (depth + 1) arg;
        Buffer.add_string buf ")"
    | Sigma (x, a, b) ->
        Buffer.add_string buf ("Σ(" ^ x ^ " : ");
        print_term_depth (depth + 1) a;
        Buffer.add_string buf ").";
        print_term_depth (depth + 1) b
    | Pair (a, b) ->
        Buffer.add_string buf "(";
        print_term_depth (depth + 1) a;
        Buffer.add_string buf ", ";
        print_term_depth (depth + 1) b;
        Buffer.add_string buf ")"
    | Fst t ->
        Buffer.add_string buf "fst ";
        print_term_depth (depth + 1) t
    | Snd t ->
        Buffer.add_string buf "snd ";
        print_term_depth (depth + 1) t
    | Id (ty, a, b) ->
        Buffer.add_string buf "{";
        print_term_depth (depth + 1) a;
        Buffer.add_string buf " = ";
        print_term_depth (depth + 1) b;
        Buffer.add_string buf " : ";
        print_term_depth (depth + 1) ty;
        Buffer.add_string buf "}"
    | Refl t ->
        Buffer.add_string buf "refl ";
        print_term_depth (depth + 1) t
    | Constr (i, d, args) ->
        Buffer.add_string buf d.name;
        Buffer.add_string buf ".";
        Buffer.add_string buf (string_of_int i);
        List.iter (fun c ->
          Buffer.add_string buf " ";
          print_term_depth (depth + 1) c
        ) args
    | Elim (d, p, cases, t') ->
        Buffer.add_string buf (d.name ^ ".elim ");
        print_term_depth (depth + 1) p;
        Buffer.add_string buf " [";
        List.iteri (fun i c ->
          if i > 0 then Buffer.add_string buf "; ";
          print_term_depth (depth + 1) c
        ) cases;
        Buffer.add_string buf "] ";
        print_term_depth (depth + 1) t'
    | Inductive d -> Buffer.add_string buf d.name
  in
  print_term_depth 0 t;
  Buffer.contents buf

and print_term t = print_string (string_of_term t)

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
    (1, Inductive { name = "List"; params = [("A", a)]; level = 0; constrs = []; mutual_group = ["List"] });
    (2, Pi ("x", a, Pi ("xs", Inductive { name = "List"; params = [("A", a)]; level = 0; constrs = []; mutual_group = ["List"] },
                        Inductive { name = "List"; params = [("A", a)]; level = 0; constrs = []; mutual_group = ["List"] })))
  ];
  mutual_group = ["List"]
}

let env = [("Nat", nat_def); ("List", list_def (Universe 0))]
let nat_ind = Inductive nat_def
let list_ind = Inductive (list_def (Universe 0))

let list_length =
  Lam ("l", list_ind,
    Elim ((list_def (Universe 0)),
          Pi ("_", list_ind, nat_ind),
          [Constr (1, nat_def, []);
           Lam ("x", Universe 0,
             Lam ("xs", list_ind,
               Lam ("ih", nat_ind,
                 Constr (2, nat_def, [Var "ih"]))))],
          Var "l"))

let sample_list =
  Constr (2, list_def (Universe 0),
    [Constr (1, nat_def, []);
     Constr (2, list_def (Universe 0),
       [Constr (2, nat_def, [Constr (1, nat_def, [])]);
        Constr (1, list_def (Universe 0), [])])])

let plus =
  Lam ("m", nat_ind, Lam ("n", nat_ind,
    Elim (nat_def,
          Pi ("_", nat_ind, nat_ind),
          [Var "m"; Lam ("k", nat_ind, Lam ("ih", nat_ind, Constr (2, nat_def, [Var "ih"])))],
          Var "n")))

let succ = Lam ("n", nat_ind, Constr (2, nat_def, [Var "n"]))

let test () =
  let ctx = empty_ctx in
  let zero = Constr (1, nat_def, []) in
  let one = Constr (2, nat_def, [zero]) in
  let two = Constr (2, nat_def, [one]) in
  let add_term = App (App (plus, two), two) in
  let add_normal = normalize env empty_ctx add_term in
  Printf.printf "Nat.add: "; print_term add_normal; print_endline "";
  Printf.printf "List.length: "; print_term (normalize env empty_ctx (App (list_length, sample_list))); print_endline "";

  (* Additional tests for Sigma and Id *)
  let pair_term = Pair (zero, one) in
  let pair_ty = Sigma ("x", nat_ind, nat_ind) in
  let id_term = Refl zero in
  let id_ty = Id (nat_ind, zero, zero) in

  try
    check env ctx pair_term pair_ty;
    Printf.printf "Pair typechecks\n";
    check env ctx id_term id_ty;
    Printf.printf "Refl typechecks\n";
    let succ_ty = infer env ctx succ in
    Printf.printf "typeof(Nat.succ): "; print_term succ_ty; print_endline "";
    let plus_ty = infer env ctx plus in
    Printf.printf "typeof(Nat.plus): "; print_term plus_ty; print_endline "";
    let inferred = infer env ctx add_term in
    Printf.printf "typeof(Nat.add 2 2): "; print_term inferred; print_endline ""
  with TypeError msg -> print_endline ("Type error: " ^ msg)

let _ = test ()
