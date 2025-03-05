(*

Copyright (c) Groupoid Infinity 2016-2025 DHARMA 5ht.co/license

Per: MLTT /w Calculus of Inductive Constructions

[1]. <a href="https://inria.hal.science/hal-01094195/document">Christine Paulin-Mohring. Introduction to the Calculus of Inductive Constructions.</a><br>
[2]. <a href="https://www.cs.unibo.it/~sacerdot/PAPERS/sadhana.pdf"> A. Asperti, W. Ricciotti, C. Sacerdoti Coen, E. Tassi. A compact kernel for the calculus of inductive constructions.</a><br>
[3]. <a href="https://www.cs.cmu.edu/%7Efp/papers/mfps89.pdf">Frank Pfenning, Christine Paulin-Mohring. Inductively Defined Types in the Calculus of Construction</a><br>

*)

(* Universe levels *)
type level = int

(* Variable names *)
type name = string

(* Terms and types *)
type term =
  | Var of name
  | Universe of level
  | Pi of name * term * term
  | Lam of name * term
  | App of term * term
  | Sigma of name * term * term
  | Pair of term * term
  | Fst of term
  | Snd of term
  | Id of term * term * term
  | Refl of term
  | Inductive of inductive  (* Inductive type D *)
  | Constr of int * inductive * term list  (* j-th constructor of D *)
  | Elim of inductive * term * term list * term  (* Elim D P cases t *)

(* Inductive type definition *)
and inductive = {
  name : string;                (* e.g., "Nat", "List" *)
  params : (name * term) list;  (* Parameters, e.g., [( "A", Universe 0 )] for List A *)
  level : level;                (* Type level: D : Type i *)
  constrs : (int * term) list;  (* Constructors: index j -> type Cj *)
  mutual_group : string list
}

(* Environment of inductive definitions *)
type env = (string * inductive) list
type context = (name * term) list

let empty_env : env = []
let empty_ctx : context = []
let add_var (ctx : context) (x : name) (ty : term) : context = (x, ty) :: ctx
let lookup_var (ctx : context) (x : name) : term option = try Some (List.assoc x ctx) with Not_found -> None
let rec count_pis (ty : term) : int = match ty with | Pi (_, _, body) -> 1 + count_pis body | _ -> 0
let rec apply_args (f : term) (args : term list) : term = match args with | [] -> f | arg :: rest -> apply_args (App (f, arg)) rest

exception TypeError of string



(* Substitution *)
let rec subst (x : name) (s : term) (t : term) : term =
  match t with
  | Var y -> if x = y then s else t
  | Universe i -> Universe i
  | Pi (y, a, b) ->
      if x = y then Pi (y, subst x s a, b)
      else Pi (y, subst x s a, subst x s b)
  | Lam (y, body) ->
      if x = y then Lam (y, body) else Lam (y, subst x s body)
  | App (f, arg) -> App (subst x s f, subst x s arg)
  | Sigma (y, a, b) ->
      if x = y then Sigma (y, subst x s a, b)
      else Sigma (y, subst x s a, subst x s b)
  | Pair (t1, t2) -> Pair (subst x s t1, subst x s t2)
  | Fst t -> Fst (subst x s t)
  | Snd t -> Snd (subst x s t)
  | Id (a, t1, t2) -> Id (subst x s a, subst x s t1, subst x s t2)
  | Refl t -> Refl (subst x s t)
  | Inductive d -> Inductive d
  | Constr (j, d, args) -> Constr (j, d, List.map (subst x s) args)
  | Elim (d, p, cases, t') -> Elim (d, subst x s p, List.map (subst x s) cases, subst x s t')

and equal (env : env) (ctx : context) (t1 : term) (t2 : term) : bool =
  match t1, t2 with
  | Var x, Var y -> x = y
  | Universe i, Universe j -> i = j
  | Pi (x, a, b), Pi (y, a', b') ->
      equal env ctx a a' &&
      let ctx' = add_var ctx x a in
      equal env ctx' b (subst y (Var x) b')
  | Lam (x, t), Lam (y, u) ->
      (* Avoid infer here; assume type checked earlier, or pass type explicitly *)
      let ctx' = add_var ctx x (Var "unknown_type") in (* Placeholder; refine later *)
      equal env ctx' t (subst y (Var x) u)
  | App (f, arg), App (f', arg') ->
      equal env ctx f f' && equal env ctx arg arg'
  | Sigma (x, a, b), Sigma (y, a', b') ->
      equal env ctx a a' &&
      let ctx' = add_var ctx x a in
      equal env ctx' b (subst y (Var x) b')
  | Pair (t1, t2), Pair (u1, u2) ->
      equal env ctx t1 u1 && equal env ctx t2 u2
  | Fst t, Fst u -> equal env ctx t u
  | Snd t, Snd u -> equal env ctx t u
  | Id (a, t, u), Id (a', t', u') ->
      equal env ctx a a' && equal env ctx t t' && equal env ctx u u'
  | Refl t, Refl u -> equal env ctx t u
  | Inductive d1, Inductive d2 ->
      d1.name = d2.name && d1.level = d2.level &&
      List.for_all2 (fun (n1, t1) (n2, t2) -> n1 = n2 && equal env ctx t1 t2) d1.params d2.params
  | Constr (j, d1, args1), Constr (k, d2, args2) ->
      j = k && d1.name = d2.name &&
      List.for_all2 (fun (n1, t1) (n2, t2) -> n1 = n2 && equal env ctx t1 t2) d1.params d2.params &&
      List.for_all2 (equal env ctx) args1 args2
  | Elim (d1, p1, cases1, t1), Elim (d2, p2, cases2, t2) ->
      d1.name = d2.name &&
      List.for_all2 (fun (n1, t1) (n2, t2) -> n1 = n2 && equal env ctx t1 t2) d1.params d2.params &&
      equal env ctx p1 p2 && List.for_all2 (equal env ctx) cases1 cases2 && equal env ctx t1 t2
  | _ -> false

(* Mutual recursive infer and check *)
and infer (env : env) (ctx : context) (t : term) : term =
  match t with
  | Var x ->
      (match lookup_var ctx x with
       | Some ty -> ty
       | None -> raise (TypeError ("Unbound variable: " ^ x)))
  | Universe i -> Universe (i + 1)
  | Pi (x, a, b) ->
      let a_ty = infer env ctx a in
      (match a_ty with
       | Universe i ->
           let ctx' = add_var ctx x a in
           let b_ty = infer env ctx' b in
           (match b_ty with
            | Universe j -> Universe (max i j)
            | _ -> raise (TypeError "Pi body must be a type"))
       | _ -> raise (TypeError "Pi domain must be a type"))
  | App (f, arg) ->
      let f_ty = infer env ctx f in
      (match f_ty with
       | Pi (x, a, b) ->
           check env ctx arg a;
           subst x arg b
       | _ -> raise (TypeError "Application requires a Pi type"))
  | Constr (j, d, args) ->
      (try
         let cj = List.assoc j d.constrs in
         let cj_subst = List.fold_left2 (fun acc (n, _) arg -> subst n arg acc) cj d.params (List.map snd d.params) in
         let rec check_args ty args_acc remaining_args =
           match ty, remaining_args with
           | Pi (x, a, b), arg :: rest ->
               check env ctx arg a;
               check_args (subst x arg b) (arg :: args_acc) rest
           | _, [] -> ty
           | _ -> raise (TypeError "Constructor argument mismatch")
         in
         check_args cj_subst [] args
       with Not_found -> raise (TypeError ("Invalid constructor index: " ^ string_of_int j)))
  | Elim (d, p, cases, t') ->
      let d_ty = infer env ctx (Inductive d) in
      (match d_ty with
       | Universe i ->
           let d_applied = apply_inductive d (List.map snd d.params) in
           let t_ty = infer env ctx t' in
           if not (equal env ctx t_ty d_applied) then raise (TypeError "Elim target type mismatch");
           let expected_p_ty = 
             List.fold_right (fun (n, p_ty) acc -> Pi (n, p_ty, acc)) d.params (Pi ("x", d_applied, Universe d.level)) in
           check env ctx p expected_p_ty;
           let p_ty = infer env ctx p in
           (match p_ty with
            | Pi (_, _, Universe k) ->
                if List.length cases <> List.length d.constrs then
                  raise (TypeError "Wrong number of cases in Elim");
                List.iteri (fun j case ->
                  let cj = List.assoc (j + 1) d.constrs in
                  let cj_subst = List.fold_left2 (fun acc (n, _) arg -> subst n arg acc) cj d.params (List.map snd d.params) in
                  let rec replace_d_with_p ty =
                    match ty with
                    | Inductive d' when d'.name = d.name -> App (p, Var "x")
                    | Pi (y, a, b) -> Pi (y, replace_d_with_p a, replace_d_with_p b)
                    | App (f, arg) -> App (replace_d_with_p f, replace_d_with_p arg)
                    | _ -> ty
                  in
                  let case_ty = replace_d_with_p cj_subst in
                  check env ctx case case_ty
                ) cases;
                App (p, t')
            | _ -> raise (TypeError "Elim motive must return a type"))
       | _ -> raise (TypeError "Inductive type must be a Type"))
  | _ -> raise (TypeError "Inference not implemented for this term")

and check (env : env) (ctx : context) (t : term) (ty : term) : unit =
  match t, ty with
  | Lam (x, body), Pi (y, a, b) ->
      let ctx' = add_var ctx x a in
      check env ctx' body b
  | Pair (t1, t2), Sigma (x, a, b) ->
      check env ctx t1 a;
      check env ctx t2 (subst x t1 b)
  | Refl t, Id (a, t1, t2) ->
      check env ctx t a;
      if not (equal env ctx t t1 && equal env ctx t t2) then
        raise (TypeError "Refl arguments do not match Id type")
  | _, _ ->
      let inferred = infer env ctx t in
      if not (equal env ctx inferred ty) then
        raise (TypeError "Inferred type does not match expected type")

(* Apply parameters to an inductive type *)
and apply_inductive (d : inductive) (args : term list) : term =
  if List.length d.params <> List.length args then raise (TypeError "Parameter mismatch");
  let subst_param t = List.fold_left2 (fun acc (n, _) arg -> subst n arg acc) t d.params args
  in Inductive { d with constrs = List.map (fun (j, ty) -> (j, subst_param ty)) d.constrs }

let rec reduce (env : env) (ctx : context) (t : term) : term =
  match t with
  | App (Lam (x, body), arg) -> subst x arg body
  | Fst (Pair (t1, _)) -> t1
  | Snd (Pair (_, t2)) -> t2
  | Elim (d, p, cases, Constr (j, d', args)) when List.mem d'.name d.mutual_group ->
      (* Find the inductive definition in the environment *)
      let d_target = List.find (fun (_, def) -> def.name = d'.name) env in
      let param_args = List.map snd d.params in
      if List.length d.params <> List.length d'.params then t
      else
        let cj_ty = List.assoc j (snd d_target).constrs in
        let expected_arity = count_pis cj_ty - List.length d.params in
        if List.length args <> expected_arity then t
        else
          let cj = List.nth cases (j - 1) in (* 0-based index *)
          let cj_ty_subst = List.fold_left2 (fun acc (n, _) arg -> subst n arg acc) cj_ty d.params param_args in
          (* Collect recursive arguments and their types *)
          let rec collect_rec_args ty acc_args pos =
            match ty with
            | Pi (x, a, b) ->
                let rec_type =
                  match a with
                  | Inductive d'' when List.mem d''.name d.mutual_group ->
                      Some (List.find (fun (_, def) -> def.name = d''.name) env |> snd)
                  | _ -> None
                in
                (match rec_type with
                 | Some d_rec ->
                     collect_rec_args b ((List.nth args pos, d_rec) :: acc_args) (pos + 1)
                 | None ->
                     collect_rec_args b acc_args (pos + 1))
            | _ -> acc_args
          in
          let rec_args = collect_rec_args cj_ty_subst [] 0 in
          (* Substitute recursive args with Elim calls *)
          let rec subst_rec_args fn fn_args rec_args pos =
            match fn_args, rec_args with
            | a :: rest_args, (r, d_rec) :: rest_rec when equal env ctx a r ->
                let elim_term = Elim (d_rec, p, cases, r) in
                subst_rec_args (App (fn, elim_term)) rest_args rest_rec (pos + 1)
            | a :: rest_args, _ :: rest_rec ->
                subst_rec_args (App (fn, a)) rest_args rest_rec (pos + 1)
            | a :: rest_args, [] ->
                subst_rec_args (App (fn, a)) rest_args [] (pos + 1)
            | [], _ -> fn
          in
          subst_rec_args cj args rec_args 0
  | Elim (d, p, cases, t') ->
      let t'' = reduce env ctx t' in
      if equal env ctx t' t'' then t else Elim (d, p, cases, t'')
  | App (f, arg) ->
      let f' = reduce env ctx f in
      if equal env ctx f f' then App (f', arg) else App (f', arg)
  | _ -> t

let rec normalize (env : env) (ctx : context) (t : term) : term =
  let t' = reduce env ctx t in
  if equal env ctx t t' then t
  else normalize env ctx t'

(* Pretty Printer *)

let rec print_term (t : term) : unit =
  match t with
  | Var x -> Printf.printf "%s" x
  | Universe i -> Printf.printf "Type%d" i
  | Pi (x, a, b) ->
      Printf.printf "Π(%s : " x;
      print_term a;
      Printf.printf "). ";
      print_term b
  | Lam (x, body) ->
      Printf.printf "λ%s. " x;
      print_term body
  | App (f, arg) ->
      Printf.printf "(";
      print_term f;
      Printf.printf " ";
      print_term arg;
      Printf.printf ")"
  | Sigma (x, a, b) ->
      Printf.printf "Σ(%s : " x;
      print_term a;
      Printf.printf "). ";
      print_term b
  | Pair (t1, t2) ->
      Printf.printf "(";
      print_term t1;
      Printf.printf ", ";
      print_term t2;
      Printf.printf ")"
  | Fst t ->
      Printf.printf "fst ";
      print_term t
  | Snd t ->
      Printf.printf "snd ";
      print_term t
  | Id (a, t1, t2) ->
      Printf.printf "Id ";
      print_term a;
      Printf.printf " ";
      print_term t1;
      Printf.printf " ";
      print_term t2
  | Refl t ->
      Printf.printf "refl ";
      print_term t
  | Inductive d ->
      Printf.printf "%s" d.name;
      List.iter (fun (_, p) -> Printf.printf " "; print_term p) d.params
  | Constr (j, d, args) ->
      (* Map constructor index to a name for readability *)
      let constr_name =
        match d.name, j with
        | "Nat", 1 -> "zero"
        | "Nat", 2 -> "succ"
        | "Even", 1 -> "ezero"
        | "Even", 2 -> "esucc"
        | _ -> Printf.sprintf "%s%d" d.name j
      in
      Printf.printf "%s" constr_name;
      List.iter (fun arg -> Printf.printf " "; print_term arg) args
  | Elim (d, p, cases, t') ->
      Printf.printf "elim_%s " d.name;
      print_term p;
      Printf.printf " [";
      List.iteri (fun i c ->
        if i > 0 then Printf.printf "; ";
        print_term c
      ) cases;
      Printf.printf "] ";
      print_term t'


(* Examples *)

let nat_def = {
  name = "Nat";
  params = [];
  level = 0;
  constrs = [
    (0, Inductive { name = "Nat"; params = []; level = 0; constrs = []; mutual_group = [] }); (* zero : Nat *)
    (1, Pi ("n", Inductive { name = "Nat"; params = []; level = 0; constrs = []; mutual_group = [] }, 
                 Inductive { name = "Nat"; params = []; level = 0; constrs = []; mutual_group = [] })) (* succ : Nat -> Nat *)
  ];
  mutual_group = []
}

let list_def (a : term) = {
  name = "List";
  params = [("A", a)];
  level = (match a with Universe i -> i | _ -> failwith "List param must be a type");
  constrs = [
    (0, Inductive { name = "List"; params = [("A", a)]; level = 0; constrs = []; mutual_group = [] }); (* nil : List A *)
    (1, Pi ("x", a,
        Pi ("xs", Inductive { name = "List"; params = [("A", a)]; level = 0; constrs = []; mutual_group = [] },
                  Inductive { name = "List"; params = [("A", a)]; level = 0; constrs = []; mutual_group = [] }))) (* cons : A -> List A -> List A *)
  ];
  mutual_group = []
}

let nat_even_def = {
  name = "NatEven";
  params = [];
  level = 0;
  constrs = [
    (1, Inductive { name = "NatEven"; params = []; level = 0; constrs = []; mutual_group = ["NatEven"; "Even"] }); (* zero *)
    (2, Pi ("n", Inductive { name = "NatEven"; params = []; level = 0; constrs = []; mutual_group = ["NatEven"; "Even"] },
                 Inductive { name = "NatEven"; params = []; level = 0; constrs = []; mutual_group = ["NatEven"; "Even"] })) (* succ *)
  ];
  mutual_group = ["NatEven"; "Even"]
}

let even_def = {
  name = "Even";
  params = [];
  level = 0;
  constrs = [
    (1, Inductive { name = "Even"; params = []; level = 0; constrs = []; mutual_group = ["NatEven"; "Even"] }); (* ezero *)
    (2, Pi ("n", Inductive { name = "NatEven"; params = []; level = 0; constrs = []; mutual_group = ["NatEven"; "Even"] },
                 Inductive { name = "Even"; params = []; level = 0; constrs = []; mutual_group = ["NatEven"; "Even"] })) (* esucc *)
  ];
  mutual_group = ["NatEven"; "Even"]
}


let nat_ind      = Inductive nat_def
let nat_even_ind = Inductive nat_even_def
let even_ind     = Inductive even_def

let env_with_nat_list = [("Nat", nat_def), ("List", list_def)]
let env_mutual        = [("NatEven", nat_even_def); ("Even", even_def)]


let plus =
  Lam ("m", Lam ("n",
    Elim (nat_def,
          Pi ("_", nat_ind, nat_ind),
          [Var "m"; Lam ("k", Lam ("ih", Constr (2, nat_def, [Var "ih"])))],
          Var "n"
    )))

let plus_ty = Pi ("m", nat_ind, Pi ("n", nat_ind, nat_ind))

let length =
  Lam ("n",
    Elim (nat_def,
          Pi ("_", nat_even_ind, nat_even_ind),
          [Constr (1, nat_def, []);  (* zero -> zero *)
           Lam ("k", Lam ("ih", Constr (2, nat_even_def, [Var "ih"])))], (* succ k ih -> succ ih *)
          Var "n"))

(* Mutual test: toEven : Nat -> NatEven *)
let to_even =
  Lam ("n",
    Elim (nat_even_def,
          Pi ("_", nat_even_ind, nat_even_ind),
          [Constr (1, nat_even_def, []);  (* zero -> ezero *)
           Lam ("k", Lam ("ih", Constr (2, nat_even_def, [Var "k"])))], (* succ k ih -> esucc k *)
          Var "n"))

let test () =
  try
    check env_mutual empty_ctx plus plus_ty;
    print_endline "Type checking succeeded!"
  with
  | TypeError msg -> print_endline ("Type error: " ^ msg)

let test_normalize () =
  let zero = Constr (1, nat_even_def, []) in
  let one = Constr (2, nat_even_def, [zero]) in
  let two = Constr (2, nat_even_def, [one]) in
  let term = App (length, two) in
  let normal = normalize env_mutual empty_ctx term in

  Printf.printf "Length 2 normalized: ";
  print_term normal;
  print_endline "";
  let even_term = App (to_even, two) in
  let even_normal = normalize env_mutual empty_ctx even_term in
  Printf.printf "ToEven 2 normalized: ";
  print_term even_normal;
  print_endline ""


let _ = test_normalize ()
