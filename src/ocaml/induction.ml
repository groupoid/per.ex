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
  | Lam of name * term * term
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
let var c = match c with | Some x -> x | None -> Universe 0
let rec count_pis (ty : term) : int = match ty with | Pi (_, _, body) -> 1 + count_pis body | _ -> 0
let rec apply_args (f : term) (args : term list) : term = match args with | [] -> f | arg :: rest -> apply_args (App (f, arg)) rest
let rec count_lambdas t = match t with | Lam (_, _, body) -> 1 + count_lambdas body | _ -> 0

exception TypeError of string

(* Substitution *)
let rec subst (x : name) (s : term) (t : term) : term =
  match t with
  | Var y -> if x = y then s else t
  | Universe i -> Universe i
  | Pi (y, a, b) ->
      if x = y then Pi (y, subst x s a, b)
      else Pi (y, subst x s a, subst x s b)
  | Lam (y, domain, body) ->
      if x = y then Lam (y, domain, body)  (* y shadows x, no subst in body *)
      else Lam (y, subst x s domain, subst x s body)
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
  | Pi (x, a, b), Pi (y, a', b') 
  | Lam (x, a, b), Lam (y, a', b') ->
      equal env ctx a a' &&
      let ctx' = add_var ctx x a in
      equal env ctx' b (subst y (Var x) b')
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

and replace_d_with_p d p ty is_arg =
    match ty with
    | Inductive d' when d'.name = d.name && is_arg -> App (p, Var "_")
    | Inductive d' -> ty
    | Pi (y, a, b) -> Pi (y, replace_d_with_p d p a true, replace_d_with_p d p b false)
    | App (f, arg) -> App (replace_d_with_p d p f false, replace_d_with_p d p arg false)
    | _ -> ty

(* Mutual recursive infer and check *)
let rec infer (env : env) (ctx : context) (t : term) : term =
  match t with
  | Var x ->
      (match lookup_var ctx x with
       | Some ty -> ty
       | None -> raise (TypeError ("Unbound variable: " ^ x)))
  | Universe i -> Universe (i + 1)
  | Pi (x, a, b) ->
      let a_ty = infer env ctx a in
      let ctx' = add_var ctx x a in
      let b_ty = infer env ctx' b in
      (match a_ty with
       | Universe i ->
           (match b_ty with
            | Universe j -> Universe (max i j)
            | _ -> Pi (x, a, b_ty))
       | _ -> Pi (x, a, b_ty))
  | Lam (x, domain, body) ->
      let domain_ty = infer env ctx domain in
      let ctx' = add_var ctx x domain in
      let body_ty = infer env ctx' body in
      Pi (x, domain, body_ty)  (* Domain can be any type term *)
  | App (f, arg) ->
      let f_ty = infer env ctx f in
      (match f_ty with
       | Pi (x, a, b) ->
           check env ctx arg a;
           subst x arg b
       | _ -> raise (TypeError "Application requires a Pi type"))
  | Inductive d ->
      Inductive d
(* ... *)
  | Elim (d, p, cases, t') ->
      let d_ty = infer env ctx (Inductive d) in
      let d_applied = apply_inductive d (List.map snd d.params) in
      let t_ty = infer env ctx t' in
      if not (equal env ctx t_ty d_applied) then raise (TypeError "Elim target type mismatch");
      let expected_p_ty = Pi ("_", d_applied, d_applied) in
      check env ctx p expected_p_ty;
      let p_ty = infer env ctx p in
      (match p_ty with
       | Pi (_, _, codomain) ->
           if List.length cases <> List.length d.constrs then
             raise (TypeError "Wrong number of cases in Elim");
           List.iteri (fun j case ->
             let cj = List.assoc (j + 1) d.constrs in
             let cj_subst = List.fold_left2 (fun acc (n, _) arg -> subst n arg acc) cj d.params (List.map snd d.params) in
             let case_ty = cj_subst  (* Full constructor type *)
             in
             check env ctx case case_ty
           ) cases;
           App (p, t')
       | _ -> raise (TypeError "Elim motive must be a function type"))
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
  | _ -> raise (TypeError "Inference not implemented for this term")

and check (env : env) (ctx : context) (t : term) (ty : term) : unit =
  match t, ty with
  | Lam (x, domain, body), Pi (y, a, b) ->
      check env ctx domain a;
      let ctx' = add_var ctx x domain in
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
      Printf.printf "Checking term: "; print_term t; print_endline "";
      Printf.printf "inferred: "; print_term inferred; print_endline "";
      Printf.printf "expected: "; print_term ty; print_endline "";
      if not (equal env ctx inferred ty) then
        raise (TypeError "Inferred type does not match expected type")

and reduce (env : env) (ctx : context) (t : term) : term =
  match t with
  | App (Lam (x, _, body), arg) ->
      Printf.printf "Reducing App Lam %s\n" x; 
      subst x arg body
  | Elim (d, p, cases, Constr (j, d', args)) when List.mem d'.name d.mutual_group ->
      Printf.printf "Reducing Elim %s, constructor %d, mutual_group: %s\n" d.name j (String.concat "," d.mutual_group);
      let d_target = List.find (fun (_, def) -> def.name = d'.name) env |> snd in
      let param_args = List.map snd d.params in
      let cj = List.assoc j d_target.constrs in
      let cj_subst = List.fold_left2 (fun acc (n, _) arg -> subst n arg acc) cj d.params param_args in
      let case = List.nth cases (j - 1) in
      let rec_args = collect_rec_args env ctx cj_subst args d in
      Printf.printf "Applying case %d with %d recursive args\n" j (List.length rec_args);
      subst_rec_args env ctx p cases case args rec_args


  | Elim (d, p, cases, t') ->
      let t'' = reduce env ctx t' in
      if equal env ctx t' t'' then t else Elim (d, p, cases, t'')
  | App (f, arg) ->
      let f' = reduce env ctx f in
      if equal env ctx f f' then App (f', arg) else App (f', arg)
  | Constr (j, d, args) ->
      Constr (j, d, List.map (reduce env ctx) args)
  | _ -> t

and collect_rec_args env ctx ty args d =
  let rec collect ty acc pos =
    match ty with
    | Pi (x, a, b) ->
        let arg = List.nth args pos in
        let rec_type = match a with
          | Inductive d' when List.mem d'.name d.mutual_group -> Some d'
          | _ -> None
        in
        (match rec_type with
         | Some d_rec -> collect b ((arg, d_rec) :: acc) (pos + 1)
         | None -> collect b acc (pos + 1))
    | _ -> acc
  in collect ty [] 0

and subst_rec_args env ctx p cases fn fn_args rec_args =
  let rec apply_args fn args rec_args =
    match fn, args, rec_args with
    | Lam (x, domain, body), a :: rest_args, [] ->
        Printf.printf "Applying %s to " x; print_term a; print_endline "";
        apply_args (subst x a body) rest_args []
    | Lam (x, domain, body), a :: rest_args, (r, d_rec) :: rest_rec when equal env ctx a r ->
        let elim_term = normalize env ctx (Elim (d_rec, p, cases, r)) in
        Printf.printf "Applying recursive %s to " x; print_term elim_term; print_endline "";
        apply_args (subst x elim_term body) rest_args rest_rec
    | Lam (x, domain, body), a :: rest_args, _ ->
        Printf.printf "Applying %s to " x; print_term a; print_endline "";
        apply_args (subst x a body) rest_args rec_args
    | Lam (x, domain, body), [], (r, d_rec) :: rest_rec ->
        let elim_term = normalize env ctx (Elim (d_rec, p, cases, r)) in
        Printf.printf "Applying recursive %s to " x; print_term elim_term; print_endline "";
        apply_args (subst x elim_term body) [] rest_rec
    | Lam (x, domain, body), [], [] ->
        Printf.printf "No args for %s, reducing body: " x; print_term body; print_endline "";
        normalize env ctx body
    | Lam (x, domain, body), [], rec_args ->
        Printf.printf "Applying recursive %s with rec_args: " x; print_term body; print_endline "";
        apply_args body [] rec_args
    | body, [], [] -> body
    | body, [], _ -> body
    | _ -> raise (Failure (Printf.sprintf "Mismatch in subst_rec_args: fn_args=%d, rec_args=%d" 
                            (List.length args) (List.length rec_args)))
  in
  let result = apply_args fn fn_args rec_args in
  normalize env ctx result

(* Apply parameters to an inductive type *)
and apply_inductive (d : inductive) (args : term list) : term =
  if List.length d.params <> List.length args then raise (TypeError "Parameter mismatch");
  let subst_param t = List.fold_left2 (fun acc (n, _) arg -> subst n arg acc) t d.params args
  in Inductive { d with constrs = List.map (fun (j, ty) -> (j, subst_param ty)) d.constrs }

(* Helper: Collect free variables *)
and free_vars t =
  let rec fv acc t =
    match t with
    | Var x -> x :: acc
    | Universe _ -> acc
    | Pi (x, a, b) -> fv (fv (List.filter ((<>) x) acc) a) b
    | Lam (x, _, b) -> fv (List.filter ((<>) x) acc) b
    | App (f, arg) -> fv (fv acc f) arg
    | _ -> acc
  in fv [] t


and normalize (env : env) (ctx : context) (t : term) : term =
  let t' = reduce env ctx t in
  if equal env ctx t t' then t else normalize env ctx t'

(* Pretty Printer *)

and print_term (t : term) : unit =
  match t with
  | Var x -> Printf.printf "%s" x
  | Universe i -> Printf.printf "Type%d" i
  | Pi (x, a, b) ->
      Printf.printf "Π(%s : " x;
      print_term a;
      Printf.printf "). ";
      print_term b
  | Lam (x, _, body) ->
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
      Printf.printf "Ind-%s" d.name;
      List.iter (fun (_, p) -> Printf.printf " "; print_term p) d.params
  | Constr (j, d, args) ->
      (* Map constructor index to a name for readability *)
      let constr_name =
        match d.name, j with
        | "Nat", 1 -> "zero"
        | "Nat", 2 -> "succ"
        | "Even", 1 -> "ezero"
        | "Even", 2 -> "esucc"
        | "List", 1 -> "nil"
        | "List", 2 -> "cons"
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
    (1, Inductive { name = "Nat"; params = []; level = 0; constrs = []; mutual_group = ["Nat"] }); (* zero : Nat *)
    (2, Pi ("n", Inductive { name = "Nat"; params = []; level = 0; constrs = []; mutual_group = ["Nat"] }, 
                 Inductive { name = "Nat"; params = []; level = 0; constrs = []; mutual_group = ["Nat"] })) (* succ : Nat -> Nat *)
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

let even_def = {
  name = "Even";
  params = [];
  level = 0;
  constrs = [
    (1, Inductive { name = "Even"; params = []; level = 0; constrs = []; mutual_group = ["Nat"; "Even"] }); (* ezero *)
    (2, Pi ("n", Inductive { name = "Nat"; params = []; level = 0; constrs = []; mutual_group = ["Nat"; "Even"] },
                 Inductive { name = "Even"; params = []; level = 0; constrs = []; mutual_group = ["Nat"; "Even"] })) (* esucc *)
  ];
  mutual_group = ["Nat"; "Even"]
}

let env_with_nat_list = [("Nat", nat_def), ("List", list_def (Universe 0))]
let env_mutual        = [("Even", even_def); ("Nat", nat_def); ("List", list_def (Universe 0))]

let nat_ind      = Inductive nat_def
let list_ind     = Inductive (list_def (Universe 0))
let even_ind     = Inductive even_def

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

let length =
  Lam ("n", nat_ind,  (* n : Nat *)
    Elim (nat_def,
          Pi ("_", nat_ind, nat_ind),
          [Constr (1, nat_def, []);  (* zero -> zero *)
           Lam ("k", nat_ind,  (* k : Nat *)
             Lam ("ih", nat_ind,  (* ih : Nat *)
               Constr (2, nat_def, [Var "ih"])))], (* succ ih *)
          Var "n"))

let to_even =
  Lam ("n", nat_ind,  (* n : Nat *)
    Elim (nat_def,
          Pi ("_", nat_ind, even_ind),
          [Constr (1, even_def, []);  (* ezero *)
           Lam ("k", nat_ind,  (* k : Nat *)
             Lam ("ih", even_ind,  (* ih : Even *)
               Constr (2, even_def, [Var "k"])))], (* esucc k *)
          Var "n"))

let test () =

  (* Test mutual recursion *)
  let zero = Constr (1, nat_def, []) in
  let one = Constr (2, nat_def, [zero]) in
  let two = Constr (2, nat_def, [one]) in
  let even_term = App (to_even, two) in
  let even_normal = normalize env_mutual empty_ctx even_term in
  Printf.printf "ToEven: ";
  print_term even_normal;
  print_endline "";

  let add_term = App (App (plus, two), two) in
  let add_normal = normalize env_mutual empty_ctx add_term in
  Printf.printf "Add(4): ";
  print_term add_normal;
  print_endline "";

  (* Test list length *)
  let list_term = App (list_length, sample_list) in
  let list_normal = normalize env_mutual empty_ctx list_term in
  Printf.printf "List length: ";
  print_term list_normal;
  print_endline "";

  (* Test raw sample list *)
  Printf.printf "Sample list: ";
  print_term sample_list;
  print_endline "";

  try check env_mutual empty_ctx plus plus_ty;
  Printf.printf "plus OK\n";
  with | TypeError msg -> print_endline ("Type error: " ^ msg)

let _ = test ()
