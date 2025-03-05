let trace: bool = false

type level = int
type name = string


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
  | Inductive of inductive
  | Constr of int * inductive * term list
  | Elim of inductive * term * term list * term

and inductive = {
  name : string;
  params : (name * term) list;
  level : level;
  constrs : (int * term) list;
  mutual_group : string list
}

module Context = Hashtbl.Make(struct
  type t = name
  let equal = (=)
  let hash = Hashtbl.hash
end)

type env = (string * inductive) list
type context = term Context.t
type memo_key = term * context
type memo_value = term option
let memo : (memo_key, memo_value) Hashtbl.t = Hashtbl.create 1024

exception TypeError of string

let empty_env : env = []
let empty_ctx () = Context.create 16
let add_var ctx x ty = Context.replace ctx x ty; ctx
let lookup_var ctx x = Context.find_opt ctx x

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
  if t1 == t2 then true
  else match t1, t2 with
  | Var x, Var y -> x = y
  | Universe i, Universe j -> i = j
  | App (f1, a1), App (f2, a2) -> equal env ctx f1 f2 && (f1 == f2 || equal env ctx a1 a2)
  | Pi (x, a1, b1), Pi (y, a2, b2) -> equal env ctx a1 a2 && (a1 == a2 || equal env (add_var ctx x a1) b1 (subst y (Var x) b2))
  | Lam (x, d1, b1), Lam (y, d2, b2) -> equal env ctx d1 d2 && (d1 == d2 || equal env (add_var ctx x d1) b1 (subst y (Var x) b2))
  | Inductive d1, Inductive d2 -> d1.name = d2.name && d1.level = d2.level && List.for_all2 (fun (n1, t1) (n2, t2) -> n1 = n2 && equal env ctx t1 t2) d1.params d2.params
  | Constr (j, d1, args1), Constr (k, d2, args2) -> j = k && d1.name = d2.name && List.for_all2 (equal env ctx) args1 args2
  | Elim (d1, p1, cases1, t1), Elim (d2, p2, cases2, t2) -> d1.name = d2.name && equal env ctx p1 p2 && List.for_all2 (equal env ctx) cases1 cases2 && equal env ctx t1 t2
  | _ -> false

let apply_inductive d args =
  if List.length d.params <> List.length args then raise (TypeError "Parameter mismatch in inductive type");
  let m = List.combine (List.map fst d.params) args in Inductive { d with constrs = List.map (fun (j, ty) -> (j, subst_many m ty)) d.constrs }

type whnf = 
  | WHNF_Neutral of term
  | WHNF_Value of term

let rec reduce env ctx t =
  match t with
  | App (Lam (x, _, body), arg) -> subst x arg body
  | App (Pi (x, a, b), arg) -> subst x arg b
  | App (f, arg) -> let f' = reduce env ctx f in if equal env ctx f f' then App (f, reduce env ctx arg) else App (f', arg)
  | Elim (d, p, cases, Constr (j, d', args)) when d.name = d'.name ->
      let case = List.nth cases (j - 1) in
      let cj = List.assoc j d.constrs in
      let cj_subst = subst_many (List.combine (List.map fst d.params) (List.map snd d.params)) cj in
      apply_case env ctx d p cases case cj_subst args
  | Elim (d, p, cases, t') -> let t'' = reduce env ctx t' in if equal env ctx t' t'' then t else Elim (d, p, cases, t'')
  | Constr (j, d, args) -> Constr (j, d, List.map (reduce env ctx) args)
  | _ -> t

and whnf env ctx t =
  match reduce env ctx t with
  | App (f, arg) as app -> 
      (match whnf env ctx f with
       | WHNF_Value (Lam (x, _, body)) -> whnf env ctx (subst x arg body)
       | WHNF_Neutral f' -> WHNF_Neutral app
       | WHNF_Value f' -> WHNF_Neutral (App (f', arg)))
  | t' when equal env ctx t t' -> WHNF_Value t
  | t' -> whnf env ctx t'

and normalize env ctx t =
  match whnf env ctx t with
  | WHNF_Value v -> v
  | WHNF_Neutral n -> normalize_neutral env ctx n

and normalize_neutral env ctx t =
  match t with
  | App (f, arg) -> App (normalize env ctx f, normalize env ctx arg)
  | _ -> t

and apply_case env ctx d p cases case ty args =
  let rec apply ty args_acc remaining_args =
    match ty, remaining_args with
    | Pi (x, a, b), arg :: rest ->
        let b' = subst x arg b in
        let rec_arg = 
          if equal env ctx a (Inductive d) then
            match arg with
            | Constr (j, d', sub_args) when d.name = d'.name -> Some (normalize env ctx (Elim (d, p, cases, arg)))
            | _ -> None
          else None
        in
        let new_args_acc = match rec_arg with
          | Some r -> r :: arg :: args_acc
          | None -> arg :: args_acc
        in apply b' new_args_acc rest
    | _, [] -> 
        let rec apply_term t args =
          match t, args with
          | Lam (x, _, body), arg :: rest -> apply_term (subst x arg body) rest
          | _, [] -> t
          | _ -> raise (TypeError "Case application mismatch")
        in apply_term case (List.rev args_acc)
    | _ -> raise (TypeError "Constructor argument mismatch")
  in apply ty [] args

let rec infer env ctx t =
  let key = (t, ctx) in
  match Hashtbl.find_opt memo key with
  | Some (Some ty) -> ty
  | _ ->
      let result = match t with
        | Var x -> 
            (match lookup_var ctx x with
             | Some ty -> ty
             | None -> raise (TypeError ("Unbound variable: " ^ x)))
        | Universe i -> 
            if (trace) then Printf.printf "Inferring Universe %d: Type%d\n" i (i + 1);
            Universe (i + 1)
        | Pi (x, a, b) ->
            if (trace) then Printf.printf "Inferring Pi %s\n" x;
            let i = check_universe env ctx a in
            if (trace) then Printf.printf "Domain level: %d\n" i;
            let ctx' = add_var ctx x a in
            let j = check_universe env ctx' b in
            if (trace) then Printf.printf "Codomain level: %d\n" j;
            let result = Universe (max i j + 1) in  (* CIC rule *)
            if (trace) then (Printf.printf "Pi type: "; print_term result; print_endline "");
            result
        | Lam (x, domain, body) ->
            if (trace) then (Printf.printf "Inferring Lam %s: domain = " x; print_term domain; print_endline "");
            check env ctx domain (infer env ctx domain);
            let ctx' = add_var ctx x domain in
            let body_ty = infer env ctx' body in
            if (trace) then (Printf.printf "Inferred body type: "; print_term body_ty; print_endline "");
            let pi_ty = Pi (x, domain, body_ty) in
            if (trace) then (Printf.printf "Returning Pi type: "; print_term pi_ty; print_endline "");
            pi_ty
        | App (f, arg) ->
            (match infer env ctx f with
             | Pi (x, a, b) -> check env ctx arg a; subst x arg b
             | ty -> Printf.printf "App failed: inferred "; print_term ty; print_endline "";
                     raise (TypeError "Application requires a Pi type"))
        | Inductive d ->
            List.iter (fun (_, ty) -> 
              match infer env ctx ty with
              | Universe _ -> ()
              | _ -> raise (TypeError "Inductive parameters must be types")
            ) d.params;
            Universe d.level
        | Constr (j, d, args) ->
            let cj = List.assoc j d.constrs in
            let cj_subst = subst_many (List.combine (List.map fst d.params) (List.map snd d.params)) cj in
            check_constructor_args env ctx cj_subst args
        | Elim (d, p, cases, t') -> check_elim env ctx d p cases t'
      in
      Hashtbl.replace memo key (Some result);
      result

and check_universe env ctx t =
  match infer env ctx t with
  | Universe i -> i
  | _ -> raise (TypeError "Expected a universe")

and check_constructor_args env ctx ty args =
  let rec check_args ty args_acc = function
    | [] -> ty
    | arg :: rest ->
        match ty with
        | Pi (x, a, b) ->
            check env ctx arg a;
            check_args (subst x arg b) (arg :: args_acc) rest
        | _ -> raise (TypeError "Too many arguments to constructor")
  in check_args ty [] args

and check_elim env ctx d p cases t' =
  if (trace) then (Printf.printf "Checking Elim for %s\n" d.name);
  let t_ty = infer env ctx t' in
  if (trace) then (Printf.printf "Target type: "; print_term t_ty; print_endline "");
  let d_applied = apply_inductive d (List.map snd d.params) in
  if not (equal env ctx t_ty d_applied) then
    raise (TypeError "Elimination target type mismatch");
  let motive_ty_ty = Universe (d.level + 1) in
  if (trace) then (Printf.printf "Checking motive against: "; print_term motive_ty_ty; print_endline "");
  let p_ty = infer env ctx p in
  if (trace) then (Printf.printf "Inferred motive type: "; print_term p_ty; print_endline "");
  check env ctx p motive_ty_ty;
  if List.length cases <> List.length d.constrs then
    raise (TypeError "Number of cases doesn't match constructors");
  List.iteri (fun j case ->
    let j_idx = j + 1 in
    let cj = List.assoc j_idx d.constrs in
    let cj_subst = subst_many (List.combine (List.map fst d.params) (List.map snd d.params)) cj in
    let rec compute_case_type ty ctx_acc =
      match normalize env ctx ty with
      | Pi (x, a, b) ->
          let var = Var x in
          let ctx' = add_var ctx_acc x a in
          let b_ty = compute_case_type b ctx' in
          if equal env ctx a d_applied then
            Pi (x, a, Pi ("ih", normalize env ctx (App (p, var)), b_ty))
          else Pi (x, a, b_ty)
      | Inductive d' when d'.name = d.name ->
          (match normalize env ctx p with
           | Pi (x, _, b) ->
               let constr = Constr (j_idx, d, []) in
               normalize env ctx (subst x constr b)
           | _ -> raise (TypeError "Motive must be a Pi type"))
      | _ -> raise (TypeError "Invalid constructor return type")
    in
    let expected_ty = compute_case_type cj_subst ctx in
    if (trace) then (Printf.printf "Checking case %d against: " j; print_term expected_ty; print_endline "");
    check env ctx case expected_ty
  ) cases;
  match normalize env ctx p with
  | Pi (x, _, b) -> normalize env ctx (subst x t' b)
  | _ -> raise (TypeError "Motive must be a Pi type")

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
        print_string (d.name ^ ".elim");
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

let list_def a = {
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
           Lam ("x", Universe 0, Lam ("xs", list_ind, Lam ("ih", nat_ind, Constr (2, nat_def, [Var "ih"]))))],
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

let nat_elim = 
    Elim (nat_def,
          Pi ("x", nat_ind, Universe 0),
          [Inductive nat_def; Lam ("n", nat_ind, Lam ("ih", Universe 0, Var "ih"))],
          Constr (1, nat_def, []))

let test () =
  let ctx = empty_ctx () in
  let zero = Constr (1, nat_def, []) in
  let one = Constr (2, nat_def, [zero]) in
  let two = Constr (2, nat_def, [one]) in
  let add_term = App (App (plus, two), two) in
  let add_normal = normalize env ctx add_term in
  Printf.printf "Nat.Add: "; print_term add_normal; print_endline "";
  
  let list_term = App (list_length, sample_list) in
  let list_normal = normalize env ctx list_term in
  Printf.printf "List.Length: "; print_term list_normal; print_endline "";

  Printf.printf "Nat.Elim: "; print_term nat_elim; print_endline "";
  
  let succ = Lam ("n", nat_ind, Constr (2, nat_def, [Var "n"])) in
  let nat_elim =
    Elim (nat_def,
          Pi ("x", nat_ind, Universe 0),
          [Inductive nat_def; Lam ("n", nat_ind, Lam ("ih", Universe 0, Var "ih"))],
          Constr (1, nat_def, [])) in
  try
    let succ_ty = infer env ctx succ in
    Printf.printf "typeof(Nat.succ): "; print_term succ_ty; print_endline "";
    let plus_ty = infer env ctx plus in
    Printf.printf "typeof(Nat.plus): "; print_term plus_ty; print_endline "";
    let nat_elim_ty = infer env ctx nat_elim in
    Printf.printf "typeof(Nat.elim): "; print_term nat_elim_ty; print_endline ""
  with TypeError msg -> print_endline ("Type error: " ^ msg)

let _ = test ()
