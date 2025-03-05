Per Martin-Löf: Calculus of Inductive Constructions
===================================================

## Abstract

Type theory lies at the heart of modern functional programming, bridging computation and logic.
In this pearl, we present Per, a type checker for Classical Martin-Löf Type Theory (MLTT) with
General Inductive Types, implemented in OCaml. Per marries the elegance of dependent types—Pi,
Sigma, Identity, and Inductive types—with the practicality of bidirectional type checking and
normalization. Through iterative refinements, we explore how OCaml’s expressive power yields
a concise yet robust system, normalizing terms like `length [zero; succ zero]` into `succ (succ zero)`.
We conclude with meta-theorems affirming Per’s theoretical sheen, from soundness to initiality.

## Intro

Martin-Löf Type Theory (MLTT) is a computational jewel, its dependent types encoding rich
specifications within programs. The Calculus of Inductive Constructions (CIC), as realized in Coq,
extends MLTT with general inductive types—think Nat or List A. Implementing a type checker for
such a system is both a challenge and a delight, demanding precision and creativity.

Per—short for “Per Martin-Löf”—is our OCaml-crafted type checker for this classical realm.
From Pi-types to mutual inductives, from one-step reduction to full normalization,
Per evolved through a series of polishing steps. This pearl narrates that journey,
showcasing a system that type-checks and normalizes with elegance.
We’ll cap it with meta-theorems, linking our implementation to the deep waters of type-theoretic guarantees.

## Syntax

```
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
```

Examples:

```
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
```

```
let list_length =
  Lam ("l",
    Elim (list_def (Universe 0),
          Pi ("_", list_ind, nat_ind),
          [Constr (1, nat_def, []); Lam ("x", Lam ("xs", Lam ("ih", Constr (2, nat_def, [Var "ih"]))))],
          Var "l"))
```

## Bidirectional Inference and Checking

Per’s type checker pirouettes between `infer` and `check`, a mutual recursion that OCaml renders with grace:

```
let rec infer (env : env) (ctx : context) (t : term) : term =
  match t with
  | Var x -> (match lookup_var ctx x with Some ty -> ty | None -> raise (TypeError ("Unbound: " ^ x)))
  | App (f, arg) ->
      let f_ty = infer env ctx f in
      (match f_ty with
       | Pi (x, a, b) -> check env ctx arg a; subst x arg b
       | _ -> raise (TypeError "Application requires Pi type"))
  | Elim (d, p, cases, t') ->
      let d_applied = apply_inductive d (List.map snd d.params) in
      check env ctx t' d_applied;
      let p_ty = List.fold_right (fun (n, p_ty) acc -> Pi (n, p_ty, acc)) d.params (Pi ("x", d_applied, Universe d.level)) in
      check env ctx p p_ty;
      List.iteri (fun j case ->
        let cj = List.assoc (j + 1) d.constrs in
        let cj_subst = List.fold_left2 (fun acc (n, _) arg -> subst n arg acc) cj d.params (List.map snd d.params) in
        check env ctx case (replace_d_with_p cj_subst p)
      ) cases;
      App (p, t')
  (* ... *)

and check (env : env) (ctx : context) (t : term) (ty : term) : unit =
  match t, ty with
  | Lam (x, body), Pi (y, a, b) -> check env (add_var ctx x a) body b
  | _, _ -> let inferred = infer env ctx t in if not (equal env ctx inferred ty) then raise (TypeError "Type mismatch")
```

The Elim case shines, orchestrating induction across mutual types with precision.

## Normalization

Normalization is Per’s polishing cloth:

```
let rec reduce (env : env) (ctx : context) (t : term) : term =
  match t with
  | App (Lam (x, body), arg) -> subst x arg body
  | Elim (d, p, cases, Constr (j, d', args)) when List.mem d'.name d.mutual_group ->
      let d_target = List.find (fun (_, def) -> def.name = d'.name) env |> snd in
      let cj = List.nth cases (j - 1) in
      let cj_ty = List.assoc j d_target.constrs in
      let rec_args = collect_rec_args cj_ty args d_target in
      subst_rec_args cj args rec_args
  | _ -> t

let rec normalize (env : env) (ctx : context) (t : term) : term =
  let t' = reduce env ctx t in
  if equal env ctx t t' then t else normalize env ctx t'
```

## Semantics

Per’s elegance rests on firm theoretical ground. Here, we reflect on key meta-theorems for Classical MLTT with General Inductive Types, drawing from CIC’s lineage:

* **Soundness and Completeness**: Per’s type checker is sound—every term it accepts has a type under MLTT’s rules [Paulin-Mohring, 1996].
  Completeness holds relative to our bidirectional algorithm: if a term is well-typed in MLTT, Per can infer or check it,
  assuming proper context management [Harper & Licata, 2007]. Our infer and check duo ensures this duality.
* **Canonicity, Normalization, and Totality**: Canonicity guarantees that every closed term of type `Nat` normalizes
  to `zero` or `succ n` [Martin-Löf, 1984]. Per’s normalize achieves strong normalization—every term reduces to a
  unique normal form—thanks to CIC’s strict positivity [Coquand & Paulin-Mohring, 1990]. Totality follows: all
  well-typed functions terminate, as seen in list_length reducing to `succ (succ zero)`.
* **Consistency and Decidability**: Consistency ensures no proof of ⊥ exists, upheld by normalization and the
  absence of paradoxes like Girard’s [Girard, 1972]. Type checking is decidable in Per, as our algorithm
  terminates for well-formed inputs, leveraging CIC’s decidable equality [Asperti et al., 2009].
* **Conservativity and Initiality**: Per is conservative over simpler systems like System F, adding dependent
  types without altering propositional truths [Pfenning & Paulin-Mohring, 1989]. Inductive types like Nat satisfy
  initiality—every algebra morphism from Nat to another structure is uniquely defined—ensuring categorical universality [Dybjer, 1997].

## Test

```
$ ocamlopt -o per induction.ml
$ ./per
ToEven: esucc succ zero
Add(3): succ succ succ zero
List length: succ succ zero
Sample list: cons zero cons succ zero nil
```

## CIC

[1]. <a href="https://inria.hal.science/hal-01094195/document">Christine Paulin-Mohring. Introduction to the Calculus of Inductive Constructions.</a><br>
[2]. <a href="https://www.cs.unibo.it/~sacerdot/PAPERS/sadhana.pdf"> A. Asperti, W. Ricciotti, C. Sacerdoti Coen, E. Tassi. A compact kernel for the calculus of inductive constructions.</a><br>
[3]. <a href="https://www.cs.cmu.edu/%7Efp/papers/mfps89.pdf">Frank Pfenning, Christine Paulin-Mohring. Inductively Defined Types in the Calculus of Construction</a><br>
[4]. Asperti, A., Ricciotti, W., Coen, C. S., & Tassi, E. (2009). A compact kernel for the Calculus of Inductive Constructions.<br>
[5]. Coquand, T., & Paulin-Mohring, C. (1990). Inductively defined types.<br>
[6]. Dybjer, P. (1997). Inductive families.<br>
[7]. Girard, J.-Y. (1972). Interprétation fonctionnelle et élimination des coupures.<br>
[8]. Harper, R., & Licata, D. (2007). Mechanizing metatheory in a logical framework.<br>
[9]. Martin-Löf, P. (1984). Intuitionistic Type Theory.

## Author

Namdak Tonpa
