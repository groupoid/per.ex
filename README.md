Per Martin-Löf: Calculus of Inductive Constructions
===================================================

## Abstract

This article presents an implementation of a dependently-typed
lambda calculus with inductive types in OCaml, drawing inspiration
from Martin-Löf’s Intuitionistic Type Theory (ITT) [1] and the
Calculus of Inductive Constructions (CIC) [2]. The system supports
type inference, type checking, reduction, and normalization, with
a focus on natural numbers (Nat) and lists (List) as example
inductive types. Below, we provide a detailed teardown of each
core function, grounded in formal theorems and referencing
seminal works, followed by technical insights into their design
and implementation.

The implementation realizes a fragment of CIC,
balancing expressiveness and decidability. The type system
enforces universe consistency (via `check_universe`) and dependent
elimination (via `check_elim`), ensuring soundness as per Martin-Löf’s
formation, introduction, and elimination rules [1]. Substitution and
reduction handle α-equivalence implicitly, trading off formal rigor
for simplicity, while `infer` and `check` form a bidirectional core,
optimizing type inference (O(n) in term size, assuming small contexts).
Inductive types, inspired by Coquand’s work [2], support recursion
through `Elim`, with apply_case encoding the induction principle via recursive calls.
The lack of full cumulativity (e.g., `Type i <: Type (i + 1)`)
and weak equality (no η-expansion) limits expressiveness compared
to Coq, but the system proves `Nat.plus : Nat -> Nat -> Nat` and
`Nat.elim : Π(x:Nat).Type0`, demonstrating practical utility.
Debugging prints, while verbose, expose the system’s reasoning,
aligning with Pierce’s emphasis on transparency in type checkers [4].

## Intro

The system defines terms `term`, inductive types `inductive`,
environments `env`, and contexts `context` to represent
a dependent type theory. These structures align with the
formal syntax of CIC, as described by Coquand and Huet [2].

### Types

* `term`: Includes variables, universes, Pi types, lambda abstractions,
  applications, Sigma types, pairs, identity types, inductive types,
  constructors, and eliminators.
* `inductive`: Captures parameterized inductive definitions with constructors and mutual recursion groups.
* `env` and `context`: Store global inductive definitions and local variable bindings, respectively.

**Technical Insight**: The term type encodes a pure type system (PTS)
extended with inductive constructs, supporting full
dependent types (e.g., Pi and Sigma). The inductive record mirrors
CIC’s inductive schemas, allowing parameterized types like List A,
while mutual_group hints at potential mutual recursion, though not fully exploited here.

## Syntax

```
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
```

## Semantics

### Syntactic Equality `equal env ctx t1 t2`

Structural equality of terms under an environment and context.

The function implements judgmental equality with substitution to handle bound variables,
avoiding explicit α-conversion by assuming fresh names (a simplification
over full de Bruijn indices [3]). The recursive descent ensures congruence,
but lacks normalization, making it weaker than CIC’s definitional equality,
which includes β-reduction.

* **Base Cases**: Variables `Var x` are equal if names match; universes `Universe i` if levels are identical.
* **Resursive Cases**: `App (f, arg)` requires equality of function and argument.
`Pi (x, a, b)` compares domains and codomains, adjusting for variable renaming via substitution.
`Inductive d` checks name, level, and parameters.
`Constr` and `Elim` compare indices, definitions, and arguments/cases.
* **Fallback**: Returns false for mismatched constructors.

**Theorem**. Equality is reflexive, symmetric, and transitive modulo
α-equivalence (cf. [1], Section 2). For `Pi (x, a, b)` and `Pi (y, a', b')`,
equality holds if `a = a'` and `b[x := Var x] = b'[y := Var x]`,
ensuring capture-avoiding substitution preserves meaning.

### Context Variables Lookup `lookup_var ctx x`

Retrieve a variable’s type from the context.

This linear search assumes a small context, which is inefficient
for large ctx (O(n) complexity). A hash table (Second Lesson `per2.ml` of Tutorial)
could optimize this to O(1), but the simplicity suits small-scale examples. Debugging
output aids in tracing type errors, critical for dependent type
systems where context mismatches are common.

* Searches `ctx` for `(x, ty)` using `List.assoc`.
* Returns `Some ty` if found, `None` otherwise.
* Includes debugging output for transparency.

**Theorem**: Context lookup is well-defined under uniqueness
of names (cf. [1], Section 3). If `ctx = Γ, x : A, Δ`,
then `lookup_var ctx x = Some A`.

### Substitution Calculus `subst x s t`

Substitute term `s` for variable `x` in term `t`.

The capture-avoiding check `if x = y` prevents variable capture
but assumes distinct bound names, a simplification over full
renaming or de Bruijn indices. For Elim, substituting in the
motive and cases ensures recursive definitions remain sound,
aligning with CIC’s eliminator semantics.

* `Var`: Replaces `x` with `s`, leaves others unchanged.
* `Pi/Lam`: Skips substitution if bound variable shadows `x`, else recurses on domain and body.
* `App/Constr/Elim`: Recurses on subterms.
* `Inductive`: No substitution (assumes no free variables).

**Theorem**. Substitution preserves typing (cf. [2], Lemma 2.1).
If `Γ ⊢ t : T` and `Γ ⊢ s : A`, then `Γ ⊢ t[x := s] : T[x := s]`
under suitable conditions on x.

### Inductive Instantiation `apply_inductive d args`

Instantiate an inductive type’s constructors with parameters.

This function ensures type-level parametricity, critical for
polymorphic inductives like List A. The fold-based substitution
avoids explicit recursion, leveraging OCaml’s functional style,
but assumes args are well-typed, deferring validation to infer.

* Validates argument count against d.params.
* Substitutes each parameter into constructor types using subst_param.

**Theorem**: Parameter application preserves inductiveness (cf. [2], Section 4).
If `D` is an inductive type with parameters `P`, then `D[P]` is
well-formed with substituted constructors.

### Type Inference `infer env ctx t`

Infer the type of term `t` in context `ctx` and environment `env`.

For `Pi` and `Lam`, universe levels ensure consistency
(e.g., `Type i : Type (i + 1)`), while `Elim` handles induction,
critical for dependent elimination. Debugging prints expose
inference steps, vital for diagnosing failures in complex terms.

### Check Universes `check_universe env ctx t`

### Check Ctor `check_constructor_args env ctx ty args`

### Check General Induction `env ctx d p cases t'`

### Check `check env ctx t ty`

### Granular Reductor `reduce env ctx t`

### Case Branch `apply_case env ctx d p cases case ty args`

### Normalization `normalize env ctx t`



## Properties

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

[1]. Martin-Löf, P. (1984). Intuitionistic Type Theory.
[2]. <a href="https://www.cs.unibo.it/~sacerdot/PAPERS/sadhana.pdf"> A. Asperti, W. Ricciotti, C. Sacerdoti Coen, E. Tassi. A compact kernel for the calculus of inductive constructions.</a><br>
[3]. de Bruijn, N. G. (1972). Lambda Calculus Notation with Nameless Dummies. Indagationes Mathematicae, 34(5), 381-392.
[4]. <a href="https://inria.hal.science/hal-01094195/document">Christine Paulin-Mohring. Introduction to the Calculus of Inductive Constructions.</a><br>
[5]. <a href="https://www.cs.cmu.edu/%7Efp/papers/mfps89.pdf">Frank Pfenning, Christine Paulin-Mohring. Inductively Defined Types in the Calculus of Construction</a><br>
[6]. Asperti, A., Ricciotti, W., Coen, C. S., & Tassi, E. (2009). A compact kernel for the Calculus of Inductive Constructions.<br>
[7]. Coquand, T., & Paulin-Mohring, C. (1990). Inductively defined types.<br>
[8]. Dybjer, P. (1997). Inductive families.<br>
[9]. Girard, J.-Y. (1972). Interprétation fonctionnelle et élimination des coupures.<br>
[10]. Harper, R., & Licata, D. (2007). Mechanizing metatheory in a logical framework.<br>

## Author

Namdak Tonpa
