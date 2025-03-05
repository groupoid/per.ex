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

**Base Cases**: Variables `Var x` are equal if names match; universes `Universe i` if levels are identical.
**Resursive Cases**: `App (f, arg)` requires equality of function and argument.
`Pi (x, a, b)` compares domains and codomains, adjusting for variable renaming via substitution.
`Inductive d` checks name, level, and parameters.
`Constr` and `Elim` compare indices, definitions, and arguments/cases.
**Fallback**: Returns false for mismatched constructors.

**Theorem**. Equality is reflexive, symmetric, and transitive modulo
α-equivalence (cf. [1], Section 2). For `Pi (x, a, b)` and `Pi (y, a', b')`,
equality holds if `a = a'` and `b[x := Var x] = b'[y := Var x]`,
ensuring capture-avoiding substitution preserves meaning.


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
