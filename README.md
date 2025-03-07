Per Martin-Löf: Calculus of Inductive Constructions
===================================================

<img src="https://per.groupoid.space/img/per.jpg" height=400>

## Abstract

This type checker, implemented in OCaml, constitutes a minimal core for a dependently-typed lambda calculus,
constrained to exclude pattern matching, let-bindings, implicit arguments, modules, namespaces, and function extensionality.
It encompasses universes, dependent products `Pi`, dependent pairs `Sigma`, identity types `Id`, and `Inductive` types with strict positivity enforcement.
Recent refinements ensure totality for user-defined lambda terms via a positive occurrence check. 
Its mathematical properties, focusing on correctness,
soundness, totality, and related attributes relevant
to formal mathematics are being analyzed.

## Intro

The type checker operates over a term syntax comprising:

* `Universe i`: Type universes with level `i ∈ ℕ`.
* `Pi (x, A, B)`: Dependent function, where `A : Universe i` and `B : Universe j` under `x : A`.
  `Lam (x, A, t)`: Lambda abstraction with totality enforced.
  `App (f, a)`: Function application.
* `Sigma (x, A, B)`: Dependent pair types.
  `Pair (a, b)`, `Fst p`, `Snd p` construction and projections.
* `Id (A, a, b)`: Identity type, with `Refl` a and `J` eliminator.
* `Inductive d`: Inductive types with intros `Constr` and eliminator `Ind`.

The typing judgment `Γ ⊢ t : T` is defined via `infer` and `check` functions,
with definitional equality `Γ ⊢ t = t'` implemented via `equal`.

## Syntax

```OCaml
type term =
  | Var of name | Universe of level
  | Pi of name * term * term | Lam of name * term * term | App of term * term
  | Sigma of name * term * term | Pair of term * term | Fst of term | Snd of term
  | Id of term * term * term | Refl of term
  | J of term * term * term * term * term * term  (* J A a b C d p *)
  | Inductive of inductive | Constr of int * inductive * term list
  | Elim of inductive * term * term list * term
```

## Semantics

### Syntactic Equality `equal env ctx t1 t2`

Structural equality of terms under an environment and context.

The function implements judgmental equality with substitution to handle bound variables,
avoiding explicit α-conversion by assuming fresh names (a simplification
over full de Bruijn indices [3]). The recursive descent ensures congruence,
but lacks normalization, making it weaker than CIC’s definitional equality,
which includes β-reduction.

* **Terminal Cases**: Variables `Var x` are equal if names match; universes `Universe i` if levels are identical.
* **Resursive Cases**: `App (f, arg)` requires equality of function and argument.
`Pi (x, a, b)` compares domains and codomains, adjusting for variable renaming via substitution.
`Inductive d` checks name, level, and parameters.
`Constr` and `Elim` compare indices, definitions, and arguments/cases.
* Default: Returns false for mismatched constructors.

**Theorem**. Equality is reflexive, symmetric, and transitive modulo
α-equivalence (cf. [1], Section 2). For `Pi (x, a, b)` and `Pi (y, a', b')`,
equality holds if `a = a'` and `b[x := Var x] = b'[y := Var x]`,
ensuring capture-avoiding substitution preserves meaning.

### Context Variables Lookup `lookup_var ctx x`

Retrieve a variable’s type from the context.
Context are the objects in the Substitutions categories.

This linear search assumes a small context, which is inefficient
for large ctx (O(n) complexity). A hash table (Second Lesson `per2.ml` of Tutorial)
could optimize this to O(1), but the simplicity suits small-scale examples. Debugging
output aids in tracing type errors, critical for dependent type
systems where context mismatches are common.

* Searches `ctx` for `(x, ty)` using `List.assoc`.
* Returns `Some ty` if found, `None` otherwise.

**Theorem**: Context lookup is well-defined under uniqueness
of names (cf. [1], Section 3). If `ctx = Γ, x : A, Δ`,
then `lookup_var ctx x = Some A`.

### Substitution Calculus `subst x s t`

Substitute term `s` for variable `x` in term `t`.
Substitutions are morphisms in Substitution categorties.

The capture-avoiding check `if x = y` prevents variable capture
but assumes distinct bound names, a simplification over full
renaming or de Bruijn indices. For Elim, substituting in the
motive and cases ensures recursive definitions remain sound,
aligning with CIC’s eliminator semantics.

* `Var`: Replaces `x` with `s`, leaves others unchanged.
* `Pi/Lam`: Skips substitution if bound variable shadows `x`, else recurses on domain and body.
* `App/Constr/Elim`: Recurses on subterms.
* `Inductive`: No substitution (assumes no free variables).

**Theorem**. Substitution preserves typing (cf. [4], Lemma 2.1).
If `Γ ⊢ t : T` and `Γ ⊢ s : A`, then `Γ ⊢ t[x := s] : T[x := s]`
under suitable conditions on x.

### Inductive Instantiation `apply_inductive d args`

Instantiate an inductive type’s constructors with parameters, used only in `infer_Elim`.

This function ensures type-level parametricity, critical for
polymorphic inductives like List A. The fold-based substitution
avoids explicit recursion, leveraging OCaml’s functional style,
but assumes args are well-typed, deferring validation to infer.

* Validates argument count against d.params.
* Substitutes each parameter into constructor types using subst_param.

**Theorem**: Parameter application preserves inductiveness (cf. [4], Section 4).
If `D` is an inductive type with parameters `P`, then `D[P]` is
well-formed with substituted constructors.

### Infer Contstructor `infer_ctor env ctx ty args`

Validate constructor arguments against its type.

This function implements the dependent application rule for constructors,
ensuring each argument satisfies the constructor’s domain type in sequence.
The recursive descent mirrors the structure of Π-types, where ty is peeled
layer by layer, and subst x arg b updates the type for the next argument.
The accumulator (args_acc) is a design choice for potential reversal,
though unused here, reflecting a forward-thinking approach to argument
order preservation. The absence of explicit universe level checks
assumes ty is well-formed from the inductive definition, delegating
such verification to infer or check_elim. Complexity is O(n) in the
number of arguments, with substitution dominating for large terms.

* Recursively matches `ty` (a Pi chain) with `args`, checking each argument and substituting.
* Returns the final type when all arguments are consumed.

**Theorem**. Constructor typing is preserved (cf. [1], Section 4, Application Rule; [8], Section 4.3).
If `ctx ⊢ c : Πx:A.B` and `ctx ⊢ a : A`, then `ctx ⊢ c a : B[x := a]`.

### Infer General Induction `infer_elim env ctx d p cases t'`

Type-check an elimination (induction) over inductive type `d`.

This function implements the dependent elimination rule of CIC,
generalizing both computation (e.g., plus : `Nat → Nat → Nat`)
and proof (e.g., `nat_elim : Πx:Nat.Type0`). The check `equal env ctx t_ty a`
ensures the motive’s domain aligns with the target, while `compute_case_type`
constructs the induction principle by injecting `App (p, var)`
as the hypothesis type for recursive occurrences, mirroring the
fixpoint-style eliminators of CIC [8]. The flexibility in result_ty
avoids hardcoding it to D, supporting higher-type motives (e.g., Type0). The O(n·m) complexity (where n is the term size and m the number of cases) arises from substitution and equality checks, with debugging prints providing a window into the type checker’s reasoning, critical for dependent type systems where errors cascade.

**Theorem**. Elimination preserves typing (cf. [8], Section 4.5; [1],
Elimination Rule for Inductive Types). For an inductive type `D`
with constructors `c_j`, if `ctx ⊢ t : D` and `ctx ⊢ P : D → Type_i`,
and each case case_j has type `Πx:A_j.P(c_j x)` where `A_j` are
the argument types of `c_j` (including recursive hypotheses), then `ctx ⊢ Elim(D, P, cases, t) : P t`.

### Infer Equality Induction `infer_J env ctx ty a b c d p`

### Type Inference `infer env ctx t`

Infer the type of term `t` in context `ctx` and environment `env`.

For `Pi` and `Lam`, universe levels ensure consistency
(e.g., `Type i : Type (i + 1)`), while `Elim` handles induction,
critical for dependent elimination. Note that lambda agrument should be typed
for easier type synthesis [13].

### Check Universes `check_universe env ctx t`

Ensure `t` is a universe, returning its level.
Infers type of `t`, expects `Universe i`.

This auxiliary enforces universe hierarchy, preventing
paradoxes (e.g., Type : Type). It relies on infer,
assuming its correctness, and throws errors for
non-universe types, aligning with ITT’s stratification.

**Theorem**: Universe checking is decidable (cf. [12]).
If `ctx ⊢ t : Universe i`, then `check_universe env ctx t = i`.

### Check `check env ctx t ty`

Check that `t` has type `ty`.

* `Lam`: Ensures the domain is a type, extends the context, and checks the body against the codomain.
* `Constr`: Infers the constructor’s type and matches it to the expected inductive type.
* `Elim`: Computes the elimination type via check_elim and verifies it equals ty.
* Default: Infers t’s type, normalizes ty, and checks equality.

The function leverages bidirectional typing: specific cases (e.g., `Lam`)
check directly, while the default case synthesizes via infer and compares
with a normalized ty, ensuring definitional equality (β-reduction).
Completeness hinges on normalize terminating (ITT’s strong normalization)
and equal capturing judgmental equality. Complexity is O(n·m) (term size n,
reduction steps m), with debugging output exposing mismatches, crucial for
dependent types where errors are subtle.

**Theorem**. Type checking is complete (cf. [1], Section III, Normalization; [8], Section 4.7).
If `ctx ⊢ t : T` in the type theory, then `check env ctx t T` succeeds,
assuming normalization and sound inference.

### Branch Evaluation `apply_case env ctx d p cases case ty args`

Apply a case branch to constructor arguments, used only in `reduce`.

This function realizes CIC’s ι-reduction for inductive eliminators [8], where
a case branch is applied to constructor arguments, including recursive hypotheses.
For Nat’s succ in plus, `ty = Πn:Nat.Nat`, `case = λk.λih.succ ih`, and `args = [n]`.
The recursive check `a = Inductive d` triggers for `n : Nat`, computing `ih = Elim(Nat, Π_:Nat.Nat, [m; λk.λih.succ ih], n)`,
ensuring `succ ih : Nat`. The nested apply_term handles multi-argument lambdas
(e.g., k and ih), avoiding explicit uncurrying, while substitution preserves
typing per CIC’s rules. Complexity is O(n·m) (term size n, recursive reduction
depth m), with debugging prints tracing hypothesis generation, critical for
verifying induction steps, e.g. `plus m (succ n) → succ (plus m n)`.

**Theorem**. Case application is sound (cf. [8],
Section 4.5, Elimination Typing; [1], Section 5, Elimination Rule).
If `case : Πx:A.P(c x)` and `args` match `A`, then `apply_case env ctx d p cases case ty args`
yields a term of type `P(c args)`.

### One-step β-reductor `reduce env ctx t`

Perform one-step β-reduction or inductive elimination.

The function implements a one-step reduction strategy combining ITT’s β-reduction [1] with CIC’s ι-reduction for inductives [8]. The `App (Lam, arg)` case directly applies substitution, while `Elim (Constr)` uses `apply_case` to handle induction, ensuring recursive calls preserve typing via the motive p. The Pi case, though unconventional, supports type-level computation, consistent with CIC’s flexibility. Complexity is O(n) for simple β-steps, but O(n·m) for Elim (term size n, case application depth m), with debugging prints tracing each step, essential for verifying reductions like `plus 2 2 → 4`.

* `App (Lam, arg)`: Substitutes arg into the lambda body (β-reduction).
* `App (Pi, arg)`: Substitutes arg into the codomain (type-level β-reduction).
* `App (f, arg)`: Reduces f, then arg if f is unchanged.
* `Elim (d, p, cases, Constr)`: Applies the appropriate case to constructor arguments, computing recursive calls (ι-reduction).
* `Elim (d, p, cases, t')`: Reduces the target `t'`.
* `Constr`: Reduces arguments.
* Default: Returns unchanged.

**Theorem**. Reduction preserves typing (cf. [1], Section III, Normalization Lemma;
[8], Section 4.6, Subject Reduction). If `ctx ⊢ t : T` and `t → t'`
via β-reduction or inductive elimination, then `ctx ⊢ t' : T`.

### Normalization `normalize env ctx t`

This function fully reduces a term t to its normal form by iteratively applying one-step reductions via reduce until no further changes occur, ensuring termination for well-typed terms.

This function implements strong normalization, a cornerstone of ITT [1] and CIC [8], where all reduction sequences terminate. The fixpoint iteration relies on reduce’s one-step reductions (β for lambdas, ι for inductives), with equal acting as the termination oracle. For `plus 2 2`, it steps through `Elim (Nat, Π_:Nat.Nat, [m; λk.λih.succ ih], succ (succ zero)) → succ (Elim(...)) → succ (succ (Elim(...))) → succ succ succ succ zero`, terminating at a constructor form. Complexity is O(n·m) (term size n, reduction steps m), where m is bounded by the term’s reduction length, guaranteed finite by CIC’s strong normalization [8, via 2]. Debugging prints are indispensable, tracing the path from `2 + 2 to 4`, aligning with CIC’s emphasis on computational transparency. The lack of explicit η-expansion or full cumulativity slightly weakens equality compared to Coq’s CIC, but termination holds.

**Theorem**. Normalization terminates (cf. [1], Section III, Normalization Theorem; [8],
Section 4.6, Strong Normalization via CoC). Every well-typed term in the system has a
ormal form under β- and ι-reductions.

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

### Corectness

* Definition: Typing rules conform to a minimal intensional dependent type theory.
* Formal Statement: For all `t, Γ, Δ`, if `infer Δ Γ t = T`, then `Γ ⊢ t : T` under rules including:
  1) `Γ ⊢ Lam (x, A, t) : Pi (x, A, B)` if `Γ ⊢ A : Universe i`, `Γ, x : A ⊢ t : B`, and `t` contains a positive occurrence of `x`;
  2) Other rules (e.g., Pi, Id, Inductive) align with standard formulations.
* Verification: eqality checking enforced by tests to confirm rule adherence.
* Status: Fully correct, with lambda totality integrated.

### Soundness

* Definition: Type preservation and logical consistency hold.
* Formal Statement: 1) If `Γ ⊢ t : T` and `reduce t = t'`, then `Γ ⊢ t' : T`;
  2) No `t` exists such that `Γ ⊢ t : Id (Universe 0, Universe 0, Universe 1)`.
* Proof: Preservation via terminating reduce; consistency via positivity and intensionality.
* Status: Sound, reinforced by rejecting non-total lambdas.

### Totality

* Definition: All well-typed constructs terminate under reduction.
* Formal Statement: 1) For `Inductive d : Universe i`, each `Constr (j, d, args)` is total;
  For `t : T` with `Ind` or `J`, `reduce t` terminates;
  For `Lam (x, A, t) : Pi (x, A, B)`, `reduce `(App (Lam (x, A, t), a))` terminates for all `a : A`;
  `normalize Δ Γ t` terminates.

### Normalization

* Definition: Reduction reaches a normal form; equality is decidable.
* Formal Statement: `equal Δ Γ t t'` terminates, reflecting normalize’s partial eta and beta reductions.
* Status: Complete within minimal scope, eta for Sigma is absent.

### Decidability

* Definition: Type checking and equality are computable.
* Formal Statement: `infer` and `check` terminate with a type or `TypeError`.
* Status: Decidable, enhanced by lambda totality check.

## Game Console

```
https://per.groupoid.space/

  🧊 MLTT/CIC Theorem Prover version 0.5 (c) 2025 Groupoїd Infinity

For help type `help`.

Starting proof for: Π(n : Nat).Nat
Goal 1:
Context: []
⊢ Π(n : Nat).Nat

1 goals remaining
>
```

## CIC

[2]. <a href="https://www.cs.unibo.it/~sacerdot/PAPERS/sadhana.pdf"> A. Asperti, W. Ricciotti, C. Sacerdoti Coen, E. Tassi. A compact kernel for the calculus of inductive constructions.</a><br>
[5]. <a href="https://inria.hal.science/hal-01094195/document">Christine Paulin-Mohring. Introduction to the Calculus of Inductive Constructions.</a><br>
[6]. <a href="https://www.cs.cmu.edu/%7Efp/papers/mfps89.pdf">Frank Pfenning, Christine Paulin-Mohring. Inductively Defined Types in the Calculus of Construction</a><br>
[7]. Asperti, A., Ricciotti, W., Coen, C. S., & Tassi, E. (2009). A compact kernel for the Calculus of Inductive Constructions.<br>
[8]. Coquand, T., & Paulin-Mohring, C. (1990). Inductively defined types.<br>
[9]. Dybjer, P. (1997). Inductive families.<br>
[11]. Harper, R., & Licata, D. (2007). Mechanizing metatheory in a logical framework.<br>
[12]. Marc Bezem, Thierry Coquand, Peter Dybjer, Martín Escardó. <a href="https://arxiv.org/pdf/2212.03284">Type Theory with Explicit Universe Polymorphism</a><br>

## MLTT

[1]. Martin-Löf, P. (1984). Intuitionistic Type Theory.<br>
[13]. Thierry Coquand. "An Algorithm for Type-Checking Dependent Types" (1996), published in Science of Computer Programming.<br>

## PTS

[3]. de Bruijn, N. G. (1972). Lambda Calculus Notation with Nameless Dummies. <br>
[4] <a href="https://core.ac.uk/download/pdf/82038778.pdf">The Calculus of Constructions</a> [Thierry Coquand, Gerard Huet]<br>
[10]. Girard, J.-Y. (1972). Interprétation fonctionnelle et élimination des coupures.<br>

## Author

Namdak Tonpa
