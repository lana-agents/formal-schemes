/-
Bucket every theorem of the environment by its statement, **up to the orientation of a top-level
`Eq` or `Iff`**, and report the buckets that contain two or more of this project's theorems.

Run from the repository root, after a full `lake build`:

    lake env lean scripts/symm_duplicate_statement_scan.lean

It takes about 15 seconds once the environment is loaded and scans ~166k theorems.

## What this adds over an exact scan

Bucketing by the raw `Lean.Expr` type is already signature-shaped, which is the property issue 1534
asked for. But it is *exact*, so `a = b` and `b = a` land in different buckets and a statement
written backwards is invisible. That is not hypothetical: issue 1736 was filed after a human read a
companion of `AlgebraicGeometry.LocallyRingedSpace.sectionsMapOfRangeSubset` in
`FormalSchemes.AdicSectionsInvariant` and recognised it stated **backwards** — found by eye, in one
file, by luck. PR #580 deleted the backwards copy, so only the survivor is still on the tree.
The key function below orients the two sides by hash, so either spelling produces the same key.

## What it still cannot see

A probe that does not say what it misses is how a tree accumulates duplicates, so:

* **A permuted binder order.** `∀ a b, P a b` and `∀ b a, P a b` are different keys.
* **An unused-binder difference.** A hypothesis one spelling carries and the other does not puts
  the two in different buckets (the shape issue 1542 catalogued).
* **`↔` against two separate implications**, and `Eq` against `Iff` at `Prop`.
* **A statement pinned at a special argument** — the specialisation `S = R` of a general lemma is
  not a type equality, so nothing here buckets them together (the shape issue 1563 catalogued, and
  the reason issue 1585 turned on a Mathlib lemma no scan of this kind could have found).
* **Folded against unfolded.** If one spelling states `HasAffineChartAt X x` and the other states
  it with the `def` unfolded, the types differ; `scripts/signature_scan.lean` marks that class with
  its fourth column and does not normalise it either.
* **A symmetry below the top level.** The key orients the conclusion only. An `Eq` inside a
  hypothesis, or under a binder inside the conclusion, is left alone.

## What it *over*-reports, and why that is deliberate

`Lean.Expr`'s `BEq` and `Hashable` are alpha-equivalence: they ignore binder **names** and binder
**annotations**. Verified rather than assumed — building two `Lean.Expr.forallE` nodes over one
body and comparing them, a pair differing only in `Lean.BinderInfo` and a pair differing only in
the binder name both come out equal. So a pair differing *only* in explicit-versus-implicit lands
in one bucket. That is the right default — a genuine duplicate is not made distinct by an argument
being implicit — but it means the pairs Mathlib's naming convention asks for are reported too.
`Ideal.IsCofinal.refl` and `Ideal.IsCofinal.rfl` in `FormalSchemes.CofinalIdeal` are exactly such a
pair, and they are **correct as they stand**. Rather than tighten the key and lose recall, each
group is annotated:

* `[BINDER-DIFF]` — the members do **not** share a binder-annotation spine, so the group may be a
  convention pair of that kind rather than a duplicate. **Look before deleting.**
* no annotation — the members agree on binder annotations too, so any difference between them is
  in the proof only.

## Do not "canonicalise" by rebuilding the whole expression

The key rebuilds only the `∀`-spine and the outermost relation node; every binder *type* and
both sides of the relation are passed through by reference. That is deliberate. A plain recursive
rewrite of the entire `Lean.Expr` turns a heavily shared DAG into a tree and does not finish on this
library: `scripts/signature_scan.lean` records a run that took 20 minutes and was killed at 10 GB
after exactly that change (issue 1534).
-/
import FormalSchemes

open Lean Meta Elab

/-- Is `n` an internal / auto-generated name we should ignore? -/
def isNoise (n : Name) : Bool :=
  n.isInternal ||
  (n.components.any fun c =>
    let s := c.toString
    s.startsWith "_" || s == "proof" || s == "eq_def" || s == "eq_1" ||
    s == "casesOn" || s == "recOn" || s == "below" || s == "brecOn" ||
    s == "noConfusion" || s == "noConfusionType" || s == "sizeOf_spec" ||
    s == "injEq" || s == "ndrec" || s == "rec" || s == "ofNat" || s == "match_1")

/-- Was `n` declared by this project, rather than by Mathlib or core? -/
def isProject (env : Environment) (n : Name) : Bool :=
  match env.getModuleFor? n with
  | some m => (`FormalSchemes).isPrefixOf m || m == `FormalSchemes
  | none => false

/-- The module `n` was declared in, for the report. -/
def modOf (env : Environment) (n : Name) : Name :=
  (env.getModuleFor? n).getD Name.anonymous

/-- Canonicalise a statement up to `Eq.symm`/`Iff.symm` under the leading binders. Only the spine
and the outermost relation are rebuilt; see the note on sharing at the top of this file. -/
partial def symmKey (e : Expr) : Expr :=
  match e with
  | .forallE nm t b bi => .forallE nm t (symmKey b) bi
  | _ =>
    match e.getAppFnArgs with
    | (``Eq, #[α, a, b]) =>
      if toString (hash a) ≤ toString (hash b) then mkAppN (.const ``Eq [Level.zero]) #[α, a, b]
      else mkAppN (.const ``Eq [Level.zero]) #[α, b, a]
    | (``Iff, #[a, b]) =>
      if toString (hash a) ≤ toString (hash b) then mkAppN (.const ``Iff []) #[a, b]
      else mkAppN (.const ``Iff []) #[b, a]
    | _ => e

/-- The binder annotations of the leading `∀`-spine, which `Lean.Expr`'s `BEq` discards. -/
partial def binderSpine (e : Expr) : List BinderInfo :=
  match e with
  | .forallE _ _ b bi => bi :: binderSpine b
  | _ => []

run_cmd Elab.Command.liftTermElabM do
  let env ← getEnv
  let mut m : Std.HashMap Expr (Array Name) := {}
  let mut nThm := 0
  for (n, ci) in env.constants.toList do
    match ci with
    | .thmInfo v =>
      if isNoise n then continue
      nThm := nThm + 1
      let k := symmKey v.type
      m := m.insert k ((m.getD k #[]).push n)
    | _ => pure ()
  IO.println s!"scanned {nThm} theorems (symm-normalised)"
  let mut projDup := 0
  let mut binderDiff := 0
  let mut mathlibDup := 0
  for (_, names) in m.toList do
    if names.size < 2 then continue
    let proj := names.filter (isProject env)
    if proj.isEmpty then continue
    let others := names.filter (fun n => !(isProject env n))
    let spines := names.toList.filterMap fun n => (env.find? n).map fun ci => binderSpine ci.type
    let tag := match spines with
      | [] => ""
      | s :: rest => if rest.all (· == s) then "" else " [BINDER-DIFF]"
    if others.isEmpty then
      if proj.size ≥ 2 then
        projDup := projDup + 1
        if tag != "" then binderDiff := binderDiff + 1
        IO.println s!"[PROJ-DUP]{tag} {proj.map (fun n => s!"{n} ({modOf env n})")}"
    else
      mathlibDup := mathlibDup + 1
      IO.println s!"[MATHLIB-DUP]{tag} project: {proj.map (fun n => s!"{n} ({modOf env n})")}  \
        ||  upstream: {others.toList.take 3}"
  IO.println s!"DONE  project-internal: {projDup} (binder-annotation-only: {binderDiff})   \
    project-vs-upstream: {mathlibDup}"
