import FormalSchemes.AwayBaseChangeTopFiniteType
import FormalSchemes.AwayCompletionAlgHomBasicOpen
import FormalSchemes.AwayCompletionUniversal
import FormalSchemes.RefinedOverlapRestrict

set_option linter.style.header false

/-!
# The refined overlap's cross-chart transition

Refining an arbitrary affine chart family of a formal scheme by basic opens — the construction
statement (A) of EGA I §10.15 waits on, issue 2148 — indexes the refined charts by pairs *⟨i, h⟩*
with `h : A_i`, and at a cross-chart refined pair *⟨i, h⟩*, *⟨j, h'⟩* it needs an `R`-algebra
equivalence

```
A_i{1/(h · e_ij)}  ≃ₐ[R]  A_j{1/(h' · e_ji)}
```

between the two refined presentations of one overlap. Here `e_ij` is
`FormalSpectrum.refinedOverlapElt` (`FormalSchemes.RefinedOverlapRestrict`) at that pair and `e_ji`
is the same element with the two charts and the two refining elements swapped, and the equivalence
has to sit over the coarse transition `τ_ij : A_i{1/g_ij} ≃ₐ[R] A_j{1/g_ji}` the unrefined datum
already carries. `FormalSchemes.RefinedOverlapRestrict`'s `## What is **not** proved here` named
this as the one thing that file's legs stop short of. It is
`FormalSpectrum.refinedOverlapTransition` below.

**It is a composite of statements this tree already has, and it is not a descent statement.** That
distinction is the whole reason this module is short: the span

```
A_i{1/g_ij} ⟶ A_i{1/(h · e_ij)}        A_j{1/g_ji} ⟶ A_j{1/(h' · e_ji)}
```

of `FormalSpectrum.refinedOverlapLeg` joined at the top by *τ_ij* invites reading the bottom
equivalence as descent along the two legs, and nothing here does that. The route goes *up* instead:
each refined presentation is recognised as a basic open of its own coarse chart, *τ_ij* is
transported to that basic open, and the two presentations are matched by the element that cuts them
out.

## Main results

* `FormalSpectrum.basicOpen_awayCompletionAlgEquiv_mul_refinedOverlapElt`: the two refined
  presentations cut out corresponding opens — inside `Spf (A_j{1/g_ji})`, the *τ_ij*-image of the
  refined overlap read in chart *i* is the refined overlap read in chart *j*. This is the
  hypothesis the third step of the route below asks for, and it is the only statement here with
  content.
* `FormalSpectrum.refinedOverlapTransition`: the equivalence itself, as the composite of four
  declarations and two bookkeeping steps.

## The route, in the order the term takes it

1. `FormalSpectrum.awayCompletionNestedAlgEquivOfLe` (`FormalSchemes.AwayCompletionUniversal`)
   reads `A_i{1/(h · e_ij)}` as a completed localization of the coarse chart `A_i{1/g_ij}`, at the
   structural image of `h · e_ij`. It is the `basicOpen`-keyed form, so all it wants is the
   containment `D(h · e_ij) ≤ D(g_ij)`, which is
   `FormalSpectrum.basicOpen_mul_le_of_basicOpen_le` at
   `FormalSpectrum.basicOpen_refinedOverlapElt_le`.
2. `FormalSpectrum.awayCompletionAlgEquivOfBase` (`FormalSchemes.AwayBaseChangeTopFiniteType`,
   issue 2192) transports *τ_ij* to those localizations: an `R`-algebra equivalence `σ : S ≃ₐ[R] T`
   with `σ u = v` gives `S{1/u} ≃ₐ[R] T{1/v}`. At `u := ĥ · ê_ij` it is applied with `v` left to
   unification and `huv := rfl`, so no transport lemma is named at this step.
3. `FormalSpectrum.awayCompletionCongrBasicOpenAlg` (`FormalSchemes.AwayCompletionRestrictUnique`)
   then replaces that presenting element by the one chart *j* indexes, which is exactly
   `FormalSpectrum.basicOpen_awayCompletionAlgEquiv_mul_refinedOverlapElt` above.
4. Step 1 again on the *j* side, taken backwards.

## The two bookkeeping steps the four declarations do not name, and they fail differently

This is the only non-obvious thing on the route, and both halves are stated here because a paste of
the four alone hits them in order.

`FormalSpectrum.awayCompletionCongrBasicOpenAlg` is an equivalence over the base of *its own* ideal
rather than over `R`, so it wants `AlgEquiv.restrictScalars`; a paste that omits it does **not**
report a scalar mismatch but exhausts the default heartbeats at `isDefEq`, the elaborator having
been asked whether `R` and that completion are the same scalar ring and walking the completion
tower to answer. **A timeout there is that omission and not an obstruction** — raising the budget
to a million heartbeats only buys a longer one. The second step is that equivalence's hypothesis,
which is asked for at `I.map (algebraMap R _)` where `FormalSchemes.RefinedOverlapRestrict`'s
statements are at `FormalSpectrum.awayCompletionIdeal`;
`FormalSpectrum.map_algebraMap_awayCompletion_eq` (`FormalSchemes.BasicOpenChart`) is the bridge
and it is one `rw`, and omitting *that* one does fail with a type error in seconds, naming both
spellings of the ideal. The same pair of conventions is what
`FormalSchemes.RefinedOverlapRestrict`'s transport paragraph prices one step earlier.

## Placement

A leaf over `FormalSchemes.RefinedOverlapRestrict`, `FormalSchemes.AwayCompletionAlgHomBasicOpen`,
`FormalSchemes.AwayBaseChangeTopFiniteType` and `FormalSchemes.AwayCompletionUniversal`: this
file's forward closure is **64** project modules besides itself (65 counted with itself), and its
reverse closure is **0**.

**A new module is forced, and that was measured rather than argued.** No module of this tree
reaches all four of the above — none reaches even three of the four — so the *put it in a file that
already imports enough* option does not exist, and the alternative is an import into an existing
file, which is the expensive direction. `FormalSchemes.RefinedOverlapRestrict` is the closest
candidate and reaches **41**, and it is missing three of the four: the edges to
`FormalSchemes.AwayCompletionAlgHomBasicOpen`, `FormalSchemes.AwayBaseChangeTopFiniteType` and
`FormalSchemes.AwayCompletionUniversal` cost **+6**, **+15** and **+16** modules there, and every
consumer that file ever gains would inherit them.

**One of the four imports is free in closure terms and is kept anyway.**
`FormalSchemes.AwayBaseChangeTopFiniteType` lies inside `FormalSchemes.AwayCompletionUniversal`'s
forward closure of **55** — that module imports it on its first line — so dropping the import line
would leave the 64 above unchanged. It is kept because
`FormalSpectrum.awayCompletionAlgEquivOfBase` is used here directly, which is this tree's practice
and not a departure from it: **140** of the **586** modules under `FormalSchemes/` carry an import
some other import of the same file already reaches, this one included. Counting only what each
import brings that no other of the four reaches, the split is **6** for
`FormalSchemes.AwayCompletionAlgHomBasicOpen`, **2** for
`FormalSchemes.RefinedOverlapRestrict`, **1** for `FormalSchemes.AwayCompletionUniversal` and
**0** for `FormalSchemes.AwayBaseChangeTopFiniteType`; the remaining 55 of the 64 are reached by
more than one of them.

**What the module costs is the figure sweep, not the build.** Adding any module under
`FormalSchemes/` falsifies every absolute *reverse*-closure figure quoted about anything it imports
— CONTRIBUTING.md's *What adding a module costs* is the standing account — and here that is **37**
numerals in **17** files, every one of them a `+1`. Editing those 17 re-elaborates **538** of the
586 modules, and the concentration is the same one CONTRIBUTING.md records: the reverse closure of
`FormalSchemes.StructureSheaf` is **529**, and dropping that one file from the 17 takes the sweep's
rebuild to **80**. Two of
the 37 are not renumberings: `FormalSchemes/RefinedOverlapRestrict.lean` and
`FormalSchemes/AwayCompletionAlgHomBasicOpen.lean` each state that they are **leaves**, and this
module is their first consumer, so both `## Placement` paragraphs are rewritten rather than
renumbered — in the first case because the ratio it declines a move on was argued from a *single
call site*, and this module is the second.

This paragraph's counts are measurements of the diff that added this file, at the base it was taken
at; they are not standing claims about any later tree and nothing re-runs them. Re-measure with
`scripts/closure_audit.py --tree`, and price any fifth import with `--edge` before writing a word
about it.

## What is *not* proved here

**The transition's symmetry law.** `FormalSpectrum.refinedOverlapTransition` at the swapped pair is
expected to be the inverse of this one, and that is not stated here. **It is well-typed**, which is
the first thing to know and not obvious: the swapped pair presents its *i*-side element at
`τ.symm.symm` rather than at `τ`, and those agree by `rfl` — checked, at the completions this
statement lives at, not assumed from `AlgEquiv.symm_symm`.

**What it is not is a bookkeeping step.** Both sides are composites of four equivalences through
different completions, and every pointwise route to the identity is a heartbeat timeout at the
default budget: measured with `lake env lean` outside the tree, `rfl` times out at `isDefEq`,
`AlgEquiv.ext fun _ => rfl` at `isDefEq`, and `AlgEquiv.symm_bijective.injective (by rfl)` at
`whnf`. That is the species this cluster has recorded repeatedly at the completed-localization
layer, and more heartbeats are not the answer to it. The statement wants a uniqueness argument
instead, and the general one this file reaches is
`FormalSpectrum.awayCompletion_hom_ext'` (`FormalSchemes.AwayCompletionRestrictUnique`) — two ring
maps out of a completed localization into any adically complete ring that agree after
`FormalSpectrum.awayCompletionHom` are equal — which is the shape to start from rather than a route
that is known to work, since nothing here has run it.

**The cocycle condition on a triple of charts**, and **nothing about `σ`, the triple overlap or the
refined datum's laws**. Those are issue 2148's goal 2 and are scoped elsewhere; this module is the
cross-chart transition and nothing else.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.13, §10.15.
-/

noncomputable section

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {Ai Aj : Type u} [CommRing Ai] [CommRing Aj] [Algebra R Ai] [Algebra R Aj]

/-- **The two refined presentations of one overlap correspond under the coarse transition.** Inside
`Spf (A_j{1/g_ji})`, the *τ_ij*-image of the open cut out by the *i*-side refined element
`h · e_ij` is the open cut out by the *j*-side one, `h' · e_ji`.

This is the hypothesis `FormalSpectrum.awayCompletionCongrBasicOpenAlg`
(`FormalSchemes.AwayCompletionRestrictUnique`) asks for in the third step of
`FormalSpectrum.refinedOverlapTransition`, and it is the only statement in this module with
content.

**Nothing topological happens here.** That was spent in
`FormalSpectrum.basicOpen_awayCompletionHom_mul_refinedOverlapElt`
(`FormalSchemes.RefinedOverlapRestrict`), which reads either refined presentation inside its *own*
coarse chart as the meet of the two refining elements. Both sides below are that statement — once
at *⟨i, h⟩*, *⟨j, h'⟩* and once at the swapped pair, where it arrives with a `τ.symm.symm` that is
`τ` by `AlgEquiv.symm_symm` — so what is left is to carry a meet across *τ_ij*, which is
`FormalSpectrum.basicOpen_awayCompletionAlgEquiv_eq_iff`
(`FormalSchemes.AwayCompletionAlgHomBasicOpen`, issue 2193) in the four-rewrite idiom that module's
docstring prescribes for exactly this shape. **One step beyond the idiom is needed and it is worth
naming**: the *j*-side meet has one factor already in the target chart, so
`AlgEquiv.apply_symm_apply` has to put it back under *τ_ij* before the two factors can be
multiplied under one `map_mul`. The two meets then differ by `inf_comm`.

The statement is asymmetric in appearance only. `e_ij` and `e_ji` are both
`FormalSpectrum.refinedOverlapElt`, at the two orders of the same pair, and each is pinned only up
to an equality of basic opens — which is why the elements the refined datum indexes by, `h`, `h'`
and *τ_ij*, are the ones written on both sides, and `e_ij`, `e_ji` appear only inside the
products. -/
theorem basicOpen_awayCompletionAlgEquiv_mul_refinedOverlapElt (hI : I.FG) (gij : Ai) (gji : Aj)
    (τ : awayCompletion (I.map (algebraMap R Ai)) gij ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) gji)
    (h : Ai) (h' : Aj) :
    basicOpen (awayCompletionIdeal (I.map (algebraMap R Aj)) gji)
        (τ (awayCompletionHom (I.map (algebraMap R Ai)) gij
          (h * refinedOverlapElt I hI gij gji τ h h')))
      = basicOpen (awayCompletionIdeal (I.map (algebraMap R Aj)) gji)
          (awayCompletionHom (I.map (algebraMap R Aj)) gji
            (h' * refinedOverlapElt I hI gji gij τ.symm h' h)) := by
  rw [basicOpen_awayCompletionHom_mul_refinedOverlapElt I hI gji gij τ.symm h' h,
    AlgEquiv.symm_symm, ← τ.apply_symm_apply (awayCompletionHom
      (I.map (algebraMap R Aj)) gji h'), ← basicOpen_mul, ← map_mul,
    basicOpen_awayCompletionAlgEquiv_eq_iff I gij gji τ, basicOpen_mul,
    basicOpen_awayCompletionHom_mul_refinedOverlapElt I hI gij gji τ h h']
  exact inf_comm _ _

/-- **The transition of the refined chart family at a cross-chart refined pair.** For chart
algebras `A_i`, `A_j` over `R`, coarse overlap elements `g_ij : A_i`, `g_ji : A_j` joined by an
`R`-algebra equivalence *τ_ij* of their completed localizations, and refining elements `h : A_i`,
`h' : A_j`, the `R`-algebra equivalence

```
A_i{1/(h · e_ij)}  ≃ₐ[R]  A_j{1/(h' · e_ji)}
```

between the two refined presentations of the refined overlap, with `e_ij`, `e_ji` the two orders of
`FormalSpectrum.refinedOverlapElt` (`FormalSchemes.RefinedOverlapRestrict`).

**This is a composite of four declarations already on the tree, and not a descent statement.** The
module docstring lists the four in the order the term takes them and states the two bookkeeping
steps they do not name; the one thing worth repeating here is that a paste of the four which drops
`AlgEquiv.restrictScalars` at the third step does not report a scalar mismatch but exhausts the
default heartbeats at `isDefEq`, so **a timeout there is that omission and not an obstruction**.

No hypothesis beyond `I.FG` is needed, and in particular nothing is assumed about *τ_ij* beyond its
being an `R`-algebra equivalence of the two coarse overlap algebras: the refined overlap element is
a function of it, so the cross-chart data are pinned by the coarse datum alone. -/
def refinedOverlapTransition (hI : I.FG) (gij : Ai) (gji : Aj)
    (τ : awayCompletion (I.map (algebraMap R Ai)) gij ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) gji)
    (h : Ai) (h' : Aj) :
    awayCompletion (I.map (algebraMap R Ai)) (h * refinedOverlapElt I hI gij gji τ h h') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj))
        (h' * refinedOverlapElt I hI gji gij τ.symm h' h) :=
  ((awayCompletionNestedAlgEquivOfLe I hI gij _
        (basicOpen_mul_le_of_basicOpen_le _ h
          (basicOpen_refinedOverlapElt_le I hI gij gji τ h h'))).trans
      (awayCompletionAlgEquivOfBase I hI τ rfl)).trans
    (((awayCompletionCongrBasicOpenAlg _ _ _ (hI.map _) (by
          rw [map_algebraMap_awayCompletion_eq]
          exact basicOpen_awayCompletionAlgEquiv_mul_refinedOverlapElt I hI gij gji τ h h'
          )).restrictScalars R).trans
      (awayCompletionNestedAlgEquivOfLe I hI gji _
        (basicOpen_mul_le_of_basicOpen_le _ h'
          (basicOpen_refinedOverlapElt_le I hI gji gij τ.symm h' h))).symm)

end FormalSpectrum

end
