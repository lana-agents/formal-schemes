import FormalSchemes.AwayCompletionRestrictUnique
import FormalSchemes.BasicOpenChartImage

set_option linter.style.header false

/-!
# The refined overlap's leg out of the coarse one

Refining an arbitrary affine chart family of a formal scheme by basic opens — the construction
statement (A) of EGA I §10.15 waits on, issue 2148 — indexes the refined charts by pairs *⟨i, h⟩*
with `h : A_i`, and needs, at a cross-chart refined pair *⟨i, h⟩*, *⟨j, h'⟩*, an `R`-algebra
transition between the two presentations of the refined overlap. This file supplies the **legs** of
that transition: the maps out of the *coarse* overlap algebras `A_i{1/g_ij}` and `A_j{1/g_ji}` into
the refined ones. Only one leg is declared below and that is not an omission:
`FormalSpectrum.exists_refined_overlap_element` is symmetric in its two charts, so the *j*-side
leg is `FormalSpectrum.refinedOverlapLeg` itself, at the swapped data
*(gji, gij, τ.symm, h', h)*.

## What was thought to be missing, and is not

`FormalSpectrum.exists_refined_overlap_element` (`FormalSchemes.BasicOpenChartImage`) produces the
element `e : A_i` cutting the refined overlap out of chart *i*, and issue 2148's thread then asked
for a **divisibility or an `IsUnit`** so that `CompletedTensorAwayInterchange.awayCongrHom`
(`FormalSchemes.AwayCompletionCongrEquiv`) could be applied to it, and recorded the cost of that
step as unpriced. It is unpriced because it is not the step:
`CompletedTensorAwayInterchange.awayCongrHom` wants
`IsUnit (algebraMap A (Localization.Away y) x)`, a statement in the **uncompleted** localization,
and that is exactly what an inclusion of basic opens of `Spf A` does *not* give —
`FormalSchemes.AwayCompletionRestrict` opens by saying so. The separation is strict and it is
cheap to see: at `A = ℤ`, `I = (2)`, `x = 3`, `y = 5` the formal spectrum is the single point
`Spec 𝔽₂`, so `D(5) ≤ D(3)` holds (both residues are the unit of `ℤ ⧸ (2)`), while `3` is not a
unit of `ℤ[1/5]` — `ℤ[1/5] → ZMod 3` exists and kills it. That witness is elaborated on issue
2148's thread and is not committed here.

The map keyed on the containment itself already exists, in that same module:
`FormalSpectrum.awayCompletionRestrict` takes `D(g) ≤ D(f)` and nothing else, and the containment
is free from the element's own construction —
`FormalSpectrum.basicOpen_le_of_image_basicOpenChartBase_eq`, now the second conjunct of
`exists_refined_overlap_element`: *D(e)* is an image under the chart at *g_ij*, whose range is
*D(g_ij)*. So the leg costs one `le_trans` through `FormalSpectrum.basicOpen_mul`, and the price
of the whole step is this file.

## Main results

* `FormalSpectrum.basicOpen_mul_le_of_basicOpen_le`: `D(e) ≤ D(g)` gives `D(h · e) ≤ D(g)`, the
  containment the refined presentation `A_i{1/(h · e)}` needs.
* `FormalSpectrum.refinedOverlapRestrict`: the leg
  `A_i{1/g_ij} →ₐ[R] A_i{1/(h · e)}` itself, an `R`-algebra map over the chart algebra's own base
  by `AlgHom.restrictScalars`.
* `FormalSpectrum.coe_refinedOverlapRestrict`: it is `FormalSpectrum.awayCompletionRestrict`, so
  the rigidity lemma `FormalSpectrum.awayCompletionRestrict_unique`
  (`FormalSchemes.AwayCompletionRestrictUnique`) pins it and no new object has been introduced.
* `FormalSpectrum.refinedOverlapElt` and its two properties: the refined overlap element as
  **data**, since the refined chart family needs the element and not only its existence.
* `FormalSpectrum.refinedOverlapLeg`: the leg at a cross-chart refined pair, the two put together.
  The element and the map travel in one definition on purpose — `e` is pinned only up to an
  equality of basic opens, so a map chosen independently of it is a map into a different ring.

`A_i{1/(h · e)}` is the right ambient presentation of the refined overlap rather than
`A_i{1/h}{1/ê}`: the two are identified by `FormalSpectrum.awayCompletionCongrBasicOpenAlg` at
`D(ê) = D(ĥ · ê)` inside `Spf (A_i{1/h})` followed by
`FormalSpectrum.awayCompletionNestedAlgEquiv` (`FormalSchemes.AwayCompletionNested`) at
`f := h`, `g := h · e`, whose `IsUnit` hypothesis is the divisibility `h ∣ h · e` and so is
available. That identification is *not* drawn here — this file is about the leg alone.

## What is **not** proved here

**The transition itself.** What issue 2148's refined datum needs at a cross-chart pair is an
`R`-algebra isomorphism

```
A_i{1/(h · e)}  ≃ₐ[R]  A_j{1/(h' · e')}
```

and what is below is only the pair of legs `A_i{1/g_ij} ⟶ A_i{1/(h · e)}` and
`A_j{1/g_ji} ⟶ A_j{1/(h' · e')}` out of the two coarse overlap algebras, which the coarse
transition `τ_ij : A_i{1/g_ij} ≃ₐ[R] A_j{1/g_ji}` joins at the *top*. Producing the bottom
isomorphism from that span is a **descent** statement, and it is open.

**What it was waiting on is no longer missing.**
`FormalSpectrum.awayCompletionNestedAlgEquiv` (`FormalSchemes.AwayCompletionNested`) recognises
`A{1/g}` as a completed localization of the chart algebra `A{1/f}`,

```
A{1/g} ≃ₐ[R] (A{1/f}){1/ĝ},
```

which is precisely the leg's target read from inside the source; its hypothesis, however, is
`IsUnit (algebraMap A (Localization.Away g) f)` — the **uncompleted** unit statement, strictly
stronger than the containment `D(h · e) ≤ D(g_ij)` the leg is built from, and the same thing
`CompletedTensorAwayInterchange.awayCongrHom` asks for above. The `basicOpen`-keyed form of it is
now `FormalSpectrum.awayCompletionNestedAlgEquivOfLe` (`FormalSchemes.AwayCompletionUniversal`),
proved from the universal property of a completed localization instead of from the localization
transitivity that the stronger hypothesis exists to feed. So what stands between these legs and
the transition is the transport of *τ_ij* along it and its *j*-side twin, together with the check
that the two presentations it lands on are the ones the refined datum indexes — `AlgEquiv`
bookkeeping over a statement that is now available, rather than a missing statement.

**Nothing about `σ`, the triple overlap, or the refined datum's laws.** The three conjugation
lemmas of `FormalSchemes.BasicOpenCoverTransitions` are stated over independent ambients and are
waiting for that isomorphism; they are not consumed here.

## Placement

Over `FormalSchemes.AwayCompletionRestrictUnique` and `FormalSchemes.BasicOpenChartImage`. The
refined-overlap declarations below have no home but this one.
`FormalSpectrum.basicOpen_mul_le_of_basicOpen_le` is the exception, and its
ratio is recorded here rather than left to be re-derived: it is a general statement about
`FormalSpectrum.basicOpen`, its subject-matter home is beside `FormalSpectrum.basicOpen_mul` in
`FormalSchemes.FormalSpectrum`, whose reverse closure is **535** against this file's **0**, and
it is declined on that ratio — this tree's standing disposition for a general statement with a
single call site. Re-cost the move when a second consumer appears.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.13, §10.15.
-/

noncomputable section

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- **Shrinking a basic open by a factor keeps it inside.** If `D(e) ≤ D(g)` then
`D(h · e) = D(h) ⊓ D(e) ≤ D(g)` for every `h`.

This is the step from `FormalSpectrum.exists_refined_overlap_element`'s conclusion to the
containment `FormalSpectrum.awayCompletionRestrict` consumes: the refined overlap is presented over
`A_i{1/(h · e)}`, with `h` the basic open refining the chart and `e` the element cutting out the
cross-chart overlap inside it. -/
theorem basicOpen_mul_le_of_basicOpen_le {e g : R} (h : R)
    (hle : basicOpen I e ≤ basicOpen I g) :
    basicOpen I (h * e) ≤ basicOpen I g := by
  rw [basicOpen_mul]
  exact le_trans inf_le_right hle

variable {A : Type u} [CommRing A] [Algebra R A]

/-- **The refined overlap's leg out of the coarse overlap algebra.** For a chart algebra `A` over
`R`, an element `g : A` cutting out the coarse overlap, an element `e : A` with `D(e) ≤ D(g)` in
`Spf A` and any `h : A`, the canonical `R`-algebra map

```
A{1/g}  →ₐ[R]  A{1/(h · e)}
```

`FormalSpectrum.awayCompletionRestrict` (`FormalSchemes.AwayCompletionRestrict`) supplies the ring
map from the containment alone; `FormalSpectrum.awayCompletionRestrictAlg` upgrades it to an
`A`-algebra map, and `AlgHom.restrictScalars` reads that over `R`, which is the base the charted
datum's transitions live over.

`e` is meant to be the element of `FormalSpectrum.exists_refined_overlap_element`, whose second
conjunct is the hypothesis *hle*, and `h` the basic open refining the chart; but neither is assumed
here and the statement is about two elements of `A` and an inclusion between their basic opens. -/
def refinedOverlapRestrict (hI : I.FG) (g e : A) (h : A)
    (hle : basicOpen (I.map (algebraMap R A)) e ≤ basicOpen (I.map (algebraMap R A)) g) :
    awayCompletion (I.map (algebraMap R A)) g →ₐ[R]
      awayCompletion (I.map (algebraMap R A)) (h * e) :=
  (awayCompletionRestrictAlg (I.map (algebraMap R A)) g (h * e) (hI.map _)
    (basicOpen_mul_le_of_basicOpen_le (I.map (algebraMap R A)) h hle)).restrictScalars R

/-- **`FormalSpectrum.refinedOverlapRestrict` is the canonical restriction**, on the nose: it is
`FormalSpectrum.awayCompletionRestrict` read as an `R`-algebra map, and no new object has been
introduced. In particular `FormalSpectrum.awayCompletionRestrict_unique`
(`FormalSchemes.AwayCompletionRestrictUnique`) characterises it — it is the only continuous ring
map `A{1/g} →+* A{1/(h · e)}` under `A`. -/
theorem coe_refinedOverlapRestrict (hI : I.FG) (g e : A) (h : A)
    (hle : basicOpen (I.map (algebraMap R A)) e ≤ basicOpen (I.map (algebraMap R A)) g) :
    (refinedOverlapRestrict I hI g e h hle :
        awayCompletion (I.map (algebraMap R A)) g →+*
          awayCompletion (I.map (algebraMap R A)) (h * e)) =
      awayCompletionRestrict (I.map (algebraMap R A)) g (h * e) (hI.map _)
        (basicOpen_mul_le_of_basicOpen_le (I.map (algebraMap R A)) h hle) :=
  rfl

section Refined

variable {Ai Aj : Type u} [CommRing Ai] [CommRing Aj] [Algebra R Ai] [Algebra R Aj]

/-- **The refined overlap element, as data.** `FormalSpectrum.exists_refined_overlap_element`
(`FormalSchemes.BasicOpenChartImage`) is an existential and the refined chart family needs the
element itself -- it is the overlap element of the refined datum at the pair *⟨i, h⟩*, *⟨j, h'⟩*,
so it has to be a function of the two charts and the two refining elements. Chosen once here, and
its two properties read off below, so that every consumer gets the *same* element. -/
def refinedOverlapElt (hI : I.FG) (gij : Ai) (gji : Aj)
    (τ : awayCompletion (I.map (algebraMap R Ai)) gij ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) gji)
    (h : Ai) (h' : Aj) : Ai :=
  (exists_refined_overlap_element I hI gij gji τ h h').choose

/-- **`FormalSpectrum.refinedOverlapElt` cuts out the refined overlap**, read inside the refined
chart `Spf (A_i{1/h})`: the defining property of the element, transported off the existential. -/
theorem basicOpen_awayCompletionHom_refinedOverlapElt (hI : I.FG) (gij : Ai) (gji : Aj)
    (τ : awayCompletion (I.map (algebraMap R Ai)) gij ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) gji)
    (h : Ai) (h' : Aj) :
    (basicOpen (awayCompletionIdeal (I.map (algebraMap R Ai)) h)
          (awayCompletionHom (I.map (algebraMap R Ai)) h (refinedOverlapElt I hI gij gji τ h h')) :
            Set (FormalSpectrum (awayCompletionIdeal (I.map (algebraMap R Ai)) h)))
      = basicOpenChartBase (I.map (algebraMap R Ai)) h ⁻¹'
          (basicOpenChartBase (I.map (algebraMap R Ai)) gij ''
            (basicOpen (awayCompletionIdeal (I.map (algebraMap R Ai)) gij)
                (τ.symm (awayCompletionHom (I.map (algebraMap R Aj)) gji h')) :
              Set (FormalSpectrum (awayCompletionIdeal (I.map (algebraMap R Ai)) gij)))) :=
  (exists_refined_overlap_element I hI gij gji τ h h').choose_spec.1

/-- **`FormalSpectrum.refinedOverlapElt` lies inside the coarse overlap**, which is what makes the
leg below exist. -/
theorem basicOpen_refinedOverlapElt_le (hI : I.FG) (gij : Ai) (gji : Aj)
    (τ : awayCompletion (I.map (algebraMap R Ai)) gij ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) gji)
    (h : Ai) (h' : Aj) :
    basicOpen (I.map (algebraMap R Ai)) (refinedOverlapElt I hI gij gji τ h h') ≤
      basicOpen (I.map (algebraMap R Ai)) gij :=
  (exists_refined_overlap_element I hI gij gji τ h h').choose_spec.2

/-- **The leg at a cross-chart refined pair**: the `R`-algebra map from the coarse overlap algebra
`A_i{1/g_ij}` into the refined presentation `A_i{1/(h · e)}`, with `e` the chosen element above.

This is `FormalSpectrum.refinedOverlapRestrict` at the containment
`FormalSpectrum.basicOpen_refinedOverlapElt_le`, and it is the statement issue 2148's refinement
consumes. The element and the map are tied together by construction rather than by two separate
existentials: `e` is determined only up to an equality of basic opens, so a map obtained from a
different choice would be a map into a different ring. -/
def refinedOverlapLeg (hI : I.FG) (gij : Ai) (gji : Aj)
    (τ : awayCompletion (I.map (algebraMap R Ai)) gij ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) gji)
    (h : Ai) (h' : Aj) :
    awayCompletion (I.map (algebraMap R Ai)) gij →ₐ[R]
      awayCompletion (I.map (algebraMap R Ai)) (h * refinedOverlapElt I hI gij gji τ h h') :=
  refinedOverlapRestrict I hI gij (refinedOverlapElt I hI gij gji τ h h') h
    (basicOpen_refinedOverlapElt_le I hI gij gji τ h h')

end Refined

end FormalSpectrum
