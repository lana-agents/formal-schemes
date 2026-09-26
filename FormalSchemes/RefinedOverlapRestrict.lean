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
* `FormalSpectrum.preimage_basicOpen_basicOpenChartBase`: the preimage of `D(b)` under the affine
  basic-open chart is `D(b̂)` — `FormalSpectrum.map_preimage_basicOpen` (`FormalSchemes.SpfMap`) at
  this chart, read through `SetLike.coe`. No content; a spelling.
* `FormalSpectrum.coe_basicOpen_mul_refinedOverlapElt` and
  `FormalSpectrum.basicOpen_awayCompletionHom_mul_refinedOverlapElt`: **the refined overlap read
  in the coarse chart** rather than in the refined one — the statement the transition waits on,
  see below.

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
isomorphism from that span is **not open any more, and it is not here**: it is
`FormalSpectrum.refinedOverlapTransition`
(`FormalSchemes.RefinedOverlapTransition`, issue 2196), one module downstream. What it wanted was
never a statement but the **composite**, and the route below is the one that module takes:
`FormalSpectrum.awayCompletionNestedAlgEquivOfLe` (`FormalSchemes.AwayCompletionUniversal`) into
the coarse chart, then the transport of *τ_ij* named at the end of this section, then
`FormalSpectrum.awayCompletionCongrBasicOpenAlg` (`FormalSchemes.AwayCompletionRestrictUnique`,
which this file already imports) at the identification the two statements below supply, then the
first step again on the *j* side. Four declarations, all on the tree, none of them here.

**The composite is not expensive, and that is what row 2196 was scoped from.** The four above join
to the bottom isomorphism directly: measured with `lake env lean` outside the tree, at the default
heartbeats, a sixteen-line declaration — ten lines of term after the `:=` — whose `#print axioms`
is `[propext, Classical.choice, Quot.sound]`. Two bookkeeping steps are wanted that the route above
does not name, and **they fail differently, which is the part worth knowing**.
`FormalSpectrum.awayCompletionCongrBasicOpenAlg` is an equivalence over the base of its *own* ideal
rather than over `R`, so it wants `AlgEquiv.restrictScalars`; a paste that omits it does **not**
report a scalar mismatch but exhausts the default heartbeats at `isDefEq`, the elaborator having
been asked whether `R` and that completion are the same scalar ring and walking the completion
tower to answer. **A timeout there is that omission and not an obstruction** — raising the budget
to a million heartbeats only buys a longer one. The second step is the hypothesis's ideal
convention: it is asked for at `I.map (algebraMap R _)` where the two statements below are at
`FormalSpectrum.awayCompletionIdeal`, the same ideal-convention bridge named at the end of this
section one step later, and omitting *that* one does fail with a type error in seconds, naming both
spellings. **So what was left was placement, not search and not elaboration**: this file reaches
neither `FormalSchemes.AwayBaseChangeTopFiniteType` nor
`FormalSchemes.AwayCompletionAlgHomBasicOpen`, and no module of this tree reached everything the
composite names, so the transition took a module of its own. Both bookkeeping steps are restated at
the point of use in `FormalSchemes.RefinedOverlapTransition`'s own docstring, and the diagnosis is
kept here because a reader who meets the four-declaration list above meets the timeout before that
module is in view. Re-measure all of this rather than quoting it.

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
transitivity that the stronger hypothesis exists to feed. Two steps then stand between these legs
and the transition — matching the transported presentation against the one the refined datum
indexes, and the transport of *τ_ij* itself. **This file carries the first; the second is on the
tree.** Neither is a missing statement, so what stood between these legs and the transition was
the assembly of named statements — this section's first item, now
`FormalSpectrum.refinedOverlapTransition`.

**The chart-matching step is below.** Transporting *τ_ij* along that identification lands on *some*
presentation of the refined overlap inside `Spf (A_i{1/g_ij})`, and what has to be checked is that
it is the one the refined datum indexes — the coarse overlap cut down by the refining element `h`
of chart *i* and by the *τ*-transport of the refining element `h'` of chart *j*. That is
`FormalSpectrum.basicOpen_awayCompletionHom_mul_refinedOverlapElt`, and it is where the topological
content of `FormalSpectrum.exists_refined_overlap_element` is spent: its defining property is an
equality inside the **refined** chart `Spf (A_i{1/h})`, and the transition needs it inside the
**coarse** one. What it produces is a *meet*, and carrying a meet across *τ_ij* is
`FormalSpectrum.basicOpen_awayCompletionAlgEquiv_eq_iff`
(`FormalSchemes.AwayCompletionAlgHomBasicOpen`, issue 2193), whose own module docstring gives the
three-line rewrite for exactly this shape.

**The transport of *τ_ij* itself is not here, and it is not missing.**
`FormalSpectrum.awayCompletionAlgEquivOfBase` (`FormalSchemes.AwayBaseChangeTopFiniteType`, issue
2192) is that statement: an `R`-algebra equivalence `σ : S ≃ₐ[R] T` with `σ u = v` gives
`S{1/u} ≃ₐ[R] T{1/v}`, both completions read at the extension of one ideal of the common base. That
is the convention `FormalSpectrum.awayCompletionNestedAlgEquivOfLe` leaves its target in, so at
*τ_ij* the two compose directly; written instead with `FormalSpectrum.awayCompletionIdeal` on both
sides, as the statements below are, the step costs three tactic lines through
`FormalSpectrum.map_algebraMap_awayCompletion` (`FormalSchemes.BasicOpenChart`), and
`FormalSpectrum.awayTransport` (`FormalSchemes.AwayBaseChangeGluedX`) is the general form of that
rewriting step. `FormalSchemes.AwayBaseChangeTopFiniteType`'s own
`## Hypotheses, and what is not proved` prices that reading at those three lines and records why no
declaration is added for it. The step is not drawn *here* because this file reaches neither module:
both lie outside `FormalSchemes.RefinedOverlapRestrict`'s forward closure of **41**, and the edges
cost **+15** and **+54** modules. A citation costs no edge.

The three declarations this paragraph used to weigh are each correctly described and are kept:
`FormalSpectrum.awayTransport` moves an *ideal*, `CompletedTensorAwayInterchange.awayCongrEquiv`
(`FormalSchemes.AwayCompletionCongrEquiv`) moves the *element* at a fixed base, and
`FormalSpectrum.awayCompletionAlgEquiv` (`FormalSchemes.AwayCompletionUniversal`) enlarges the
scalars of an equivalence that already exists. None of *those three* is it — which is not what this
paragraph said twice. It said none on this tree was, and that had been false since
`FormalSpectrum.awayCompletionAlgEquivOfBase` landed, which was already so at the base this
paragraph last sat on. **Before writing *is not on this tree*, grep the tree and not this file's
imports**: the fourth declaration sits outside the 41 above, and that is how a merged statement was
recorded as absent by two separate readings of the same paragraph.

**Nothing about `σ`, the triple overlap, or the refined datum's laws.** The three conjugation
lemmas of `FormalSchemes.BasicOpenCoverTransitions` are stated over independent ambients and are
waiting for that isomorphism; they are not consumed here.

## Placement

Over `FormalSchemes.AwayCompletionRestrictUnique` and `FormalSchemes.BasicOpenChartImage`. The
refined-overlap declarations below have no home but this one.
`FormalSpectrum.basicOpen_mul_le_of_basicOpen_le` is the exception, and its ratio is recorded here
rather than left to be re-derived: it is a general statement about `FormalSpectrum.basicOpen`, and
its subject-matter home is beside `FormalSpectrum.basicOpen_mul` in `FormalSchemes.FormalSpectrum`,
whose reverse closure is **537**.

**That move has been re-costed once, and what declines it is no longer the argument first written
here.** The first was the single call site, with the invitation to re-cost when a second appeared.
A second has appeared and the disposition did not change. The two call sites are
`FormalSpectrum.refinedOverlapRestrict` below and `FormalSpectrum.refinedOverlapTransition`
(`FormalSchemes.RefinedOverlapTransition`), and neither of them needs the move: that module imports
this one, so it reaches the lemma where it already stands. What decides it now is the rebuild on
each side. This file's reverse closure is **1** — that module and nothing else — so editing the
statement here re-elaborates two modules, against the 537 that editing it in
`FormalSchemes.FormalSpectrum` would. **Re-cost it again when a consumer appears that does not
reach this file**, which is the only shape that makes the move buy anything; a third consumer
inside this file's own subtree does not.

`FormalSpectrum.preimage_basicOpen_basicOpenChartBase` raises **no** placement question, and saying
why is worth a paragraph because the obvious reading of it is wrong. It looks like a general
statement about `FormalSpectrum.basicOpenChartBase` wanting a home beside that definition; it is
not. The general statement is `FormalSpectrum.map_preimage_basicOpen` (`FormalSchemes.SpfMap`) —
the preimage of a basic open along *any* map of formal spectra — which already has a home and a
name, and whose reverse closure is **506**. This file already reaches it: `FormalSchemes.SpfMap`
lies inside this file's forward closure of **41** modules. What is added below is that lemma at one
chart, read through `SetLike.coe` so that a `rw` can use it, with
`AlgebraicGeometry.BasicOpenCover.preimage_basicOpen_chartToBase`
(`FormalSchemes.BasicOpenCoverOpenImmersion`) as the precedent for the spelling. Nothing general is
being introduced, so there is nothing to move and no ratio to weigh.

`FormalSpectrum.functor_obj_preimage_basicOpen` (`FormalSchemes.BasicOpenImmersionLRS`, also inside
those 41) names the *image*-of-a-preimage step that
`FormalSpectrum.coe_basicOpen_mul_refinedOverlapElt` takes below, and using it there is
**declined**. The obstruction is a spelling, and naming it correctly is the point of this
paragraph, because it is not the one the wrapper's statement suggests. `IsOpenMap.coe_functor_obj`
**does** read that left-hand side at set level, and `TopologicalSpace.Opens.map_coe` reads the
preimage — both fire. What they leave behind is the chart's base map written through
`FormalSpectrum.mapTop` and `CategoryTheory.ConcreteCategory.hom`, and nothing on this tree
identifies that spelling with `FormalSpectrum.basicOpenChartBase`, so the next `rw` reports a
pattern it cannot find and a `have … := rfl` between the two spellings has to be written by hand.

**Measured**, `lake env lean` on a copy of this file with only the proof body below swapped: the
wrapper route with that bridge, in its own best arrangement rather than patched into the route
taken, is **10** tactic lines against the **8** below, and without the bridge it is EXIT 1. So the
line count does not favour it, and it is not what decides this either. What decides it is that the
bridge is a bare defeq between two spellings of one map with no lemma to name it, and that the
wrapper covers only this proof's left leg in any case: the right leg's argument is an arbitrary
set, so `Set.image_preimage_eq_inter_range` and `FormalSpectrum.range_basicOpenChartBase` are paid
either way. Re-cost it if the wrapper gains a set-level form, or if the chart's base map gains the
coercion lemma this bridge stands in for.

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

/-- **The preimage of a basic open under the affine basic-open chart is a basic open**, cut out by
the structural image of the same element: `Spf R{1/f} → Spf R` pulls `D(b)` back to `D(b̂)`.

**No content is added here and none is proved here.** `FormalSpectrum.map_preimage_basicOpen`
(`FormalSchemes.SpfMap`) is the general statement — the preimage of a basic open along *any* map of
formal spectra is the basic open at the image element — and `FormalSpectrum.basicOpenChartBase` is
by definition that map at `J := awayCompletionIdeal I f`, `φ := awayCompletionHom I f`, so this is
that lemma read through `SetLike.coe` and nothing else. The `Set`-level reading is what the two
statements below rewrite with, and
`AlgebraicGeometry.BasicOpenCover.preimage_basicOpen_chartToBase`
(`FormalSchemes.BasicOpenCoverOpenImmersion`) is the same specialisation at a different chart,
spelled the same way — this file follows it rather than inventing a second idiom.

`FormalSpectrum.exists_refined_overlap_element` (`FormalSchemes.BasicOpenChartImage`) takes the
same step inline, in one `simp only` and one `not_congr`, going through neither name.

This is the *preimage*, so it needs no hypothesis at all — not `Ideal.FG`, and nothing relating
`b` to `f`. The companion statement about *images* is the one that costs something, and it is
`FormalSpectrum.basicOpen_basicOpenChart_is_basicOpen`. -/
theorem preimage_basicOpen_basicOpenChartBase (f b : R) :
    basicOpenChartBase I f ⁻¹' (basicOpen I b : Set (FormalSpectrum I))
      = (basicOpen (awayCompletionIdeal I f) (awayCompletionHom I f b) :
          Set (FormalSpectrum (awayCompletionIdeal I f))) :=
  congrArg SetLike.coe
    (map_preimage_basicOpen I (awayCompletionIdeal I f) (awayCompletionHom I f)
      (le_comap_awayCompletionHom I f) b)

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

/-! ### The refined overlap read in the coarse chart -/

/-- **The refined overlap, read downstairs in `Spf A_i`.** The basic open of the refined
presentation `A_i{1/(h · e)}` is `D(h)` met with the image of the *j*-side refining element under
the coarse chart.

`FormalSpectrum.basicOpen_awayCompletionHom_refinedOverlapElt` states the defining property inside
the **refined** chart `Spf (A_i{1/h})`, as a preimage along that chart. Pushing it forward is what
this says: `FormalSpectrum.preimage_basicOpen_basicOpenChartBase` reads the left-hand side as a
preimage too, `Set.image_preimage_eq_inter_range` turns both into intersections with the chart's
range, and `FormalSpectrum.range_basicOpenChartBase` (`FormalSchemes.BasicOpenChart`) identifies
that range with `D(h)`. **The meet with `D(h)` is not a loss**: the left-hand side already carries
the factor `h`, so nothing outside `D(h)` was ever being described.

Stated on the coercions to `Set` rather than on `Opens`, because the right-hand side is a set-level
image and `TopologicalSpace.Opens` has no image. -/
theorem coe_basicOpen_mul_refinedOverlapElt (hI : I.FG) (gij : Ai) (gji : Aj)
    (τ : awayCompletion (I.map (algebraMap R Ai)) gij ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) gji)
    (h : Ai) (h' : Aj) :
    (basicOpen (I.map (algebraMap R Ai))
        (h * refinedOverlapElt I hI gij gji τ h h') :
          Set (FormalSpectrum (I.map (algebraMap R Ai))))
      = (basicOpen (I.map (algebraMap R Ai)) h :
            Set (FormalSpectrum (I.map (algebraMap R Ai)))) ∩
        basicOpenChartBase (I.map (algebraMap R Ai)) gij ''
          (basicOpen (awayCompletionIdeal (I.map (algebraMap R Ai)) gij)
              (τ.symm (awayCompletionHom (I.map (algebraMap R Aj)) gji h')) :
            Set (FormalSpectrum (awayCompletionIdeal (I.map (algebraMap R Ai)) gij))) := by
  have hpre := (preimage_basicOpen_basicOpenChartBase (I.map (algebraMap R Ai)) h
      (refinedOverlapElt I hI gij gji τ h h')).trans
    (basicOpen_awayCompletionHom_refinedOverlapElt I hI gij gji τ h h')
  have himg := congrArg (fun T => basicOpenChartBase (I.map (algebraMap R Ai)) h '' T) hpre
  simp only [Set.image_preimage_eq_inter_range,
    range_basicOpenChartBase (I.map (algebraMap R Ai)) h (hI.map _)] at himg
  rw [basicOpen_mul]
  simpa only [TopologicalSpace.Opens.coe_inf, Set.inter_comm] using himg

/-- **The refined overlap read inside the coarse overlap chart** — the statement the transition
waits on. Inside `Spf (A_i{1/g_ij})`, the refined presentation `A_i{1/(h · e)}` is cut out by the
two refining elements: `h` from chart *i*, and the *τ*-transport of `h'` from chart *j*.

This is the form the transition needs, and it is not the form
`FormalSpectrum.exists_refined_overlap_element` produces. That one pins `e` by an equality inside
the **refined** chart `Spf (A_i{1/h})`; the leg `FormalSpectrum.refinedOverlapLeg` and the
identification `FormalSpectrum.awayCompletionNestedAlgEquivOfLe`
(`FormalSchemes.AwayCompletionUniversal`) both work inside the **coarse** chart
`Spf (A_i{1/g_ij})`, and the two are different charts of `Spf A_i`. Getting from one to the other
is exactly where the topological content of the refined overlap element is spent, and it is spent
here: the proof goes down to `Spf A_i` by `FormalSpectrum.coe_basicOpen_mul_refinedOverlapElt` and
comes back up along the coarse chart, which is injective by
`FormalSpectrum.isOpenEmbedding_basicOpenChartBase` (`FormalSchemes.BasicOpenChart`).

**Why `e` alone would not do.** `e` is determined only up to an equality of basic opens, so a
statement naming `D(e)` in one chart says nothing about any other presentation of the same open.
What makes this usable is that both sides are written with the elements the refined datum indexes
by — `h`, `h'` and `τ` — and `e` appears only inside `h · e`. -/
theorem basicOpen_awayCompletionHom_mul_refinedOverlapElt (hI : I.FG) (gij : Ai) (gji : Aj)
    (τ : awayCompletion (I.map (algebraMap R Ai)) gij ≃ₐ[R]
      awayCompletion (I.map (algebraMap R Aj)) gji)
    (h : Ai) (h' : Aj) :
    basicOpen (awayCompletionIdeal (I.map (algebraMap R Ai)) gij)
        (awayCompletionHom (I.map (algebraMap R Ai)) gij
          (h * refinedOverlapElt I hI gij gji τ h h'))
      = basicOpen (awayCompletionIdeal (I.map (algebraMap R Ai)) gij)
          (awayCompletionHom (I.map (algebraMap R Ai)) gij h)
        ⊓ basicOpen (awayCompletionIdeal (I.map (algebraMap R Ai)) gij)
          (τ.symm (awayCompletionHom (I.map (algebraMap R Aj)) gji h')) := by
  have hinj : Function.Injective (basicOpenChartBase (I.map (algebraMap R Ai)) gij) :=
    (isOpenEmbedding_basicOpenChartBase (I.map (algebraMap R Ai)) gij (hI.map _)).injective
  refine SetLike.coe_injective ?_
  rw [TopologicalSpace.Opens.coe_inf, ← preimage_basicOpen_basicOpenChartBase,
    ← preimage_basicOpen_basicOpenChartBase, coe_basicOpen_mul_refinedOverlapElt,
    Set.preimage_inter, hinj.preimage_image]

end Refined

end FormalSpectrum
