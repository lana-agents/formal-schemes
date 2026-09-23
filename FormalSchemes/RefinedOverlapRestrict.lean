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
transitivity that the stronger hypothesis exists to feed. Two steps then stand between these legs
and the transition, and this file now carries one of them.

**The chart-matching step is below.** Transporting *τ_ij* along that identification lands on *some*
presentation of the refined overlap inside `Spf (A_i{1/g_ij})`, and what has to be checked is that
it is the one the refined datum indexes — the coarse overlap cut down by the refining element `h`
of chart *i* and by the *τ*-transport of the refining element `h'` of chart *j*. That is
`FormalSpectrum.basicOpen_awayCompletionHom_mul_refinedOverlapElt`, and it is where the topological
content of `FormalSpectrum.exists_refined_overlap_element` is spent: its defining property is an
equality inside the **refined** chart `Spf (A_i{1/h})`, and the transition needs it inside the
**coarse** one.

**The transport of *τ_ij* itself is not here and is not on this tree.** An `R`-algebra equivalence
`σ : S ≃ₐ[R] T` carrying `S{1/u}` to `T{1/σ u}` is a general statement with no formal geometry in
it; `FormalSpectrum.awayTransport` (`FormalSchemes.AwayBaseChangeGluedX`) moves an *ideal*,
`CompletedTensorAwayInterchange.awayCongrEquiv` (`FormalSchemes.AwayCompletionCongrEquiv`) moves
the *element* at a fixed base, and `FormalSpectrum.awayCompletionAlgEquiv`
(`FormalSchemes.AwayCompletionUniversal`) enlarges the scalars of an equivalence that already
exists. None of the three is it.

**Nothing about `σ`, the triple overlap, or the refined datum's laws.** The three conjugation
lemmas of `FormalSchemes.BasicOpenCoverTransitions` are stated over independent ambients and are
waiting for that isomorphism; they are not consumed here.

## Placement

Over `FormalSchemes.AwayCompletionRestrictUnique` and `FormalSchemes.BasicOpenChartImage`. The
refined-overlap declarations below have no home but this one.
`FormalSpectrum.basicOpen_mul_le_of_basicOpen_le` is the exception, and its ratio is recorded here
rather than left to be re-derived: it is a general statement about `FormalSpectrum.basicOpen`, its
subject-matter home is beside `FormalSpectrum.basicOpen_mul` in `FormalSchemes.FormalSpectrum`,
whose reverse closure is **535** against this file's **0**, and it is declined on that ratio — this
tree's standing disposition for a general statement with a single call site. Re-cost the move when
a second consumer appears.

`FormalSpectrum.preimage_basicOpen_basicOpenChartBase` raises **no** placement question, and saying
why is worth a paragraph because the obvious reading of it is wrong. It looks like a general
statement about `FormalSpectrum.basicOpenChartBase` wanting a home beside that definition; it is
not. The general statement is `FormalSpectrum.map_preimage_basicOpen` (`FormalSchemes.SpfMap`) —
the preimage of a basic open along *any* map of formal spectra — which already has a home and a
name, and whose reverse closure is **504**. This file already reaches it: `FormalSchemes.SpfMap`
lies inside this file's forward closure of **41** modules. What is added below is that lemma at one
chart, read through `SetLike.coe` so that a `rw` can use it, with
`AlgebraicGeometry.BasicOpenCover.preimage_basicOpen_chartToBase`
(`FormalSchemes.BasicOpenCoverOpenImmersion`) as the precedent for the spelling. Nothing general is
being introduced, so there is nothing to move and no ratio to weigh.

`FormalSpectrum.functor_obj_preimage_basicOpen` (`FormalSchemes.BasicOpenImmersionLRS`, also inside
those 41) names the *image*-of-a-preimage step that
`FormalSpectrum.coe_basicOpen_mul_refinedOverlapElt` takes below, and using it there is **declined,
measured**: its left-hand side takes the image through `IsOpenMap.functor`, which is only
definitionally the set-level image, so `rw` cannot see it and bridging it needs a `have` restating
the whole ambient — **+6** tactic lines against the `FormalSpectrum.basicOpen_mul` route actually
taken, to replace two. It covers only that proof's left leg in any case; the right leg's argument
is an arbitrary set. Re-cost it if the wrapper ever gets a set-level form.

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
  have hpre : basicOpenChartBase (I.map (algebraMap R Ai)) h ⁻¹'
        (basicOpen (I.map (algebraMap R Ai)) (refinedOverlapElt I hI gij gji τ h h') :
          Set (FormalSpectrum (I.map (algebraMap R Ai))))
      = basicOpenChartBase (I.map (algebraMap R Ai)) h ⁻¹'
        (basicOpenChartBase (I.map (algebraMap R Ai)) gij ''
          (basicOpen (awayCompletionIdeal (I.map (algebraMap R Ai)) gij)
              (τ.symm (awayCompletionHom (I.map (algebraMap R Aj)) gji h')) :
            Set (FormalSpectrum (awayCompletionIdeal (I.map (algebraMap R Ai)) gij)))) := by
    rw [preimage_basicOpen_basicOpenChartBase]
    exact basicOpen_awayCompletionHom_refinedOverlapElt I hI gij gji τ h h'
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
