import FormalSchemes.AdicOverBaseChart
import FormalSchemes.GlobalSectionsHomGlue

set_option linter.style.header false

/-!
# Gluing a morphism into a formal spectrum with no `hs`-shaped hypothesis

`AlgebraicGeometry.FormalScheme.homOfGlobalSectionsHom` (`FormalSchemes.GlueHomToSpf`) builds a
morphism `X ⟶ Spf R` out of a homomorphism `ψ : R →+* Γ(X, 𝒪_X)`, and takes three families of
continuity conditions: `hcont` on the charts of a supplied cover, and `hf`, `hg` on a supplied
affine cover of each pairwise overlap. Stated at a chart family that was produced by
`Classical.choice`, all three are of the shape

```
∀ x, I ≤ (chart x).J.comap (globalSectionsMap I (chart x).J ((chart x).map ≫ s))
```

that `FormalSchemes.GeneralFibreProductLiftAdic` records as **unreachable**: nothing describes the
chosen chart, so there is nothing to prove the bound from, and "an open immersion is adic on
sections" is false in general (issues 460/468/472/487). That module says, of the layer issue 805
deleted rather than proved, *"do not reintroduce an `hs`-shaped hypothesis in a new one"*.

The fix issue 468 found for the diagonal, and issue 798 generalised, is not to prove the bound at a
chosen chart but to **choose the chart from a neighbourhood basis that already records it**:
`AlgebraicGeometry.FormalScheme.AdicOverBaseLocallyFG` (`FormalSchemes.AdicOverBaseChart`) is
`AlgebraicGeometry.FormalScheme.LocallyFG` with the bound added to the chart it produces, and
`AlgebraicGeometry.BothChartedFibreDatumXY.adicBothCharts` with
`AlgebraicGeometry.BothChartedFibreDatumXY.adicBothCharts_hs`
(`FormalSchemes.GeneralFibreProductLiftAdic`) are the chosen family together with the continuity
discharged from the same witness.

This file runs that pattern for
`AlgebraicGeometry.FormalScheme.homOfGlobalSectionsHom`. Two predicates carry all three families:

* `AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG` — the `ψ`-relative analogue of
  `AlgebraicGeometry.FormalScheme.AdicOverBaseLocallyFG`, which supplies `charts`, `hfg` **and**
  `hcont` from one witness;
* `AlgebraicGeometry.FormalScheme.AdicOverBasePairLocallyFG` — the same for **two** base morphisms
  at once, which supplies `ocharts`, `hofg`, `hf` **and** `hg` on each overlap from one witness.

`AlgebraicGeometry.FormalScheme.homOfGlobalSectionsHomOfAdicSections` is the construction over the
two of them. Nothing in it asks a bound of a chart it did not produce.

## Why the overlap condition is about a *pair* of base morphisms, and what is open about it

On the `(i, j)` overlap, `AlgebraicGeometry.FormalScheme.homOfGlobalSectionsHom` compares two
morphisms into `Spf R` — the two projections followed by the chart morphisms at `i` and at `j` —
and needs the *same* affine cover of the overlap to be adic over **both**. A witness for each
separately gives two unrelated charts, so
`AlgebraicGeometry.FormalScheme.AdicOverBaseLocallyFG` twice is not enough; the pair condition is
the joint form, in the same way that
`AlgebraicGeometry.BothChartedFibreDatumXY.nonempty_adicBothChart` needs one chart to satisfy two
range constraints at once rather than two charts satisfying one each.

**Whether the joint condition follows from the two separate ones is open, and this file does not
settle it.** `AlgebraicGeometry.FormalScheme.AdicOverBasePairLocallyFG.adicOverBase_left` and
`AlgebraicGeometry.FormalScheme.AdicOverBasePairLocallyFG.adicOverBase_right` give one direction;
the converse would need a common refinement of two adic-over-base charts that stays adic over both,
and the refinement `AlgebraicGeometry.FormalScheme.exists_affineChart_subset_adicOverBase` provides
is a *basic open* of one of them — for which
`FormalSpectrum.le_comap_globalSectionsMap_basicOpenChart_comp` transports the bound — while
transporting the *other* bound would need the resulting open immersion into the other chart to be
adic on sections, and that is the statement `FormalSchemes.GeneralFibreProductLiftAdic` records as
false in general (issues 460/468/472/487). So the obvious route is blocked at the same place the
`hs` problem was, and no route around it is offered here.

**What is *not* blocked is refining a pair witness**, and it is worth separating the two.
`AlgebraicGeometry.FormalScheme.exists_affineChart_subset_adicOverBasePair` below shrinks a pair
witness into any given open with **both** bounds intact, because a pair witness hands over a single
chart carrying both, and `FormalSpectrum.le_comap_globalSectionsMap_basicOpenChart_comp` then
applies to it twice along the *same* `FormalSpectrum.basicOpenChart`. Nothing about open immersions
being adic on sections is needed for that. So the open question is the **merge** — two unrelated
witnesses into one — and not the refinement.

`AlgebraicGeometry.FormalScheme.AdicOverBaseLocallyFG.pair_of_eq` is the one cheap sufficient
condition: if the two base morphisms are *equal*, one witness serves. That is not circular but it
is close to it, and it is worth seeing why. The two base morphisms on the `(i, j)` overlap are
equal — that is
`AlgebraicGeometry.FormalScheme.OpenCover.pullback_fst_comp_eq_snd_comp`, the agreement
`AlgebraicGeometry.FormalScheme.OpenCover.glueMorphisms` consumes — but the only proof of it on
this tree runs through `hf` and `hg` themselves. So
`AlgebraicGeometry.FormalScheme.AdicOverBaseLocallyFG.pair_of_eq` cannot be used to discharge the
overlap condition here; it records where the joint condition would become free if the agreement
were ever proved independently.

## Why the bridge to `AlgebraicGeometry.FormalScheme.SpfHomContinuity` runs one way only

`AlgebraicGeometry.FormalScheme.SpfHomContinuity` (`FormalSchemes.GlueHomToSpf`) bundles the same
three families over a supplied chart family, with the charts on the overlaps taken canonically by
`AlgebraicGeometry.FormalScheme.overlapChartOf`. Holding one of those *and* the witnesses here
gives the same morphism, by
`AlgebraicGeometry.FormalScheme.homOfGlobalSectionsHomOfAdicSections_eq_homOfSpfHomContinuity`.

**The other direction is not available, and the obstruction is the one above.**
`AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.OverlapAdic` gives the two bounds at the
chart *its own* witness produces at a point of the overlap; the bundle asks for them at
`AlgebraicGeometry.FormalScheme.overlapChartOf` at the same point, which is
`AlgebraicGeometry.FormalScheme.LocallyFG.chart` of the overlap and is described by nothing. I
reduced the two fields to their goals rather than reasoning about them: what is left is exactly a
bound at one affine chart at a point given the bound at another affine chart at that point, which
is the open-immersion-adic-on-sections statement issues 460/468/472/487 record as false in
general. So the bundle is *not* weaker than the witnesses here, and neither predicate should be
described as the general form of the other.

## Main definitions and results

* `AlgebraicGeometry.FormalScheme.AffineChart.sectionsHom`: the chart-restriction of `ψ` at a
  single chart, definitionally `AlgebraicGeometry.FormalScheme.chartHom` of the family at that
  point (`AlgebraicGeometry.FormalScheme.chartHom_eq_sectionsHom`).
* `AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG`, with
  `AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.locallyFG`,
  `AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.chart`,
  `AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.fg_chart` and
  `AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.cont`.
* `AlgebraicGeometry.FormalScheme.AdicOverBasePairLocallyFG`, with
  `AlgebraicGeometry.FormalScheme.AdicOverBasePairLocallyFG.chart`,
  `AlgebraicGeometry.FormalScheme.AdicOverBasePairLocallyFG.fg_chart`,
  `AlgebraicGeometry.FormalScheme.AdicOverBasePairLocallyFG.left`,
  `AlgebraicGeometry.FormalScheme.AdicOverBasePairLocallyFG.right`,
  `AlgebraicGeometry.FormalScheme.AdicOverBasePairLocallyFG.adicOverBase_left`,
  `AlgebraicGeometry.FormalScheme.AdicOverBasePairLocallyFG.adicOverBase_right`, and
  `AlgebraicGeometry.FormalScheme.AdicOverBaseLocallyFG.pair_of_eq`.
* `AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.OverlapAdic`: the overlap condition, one
  pair witness per pair of points.
* `AlgebraicGeometry.FormalScheme.homOfGlobalSectionsHomOfAdicSections`: **the construction**, with
  `AlgebraicGeometry.FormalScheme.chart_comp_homOfGlobalSectionsHomOfAdicSections`,
  `AlgebraicGeometry.FormalScheme.globalSectionsHom_homOfGlobalSectionsHomOfAdicSections`,
  `AlgebraicGeometry.FormalScheme.continuous_homOfGlobalSectionsHomOfAdicSections` and
  `AlgebraicGeometry.FormalScheme.existsUnique_globalSectionsHom_eq_of_adicSections`.
* `AlgebraicGeometry.FormalScheme.homOfGlobalSectionsHomOfAdicSections_eq`: it is the *same*
  morphism `AlgebraicGeometry.FormalScheme.homOfGlobalSectionsHom` builds from any other overlap
  data at the same charts, so the overlap witness builds the morphism without pinning it down.
* `AlgebraicGeometry.FormalScheme.exists_affineChart_subset_adicSections` and
  `AlgebraicGeometry.FormalScheme.exists_affineChart_subset_adicOverBasePair`: **the charts of both
  predicates really are neighbourhood bases**, which is what their docstrings' "on a neighbourhood
  basis" refers to and what makes either checkable patch by patch. Both are the shared shrinking
  step `AlgebraicGeometry.FormalScheme.exists_basicOpenRefine_subset` (`FormalSchemes.LocallyFG`)
  followed by a transport; the transport lemmas are
  `AlgebraicGeometry.FormalScheme.AffineChart.sectionsHom_basicOpenRefine`,
  `AlgebraicGeometry.FormalScheme.AffineChart.le_comap_sectionsHom_basicOpenRefine` and
  `AlgebraicGeometry.FormalScheme.AffineChart.le_comap_globalSectionsMap_basicOpenRefine`.
* `AlgebraicGeometry.FormalScheme.AffineChart.ofSpf`,
  `AlgebraicGeometry.FormalScheme.AffineChart.sectionsHom_ofSpf` and
  `AlgebraicGeometry.FormalScheme.adicSectionsLocallyFG_Spf`: the affine case. On
  `AlgebraicGeometry.FormalScheme.Spf J` the identity is a chart and the predicate is exactly
  continuity of `ψ`, so it is satisfiable.
* `AlgebraicGeometry.FormalScheme.homOfGlobalSectionsHomOfAdicSections_eq_homOfSpfHomContinuity`:
  the bridge to `AlgebraicGeometry.FormalScheme.SpfHomContinuity` (`FormalSchemes.GlueHomToSpf`) —
  a caller holding that bundle as well gets this file's morphism from it, in one direction only.

## What is *not* proved here

**No continuity family is discharged, and no witness of either predicate is produced.** This file
changes the shape of what has to be supplied: from three families of bounds on charts nothing
describes, to two existential conditions from which the charts *and* the bounds both come. Whether
`AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG` holds anywhere is untouched, and a scheme
satisfying it is not exhibited.

**The second of the two conditions is not independent, and the reason is downstream.**
`AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.overlapAdic`
(`FormalSchemes.AdicSectionsOverlap`) proves
`AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.OverlapAdic` for *every* witness, so
`AlgebraicGeometry.FormalScheme.homOfGlobalSectionsHomOfAdicSections` is a construction over one
witness rather than two. It does **not** settle the merge question of the section above, which is
about two unrelated witnesses; it uses that on an overlap the two base morphisms have the same
global-sections homomorphism, which is exactly the independent agreement
`AlgebraicGeometry.FormalScheme.AdicOverBaseLocallyFG.pair_of_eq`'s docstring says the joint
condition would become free from. The `s = t` form there is genuinely unusable, for the reason
recorded there; the global-sections form is not, and the two are different statements.

**`AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG` is strictly stronger than
`AlgebraicGeometry.FormalScheme.LocallyFG`** —
`AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.locallyFG` is the one-way projection and
there is no converse, since a `AlgebraicGeometry.FormalScheme.LocallyFG` witness carries no bound.
Reading the two as interchangeable is the error this whole file exists to avoid.

## Implementation notes

`AlgebraicGeometry.FormalScheme.AffineChart.sectionsHom_basicOpenRefine` is **not** `rfl`: both
sides pass through `FormalSpectrum.globalSectionsEquiv` and its inverse, and those cancel only
propositionally. The `rfl` at the end of its proof closes what is left after that cancellation, and
starting from `rfl` alone and reading the failure as the statement being false would be wrong.

`AlgebraicGeometry.FormalScheme.AffineChart.ofSpf` fills its
`AlgebraicGeometry.FormalScheme.AffineChart.isOpenImmersion` field with an explicit `@`-application
supplying `CategoryTheory.IsIso.id`. Instance synthesis does **not** find
`IsIso (𝟙 (FormalSpectrum.locallyRingedSpaceObj J))` at that position, and neither a `haveI` nor a
`letI` ahead of the structure literal makes it available there, although the same synthesis
succeeds at the top level of a section. Supplying the instance argument by position is what works.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4 (10.4.6), §10.6.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry CategoryTheory.Limits
open FormalSpectrum

namespace AlgebraicGeometry.FormalScheme

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable {X : FormalScheme.{u}} (ψ : R →+* X.presheaf.obj (op (⊤ : Opens X)))

/-! ### The `ψ`-relative adic-over-base condition -/

/-- **The chart-restriction of `ψ` at a single affine chart.** This is
`AlgebraicGeometry.FormalScheme.chartHom` with the family replaced by one of its values; the two
agree definitionally (`AlgebraicGeometry.FormalScheme.chartHom_eq_sectionsHom`), and this
spelling is what lets the predicate
below quantify over a chart rather than over a family. -/
def AffineChart.sectionsHom {x : X} (c : AffineChart X x) : R →+* c.R :=
  (globalSectionsEquiv c.I).toRingHom.comp
    ((c.map.c.app (op (⊤ : Opens X))).hom.comp ψ)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- `AlgebraicGeometry.FormalScheme.chartHom` of a family at `x` is
`AlgebraicGeometry.FormalScheme.AffineChart.sectionsHom` of that family's value at `x`, on the
nose. -/
theorem chartHom_eq_sectionsHom (charts : ∀ x : X, AffineChart X x) (x : X) :
    chartHom charts ψ x = (charts x).sectionsHom ψ :=
  rfl

/-- **`X` is adic over `ψ` on a neighbourhood basis** if every point has a finitely generated
affine open-immersion chart at which the chart-restriction of `ψ` is *already* continuous. This is
`AlgebraicGeometry.FormalScheme.AdicOverBaseLocallyFG` with the ring homomorphism `ψ` in place of
a base morphism's global-sections map — the shape that condition would take if there were a
morphism `X ⟶ Spf R` to state it over, which there is not, because building one is the point.

It is strictly stronger than `AlgebraicGeometry.FormalScheme.LocallyFG`
(`AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.locallyFG` below is the one-way projection):
that predicate asks only that a finitely generated chart exist, and says nothing about `ψ` at
it. -/
def AdicSectionsLocallyFG : Prop :=
  ∀ x : X, ∃ c : AffineChart X x, c.I.FG ∧ I ≤ c.I.comap (c.sectionsHom ψ)

variable {I ψ}

omit [TopologicalSpace R] [IsAdicRing I] in
/-- An adic-over-`ψ` scheme is in particular locally finitely generated: drop the bound. There is
no converse. -/
theorem AdicSectionsLocallyFG.locallyFG (hX : AdicSectionsLocallyFG I ψ) : X.LocallyFG := fun x =>
  let ⟨c, hfg, _⟩ := hX x
  ⟨c.R, c.commRing, c.topR, c.I, c.adic, c.map, hfg, c.mem, c.isOpenImmersion⟩

/-- **The chart family the witness supplies.** Unlike
`AlgebraicGeometry.FormalScheme.LocallyFG.chart`, this one arrives with its continuity bound
already attached (`AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.cont`), which is the
whole difference. -/
def AdicSectionsLocallyFG.chart (hX : AdicSectionsLocallyFG I ψ) (x : X) : AffineChart X x :=
  (hX x).choose

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The ideals of definition of `AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.chart` are
finitely generated: the `hfg`
argument of `AlgebraicGeometry.FormalScheme.homOfGlobalSectionsHom`. -/
theorem AdicSectionsLocallyFG.fg_chart (hX : AdicSectionsLocallyFG I ψ) (x : X) :
    (hX.chart x).I.FG :=
  (hX x).choose_spec.1

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The discharged `hcont`.** Each chart of
`AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.chart` carries the continuity
of the chart-restriction of `ψ` by construction, so the first of
`AlgebraicGeometry.FormalScheme.homOfGlobalSectionsHom`'s three continuity families is not a
hypothesis of anything below. -/
theorem AdicSectionsLocallyFG.cont (hX : AdicSectionsLocallyFG I ψ) (x : X) :
    I ≤ (hX.chart x).I.comap (chartHom hX.chart ψ x) :=
  (hX x).choose_spec.2

/-! ### Adic over two base morphisms at once -/

variable (I)

/-- **`Y` is adic over the pair `(s, t)` on a neighbourhood basis**: every point has one finitely
generated affine open-immersion chart that is adic on global sections over `s` *and* over `t`.

`AlgebraicGeometry.FormalScheme.AdicOverBaseLocallyFG Y s` together with
`AdicOverBaseLocallyFG Y t` is **weaker**, because it produces two unrelated charts. The overlap
hypotheses of `AlgebraicGeometry.FormalScheme.homOfGlobalSectionsHom` are about one cover and two
morphisms, so the joint form is the one they need. -/
def AdicOverBasePairLocallyFG (Y : FormalScheme.{u})
    (s t : Y.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I) : Prop :=
  ∀ y : Y, ∃ c : AffineChart Y y, c.I.FG ∧
    I ≤ c.I.comap (globalSectionsMap I c.I (c.map ≫ s)) ∧
    I ≤ c.I.comap (globalSectionsMap I c.I (c.map ≫ t))

variable {I}
variable {Y : FormalScheme.{u}} {s t : Y.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I}

/-- The chart family a pair witness supplies: the `ocharts` argument. -/
def AdicOverBasePairLocallyFG.chart (h : AdicOverBasePairLocallyFG I Y s t) (y : Y) :
    AffineChart Y y :=
  (h y).choose

/-- Their ideals of definition are finitely generated: the `hofg` argument. -/
theorem AdicOverBasePairLocallyFG.fg_chart (h : AdicOverBasePairLocallyFG I Y s t) (y : Y) :
    (h.chart y).I.FG :=
  (h y).choose_spec.1

/-- **The bound over the first base morphism**, discharged for the chart the same witness chose. -/
theorem AdicOverBasePairLocallyFG.left (h : AdicOverBasePairLocallyFG I Y s t) (y : Y) :
    I ≤ (h.chart y).I.comap (globalSectionsMap I (h.chart y).I ((h.chart y).map ≫ s)) :=
  (h y).choose_spec.2.1

/-- **The bound over the second base morphism**, for that same chart. -/
theorem AdicOverBasePairLocallyFG.right (h : AdicOverBasePairLocallyFG I Y s t) (y : Y) :
    I ≤ (h.chart y).I.comap (globalSectionsMap I (h.chart y).I ((h.chart y).map ≫ t)) :=
  (h y).choose_spec.2.2

/-- Forgetting the second bound. This direction is free; the converse is the open question the
module docstring discusses. -/
theorem AdicOverBasePairLocallyFG.adicOverBase_left (h : AdicOverBasePairLocallyFG I Y s t) :
    AdicOverBaseLocallyFG Y s := fun y =>
  let ⟨c, hfg, hl, _⟩ := h y
  ⟨c.R, c.commRing, c.topR, c.I, c.adic, c.map, hfg, c.mem, c.isOpenImmersion, hl⟩

/-- Forgetting the first bound. -/
theorem AdicOverBasePairLocallyFG.adicOverBase_right (h : AdicOverBasePairLocallyFG I Y s t) :
    AdicOverBaseLocallyFG Y t := fun y =>
  let ⟨c, hfg, _, hr⟩ := h y
  ⟨c.R, c.commRing, c.topR, c.I, c.adic, c.map, hfg, c.mem, c.isOpenImmersion, hr⟩

/-- **The one cheap sufficient condition: equal base morphisms.** If `s = t` a single
`AlgebraicGeometry.FormalScheme.AdicOverBaseLocallyFG` witness serves for both bounds.

This does *not* discharge the overlap condition below, and the module docstring says why: the two
base morphisms there are indeed equal, by
`AlgebraicGeometry.FormalScheme.OpenCover.pullback_fst_comp_eq_snd_comp`, but the only proof of
that equality on this tree consumes the very bounds the pair condition is supplying. -/
theorem AdicOverBaseLocallyFG.pair_of_eq (h : AdicOverBaseLocallyFG Y s) (hst : s = t) :
    AdicOverBasePairLocallyFG I Y s t := by
  subst hst
  intro y
  obtain ⟨S, _, _, J, _, f, hJfg, hmem, hoi, hadic⟩ := h y
  exact ⟨{ R := S, I := J, map := f, mem := hmem }, hJfg, hadic, hadic⟩

/-! ### The charts of both predicates really are a neighbourhood basis -/

section Refinement

variable {Y : FormalScheme.{u}}

section Sections

variable (ψ)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The chart-restriction of `ψ` along a basic-open refinement factors through the refinement.**
It is `FormalSpectrum.globalSectionsMap` of the basic-open chart, applied to the chart-restriction
along the original chart.

This is the `ψ`-relative counterpart of
`FormalSpectrum.le_comap_globalSectionsMap_basicOpenChart_comp`, which is what
`AlgebraicGeometry.FormalScheme.exists_affineChart_subset_adicOverBase` uses in the base-relative
case, and it is the only new algebra in this section. **It is not `rfl`**: the two
`FormalSpectrum.globalSectionsEquiv` round-trips cancel only propositionally. -/
theorem AffineChart.sectionsHom_basicOpenRefine {x : X} (c : AffineChart X x) (g : c.R)
    [IsAdicRing (awayCompletionIdeal c.I g)]
    [LocallyRingedSpace.IsOpenImmersion (basicOpenChart c.I g ≫ c.map)]
    (hmem : x ∈ Set.range (basicOpenChart c.I g ≫ c.map).base) :
    (c.basicOpenRefine g hmem).sectionsHom ψ =
      (globalSectionsMap c.I (awayCompletionIdeal c.I g)
        (basicOpenChart c.I g)).comp (c.sectionsHom ψ) := by
  change AffineChart.sectionsHom ψ
      ({ R := awayCompletion c.I g, I := awayCompletionIdeal c.I g,
         map := basicOpenChart c.I g ≫ c.map, mem := hmem } : AffineChart X x) = _
  ext a
  simp only [AffineChart.sectionsHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe, globalSectionsMap_apply, RingEquiv.symm_apply_apply,
    LocallyRingedSpace.comp_c_app]
  rfl

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The `ψ`-bound travels to the refinement.** Immediate from the factorisation above and
`FormalSpectrum.basicOpenChart_le_comap_globalSectionsMap`. -/
theorem AffineChart.le_comap_sectionsHom_basicOpenRefine {x : X} (c : AffineChart X x) (g : c.R)
    [IsAdicRing (awayCompletionIdeal c.I g)]
    [LocallyRingedSpace.IsOpenImmersion (basicOpenChart c.I g ≫ c.map)]
    (hmem : x ∈ Set.range (basicOpenChart c.I g ≫ c.map).base)
    (hc : I ≤ c.I.comap (c.sectionsHom ψ)) :
    I ≤ (c.basicOpenRefine g hmem).I.comap ((c.basicOpenRefine g hmem).sectionsHom ψ) := by
  rw [AffineChart.sectionsHom_basicOpenRefine]
  intro a ha
  simp only [Ideal.mem_comap]
  exact basicOpenChart_le_comap_globalSectionsMap c.I g (hc ha)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The charts of `AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG` are a neighbourhood
basis**: every point of an open `U` has a witness chart whose range is contained in `U`. This is
what the phrase "on a neighbourhood basis" in that predicate's own docstring refers to, and it is
the `ψ`-relative analogue of
`AlgebraicGeometry.FormalScheme.exists_affineChart_subset_adicOverBase`.

Without it the predicate could only be used at a point. A source that is an *open* of something
else — `AlgebraicGeometry.nodeChartSaturationFormalScheme` is
`AlgebraicGeometry.FormalScheme.restrictOpen` of the Tate chain — needs charts cut down into that
open before they are charts of the source at all, so this is the lemma any patch-by-patch check of
the predicate goes through. -/
theorem exists_affineChart_subset_adicSections (hX : AdicSectionsLocallyFG I ψ) (x : X)
    (U : Set X) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ c : AffineChart X x, c.I.FG ∧ Set.range c.map.base ⊆ U ∧
      I ≤ c.I.comap (c.sectionsHom ψ) := by
  obtain ⟨c, hfg, hcont⟩ := hX x
  obtain ⟨g, _, _, hmem, hsub⟩ := exists_basicOpenRefine_subset c hfg U hU hxU
  exact ⟨c.basicOpenRefine g hmem, awayCompletionIdeal_fg c.I g hfg, hsub,
    c.le_comap_sectionsHom_basicOpenRefine ψ g hmem hcont⟩

end Sections

section Pair

variable {s t : Y.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I}

/-- **A bound over one base morphism travels to a basic-open refinement.**
`FormalSpectrum.le_comap_globalSectionsMap_basicOpenChart_comp` after re-associating; the
refinement's structure morphism is the basic-open chart followed by the original one. -/
theorem AffineChart.le_comap_globalSectionsMap_basicOpenRefine {y : Y} (c : AffineChart Y y)
    (g : c.R) [IsAdicRing (awayCompletionIdeal c.I g)]
    [LocallyRingedSpace.IsOpenImmersion (basicOpenChart c.I g ≫ c.map)]
    (hmem : y ∈ Set.range (basicOpenChart c.I g ≫ c.map).base)
    (hc : I ≤ c.I.comap (globalSectionsMap I c.I (c.map ≫ s))) :
    I ≤ (c.basicOpenRefine g hmem).I.comap
      (globalSectionsMap I (c.basicOpenRefine g hmem).I
        ((c.basicOpenRefine g hmem).map ≫ s)) := by
  change I ≤ (awayCompletionIdeal c.I g).comap
    (globalSectionsMap I (awayCompletionIdeal c.I g) ((basicOpenChart c.I g ≫ c.map) ≫ s))
  rw [Category.assoc]
  exact le_comap_globalSectionsMap_basicOpenChart_comp I c.I g (c.map ≫ s) hc

/-- **The charts of `AlgebraicGeometry.FormalScheme.AdicOverBasePairLocallyFG` are a neighbourhood
basis too**, with *both* bounds surviving the shrink. This is what the phrase "on a neighbourhood
basis" in that predicate's docstring refers to.

**It does not settle the open question of this file's module docstring, and it sharpens it.** A
pair witness hands over one chart carrying both bounds, so
`FormalSpectrum.le_comap_globalSectionsMap_basicOpenChart_comp` applies to it twice along the
*same* `FormalSpectrum.basicOpenChart` — once with `c.map ≫ s`, once with `c.map ≫ t` — and
nothing about open immersions being adic on sections is needed. What is open is only the *merge*:
turning two separate `AlgebraicGeometry.FormalScheme.AdicOverBaseLocallyFG` witnesses, whose
charts are unrelated, into one pair witness. Refining a pair witness is free; producing one from
two singles is the question. -/
theorem exists_affineChart_subset_adicOverBasePair (h : AdicOverBasePairLocallyFG I Y s t) (y : Y)
    (U : Set Y) (hU : IsOpen U) (hyU : y ∈ U) :
    ∃ c : AffineChart Y y, c.I.FG ∧ Set.range c.map.base ⊆ U ∧
      I ≤ c.I.comap (globalSectionsMap I c.I (c.map ≫ s)) ∧
      I ≤ c.I.comap (globalSectionsMap I c.I (c.map ≫ t)) := by
  obtain ⟨c, hfg, hl, hr⟩ := h y
  obtain ⟨g, _, _, hmem, hsub⟩ := exists_basicOpenRefine_subset c hfg U hU hyU
  exact ⟨c.basicOpenRefine g hmem, awayCompletionIdeal_fg c.I g hfg, hsub,
    c.le_comap_globalSectionsMap_basicOpenRefine g hmem hl,
    c.le_comap_globalSectionsMap_basicOpenRefine g hmem hr⟩

end Pair

end Refinement

/-! ### The affine case, where a witness bottoms out -/

section Affine

variable {S : Type u} [CommRing S] [TopologicalSpace S] (J : Ideal S) [IsAdicRing J]

/-- **The identity chart on an affine formal scheme.** `AlgebraicGeometry.FormalScheme.Spf J` is
`FormalSpectrum.locallyRingedSpaceObj J` with an `AlgebraicGeometry.FormalScheme.local_affine`
field added, definitionally, so the identity morphism is an open immersion of the affine model onto
the whole of it, and is a chart at every point.

The `AlgebraicGeometry.FormalScheme.AffineChart.isOpenImmersion` field is supplied by an explicit
application rather than left to instance search: `IsIso (𝟙 _)` is not found by synthesis at this
position, and neither `haveI` nor `letI` ahead of the structure literal registers it — see the
implementation note. -/
def AffineChart.ofSpf (x : FormalScheme.Spf J) : AffineChart (FormalScheme.Spf J) x :=
  { R := S, I := J, map := 𝟙 _, mem := ⟨x, rfl⟩,
    isOpenImmersion :=
      @LocallyRingedSpace.IsOpenImmersion.of_isIso _ _ (𝟙 (locallyRingedSpaceObj J))
        (CategoryTheory.IsIso.id _) }

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The chart-restriction of `ψ` at the identity chart is `ψ` itself**, read through
`FormalSpectrum.globalSectionsEquiv`. So on an affine formal scheme the condition
`AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG` asks of a chart carries no chart-dependence
at all: it is the ordinary continuity of `ψ`. -/
theorem AffineChart.sectionsHom_ofSpf
    (ψ : R →+* (FormalScheme.Spf J).presheaf.obj (op (⊤ : Opens (FormalScheme.Spf J))))
    (x : FormalScheme.Spf J) :
    (AffineChart.ofSpf J x).sectionsHom ψ = (globalSectionsEquiv J).toRingHom.comp ψ := by
  ext a
  simp only [AffineChart.sectionsHom, AffineChart.ofSpf, RingEquiv.toRingHom_eq_coe]
  rfl

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **An affine formal scheme is adic over a continuous `ψ` on a neighbourhood basis**, with the
identity chart as the witness at every point. This is where a witness of
`AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG` bottoms out: a chart *is* an affine formal
spectrum, and on one the predicate is exactly continuity of `ψ`.

**It says nothing about any non-affine source**, and in particular nothing about
`AlgebraicGeometry.nodeChartSaturationFormalScheme`. What it does is exhibit the predicate as
satisfiable, which nothing on this tree previously did — a predicate with no known instance is
indistinguishable from a false one, and this one is neither. -/
theorem adicSectionsLocallyFG_Spf (hJ : J.FG)
    (ψ : R →+* (FormalScheme.Spf J).presheaf.obj (op (⊤ : Opens (FormalScheme.Spf J))))
    (hψ : I ≤ J.comap ((globalSectionsEquiv J).toRingHom.comp ψ)) :
    AdicSectionsLocallyFG I ψ := fun x =>
  ⟨AffineChart.ofSpf J x, hJ, by rw [AffineChart.sectionsHom_ofSpf]; exact hψ⟩

end Affine

/-! ### The construction -/

open OpenCover

variable (ψ)

/-- **The overlap condition**: on every pairwise overlap of the cover
`AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG` supplies, one witness adic over both of the
morphisms
`AlgebraicGeometry.FormalScheme.homOfGlobalSectionsHom` compares there.

Its two projections are that construction's `hf` and `hg`, and its chart family is the `ocharts`
they are stated at — so unlike `hf` and `hg` this condition never mentions a chart it did not
itself produce. -/
def AdicSectionsLocallyFG.OverlapAdic (hX : AdicSectionsLocallyFG I ψ) : Prop :=
  ∀ i j : X, AdicOverBasePairLocallyFG I (chartOverlap hX.chart hX.fg_chart i j)
    (pullback.fst ((ofAffineCharts hX.chart).cmap i) ((ofAffineCharts hX.chart).cmap j) ≫
      chartMap I hX.chart ψ i (hX.cont i))
    (pullback.snd ((ofAffineCharts hX.chart).cmap i) ((ofAffineCharts hX.chart).cmap j) ≫
      chartMap I hX.chart ψ j (hX.cont j))

variable (hX : AdicSectionsLocallyFG I ψ) (hI : I.FG) (hov : hX.OverlapAdic ψ)

/-- **The morphism `X ⟶ Spf R` induced by `ψ`, with no `hs`-shaped hypothesis.** Every one of
`AlgebraicGeometry.FormalScheme.homOfGlobalSectionsHom`'s nine arguments is supplied from the two
neighbourhood-basis witnesses: `charts`, `hfg`, `hcont` from
`AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG`, and `ocharts`, `hofg`, `hf`, `hg` from
`AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.OverlapAdic`, leaving only finite
generation of `I`.

This is not a claim that the witnesses exist. It is the statement that, once they do, no further
continuity condition is asked of a chart chosen by `Classical.choice`. -/
def homOfGlobalSectionsHomOfAdicSections : X.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I :=
  homOfGlobalSectionsHom I hX.chart hX.fg_chart ψ hX.cont hI
    (fun i j => (hov i j).chart) (fun i j x => (hov i j).fg_chart x)
    (fun i j x => (hov i j).left x) (fun i j x => (hov i j).right x)

/-- Its restriction to the chart at `x` is `Spf` of the chart-restriction of `ψ`. -/
theorem chart_comp_homOfGlobalSectionsHomOfAdicSections (x : X) :
    (hX.chart x).map ≫ homOfGlobalSectionsHomOfAdicSections ψ hX hI hov =
      chartMap I hX.chart ψ x (hX.cont x) :=
  chart_comp_homOfGlobalSectionsHom I hX.chart hX.fg_chart ψ hX.cont hI _ _ _ _ x

/-- **It induces `ψ` on global sections.** -/
theorem globalSectionsHom_homOfGlobalSectionsHomOfAdicSections :
    globalSectionsHom I X.toLocallyRingedSpace
        (homOfGlobalSectionsHomOfAdicSections ψ hX hI hov) = ψ :=
  globalSectionsHom_homOfGlobalSectionsHom I hX.chart hX.fg_chart ψ hX.cont hI _ _ _ _

/-- **It is itself continuous on each of the charts the witness supplied**, so the `∃!` below is
not vacuous. -/
theorem continuous_homOfGlobalSectionsHomOfAdicSections (x : X) :
    I ≤ (hX.chart x).I.comap (globalSectionsMap I (hX.chart x).I
      ((hX.chart x).map ≫ homOfGlobalSectionsHomOfAdicSections ψ hX hI hov)) :=
  continuous_homOfGlobalSectionsHom I hX.chart hX.fg_chart ψ hX.cont hI _ _ _ _ x

/-- **The construction does not depend on the overlap data that discharged the agreement.** Any
`ocharts`/`hofg`/`hf`/`hg` whatever, at the same chart family and the same `hcont`, build the same
morphism.

This is `AlgebraicGeometry.FormalScheme.hom_ext_of_chart_comp`: both sides restrict, on the chart
at each `x`, to `AlgebraicGeometry.FormalScheme.chartMap` of the chart-restriction of `ψ` there,
and a morphism into a formal spectrum is determined by those restrictions. So the overlap witness
is used only to *build* the morphism, never to pin it down — in particular a caller who already
has an overlap cover with the two continuity families gets the same morphism as this file's, and
neither construction is more canonical than the other. -/
theorem homOfGlobalSectionsHomOfAdicSections_eq
    (ocharts : ∀ i j, ∀ x : chartOverlap hX.chart hX.fg_chart i j,
      AffineChart (chartOverlap hX.chart hX.fg_chart i j) x)
    (hofg : ∀ i j x, (ocharts i j x).I.FG)
    (hf : ∀ i j, ∀ x : chartOverlap hX.chart hX.fg_chart i j,
      I ≤ (ocharts i j x).I.comap (globalSectionsMap I (ocharts i j x).I
        ((ocharts i j x).map ≫
          pullback.fst ((ofAffineCharts hX.chart).cmap i) ((ofAffineCharts hX.chart).cmap j) ≫
            chartMap I hX.chart ψ i (hX.cont i))))
    (hg : ∀ i j, ∀ x : chartOverlap hX.chart hX.fg_chart i j,
      I ≤ (ocharts i j x).I.comap (globalSectionsMap I (ocharts i j x).I
        ((ocharts i j x).map ≫
          pullback.snd ((ofAffineCharts hX.chart).cmap i) ((ofAffineCharts hX.chart).cmap j) ≫
            chartMap I hX.chart ψ j (hX.cont j)))) :
    homOfGlobalSectionsHomOfAdicSections ψ hX hI hov =
      homOfGlobalSectionsHom I hX.chart hX.fg_chart ψ hX.cont hI ocharts hofg hf hg :=
  hom_ext_of_chart_comp I hX.chart _ _ fun x => by
    rw [chart_comp_homOfGlobalSectionsHomOfAdicSections ψ hX hI hov x,
      chart_comp_homOfGlobalSectionsHom I hX.chart hX.fg_chart ψ hX.cont hI ocharts hofg hf hg x]

include hI hov in
/-- **EGA I, 10.4.6 over a source adic over `ψ`.** The form of
`AlgebraicGeometry.FormalScheme.existsUnique_globalSectionsHom_eq` in which no continuity family is
a hypothesis: all three come from the two witnesses.

The quantifier still ranges over the continuity-restricted subtype, and that restriction is still
genuine — see the scope note of `FormalSchemes.GlobalSectionsHomGlue`. -/
theorem existsUnique_globalSectionsHom_eq_of_adicSections :
    ∃! f : { f : X.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I //
        ∀ x : X, I ≤ (hX.chart x).I.comap
          (globalSectionsMap I (hX.chart x).I ((hX.chart x).map ≫ f)) },
      globalSectionsHom I X.toLocallyRingedSpace f.1 = ψ :=
  existsUnique_globalSectionsHom_eq I hX.chart hX.fg_chart ψ hX.cont hI
    (fun i j => (hov i j).chart) (fun i j x => (hov i j).fg_chart x)
    (fun i j x => (hov i j).left x) (fun i j x => (hov i j).right x)

/-- **The two routes build the same morphism.** A caller who *also* has the three continuity
families at the canonical overlap charts — that is, an
`AlgebraicGeometry.FormalScheme.SpfHomContinuity` (`FormalSchemes.GlueHomToSpf`) at the family
this witness supplies — gets from that bundle the morphism this file builds from the overlap
witness, and not a second one.

It is an instance of
`AlgebraicGeometry.FormalScheme.homOfGlobalSectionsHomOfAdicSections_eq` at
`AlgebraicGeometry.FormalScheme.overlapChartOf`. The two continuity proofs involved,
`AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.cont` and
`AlgebraicGeometry.FormalScheme.SpfHomContinuity.cont`, are
proofs of the same `Prop` and so are interchangeable by definitional proof irrelevance; no
transport appears.

**The converse fails on this tree**, and the module docstring says where: see the paragraph on the
overlap condition below. -/
theorem homOfGlobalSectionsHomOfAdicSections_eq_homOfSpfHomContinuity
    (d : FormalScheme.SpfHomContinuity I hX.chart hX.fg_chart ψ) :
    homOfGlobalSectionsHomOfAdicSections ψ hX hI hov =
      homOfSpfHomContinuity I hX.chart hX.fg_chart ψ hI d :=
  homOfGlobalSectionsHomOfAdicSections_eq ψ hX hI hov
    (overlapChartOf hX.chart hX.fg_chart) (fg_overlapChartOf hX.chart hX.fg_chart) d.fst d.snd

end AlgebraicGeometry.FormalScheme

end
