import FormalSchemes.ChartSpfHomOverlap
import FormalSchemes.SpfBasicOpenCover
import FormalSchemes.LocallyRingedSpaceHomExt
import FormalSchemes.BasicOpenChartOverlapLegs
import FormalSchemes.ThickeningBasicOpenRefinement

set_option linter.style.header false

/-!
# `Spf R` is the colimit of its infinitesimal thickenings (EGA I, 10.6.10)

For a locally ringed space `X` covered by affine opens, a **compatible family** of morphisms
`f n : Spec (R ⧸ Iⁿ⁺¹) ⟶ X` comes from a **unique** morphism `Spf R ⟶ X`
(`FormalSpectrum.existsUnique_hom_thickeningMap`). This closes umbrella 59.

```
Hom(Spf R, X)  ≃  lim  Hom(Spec (R ⧸ Iⁿ⁺¹), X)
```

The affine-target case is `IndScheme.lean`'s `thickeningRestrictionEquiv`; what this file adds is
the general target, by descent along a cover of the *source*.

## The route, and where each step already lived

*Cover `X` by affines → pull the cover back to `|Spf R|` → refine by basic opens `D(r)` → run the
affine case on each chart → glue.* The first four steps are landed and none of them is redone here:

| step | module |
| :-- | :-- |
| pull back and refine by basic opens | `ThickeningBasicOpenRefinement.lean` |
| the chart of a thickening over `D(r)` is affine | `ThickeningChartAffine.lean` |
| the affine case on a chart: `chartSpfHomAmbient : Spf R{1/r} ⟶ X` | `ThickeningChartSpfHom.lean` |
| it does not depend on the affine chart it was built from | `ChartSpfHomIndep.lean` |
| the chart morphisms agree on the overlap `D(r·s)` | `ChartSpfHomOverlap.lean` |

This file is the fifth step. It has three parts.

1. **The cover.** `SpfBasicOpenCover.lean` presents `Spf R` as an `OpenCover` by the charts
   `Spf R{1/r i}` of a covering family of elements.
2. **The gluing.** `chartHom_pullback_compat` converts `chartSpfHomAmbient_overlap`, which is
   stated along the two *legs* of the overlap, into the *pullback* form `glueMorphisms` takes;
   the bridge is `basicOpenChartOverlapIso_inv_comp_furtherLeft`/`_furtherRight`, which
   `BasicOpenChartOverlapLegs.lean` proved for exactly this. The `Left` half already has a
   consumer in the same shape: `GeneralFibreProductExposeXAlgebraData.lean` rewrites a
   `pullback.fst` by it in its `hfst` step.
   `spfHomOfFamily` is then `OpenCover.glueMorphisms` of the chart morphisms.
3. **The computation rule**, `thickeningMap_comp_spfHomOfFamily`, which is the part that makes
   this a theorem rather than a definition — see below. Uniqueness is free from
   `hom_ext_thickeningMap_lrs` (`ThickeningHomExt.lean`).

## Why the computation rule is not a corollary of `map_glueMorphisms`

`map_glueMorphisms` pins the restrictions of the glued morphism **to the charts of the cover of
`Spf R`**. The computation rule is an equation between morphisms out of a **thickening**
`Spec (R ⧸ Iⁿ⁺¹)`, which is a different space, and it has to be checked one chart at a time:

* the charts `chartOpen I (r i) n` cover the thickening (`iSup_chartOpen_eq_top`), because the base
  map of `thickeningMap` is a homeomorphism carrying `D(r)` to `chartOpen I r n`;
* on each of them, `thickeningMap_comp_basicOpenChart` (new here — `thickeningMap` naturality
  against `chartRingMap_eq_levelRingHom`) rewrites the chart embedding into a restriction of
  `basicOpenChart`, after which `map_glueMorphisms` and
  `thickeningMap_comp_chartSpfHomAmbient` apply;
* "morphisms of locally ringed spaces agreeing on an open cover of the source are equal" is
  `LocallyRingedSpaceHomExt.lean`, added by this row because neither `OpenCover.hom_ext` (whose
  source must be a formal scheme) nor `hom_ext_thickeningMap_lrs` (whose source must be `Spf R`)
  covers a bare thickening.

## Main definitions and results

* `FormalSpectrum.thickeningMap_comp_basicOpenChart`: the basic-open chart restricted to a
  thickening is the chart embedding.
* `FormalSpectrum.chartHom_pullback_compat`: the overlap agreement in pullback form.
* `FormalSpectrum.spfHomOfFamily`: **the morphism `Spf R ⟶ X`**, with
  `FormalSpectrum.thickeningMap_comp_spfHomOfFamily` and `FormalSpectrum.spfHomOfFamily_uniq`.
* `FormalSpectrum.existsUnique_hom_thickeningMap`: **EGA I, 10.6.10**, with the chart data
  discharged from an affine open cover of `X`.
* `FormalSpectrum.spfHomFormalLine`: the witness — `Spf ℤ⟦X⟧ ⟶ Spec ℤ` glued from two charts.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6 (10.6.10), §10.8.
* [The Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable {X : LocallyRingedSpace.{u}}
variable (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X)
    (hf : ∀ n : ℕ, Spec.locallyRingedSpaceMap (stepRingHom I n) ≫ f (n + 1) = f n)

section ChartTower

variable (r : R) (hI : I.FG) [IsAdicRing (awayCompletionIdeal I r)]

omit [TopologicalSpace R] [IsAdicRing I] [IsAdicRing (awayCompletionIdeal I r)] in
/-- **The basic-open chart, restricted to the `n`-th thickening.** `basicOpenChart` is `Spf` of the
structural map `R → R{1/r}`, so `thickeningMap` naturality turns its restriction into `Spec` of the
level-`n` descent of that map — and `chartRingMap_eq_levelRingHom` says that descent is the chart
ring map, whose `Spec` is the chart embedding. -/
@[reassoc]
theorem thickeningMap_comp_basicOpenChart (n : ℕ) :
    thickeningMap (awayCompletionIdeal I r) n ≫ basicOpenChart I r =
      (chartIsoLRS I r hI n).inv ≫
        (Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1)))).ofRestrict
          (chartOpen I r n).isOpenEmbedding ≫ thickeningMap I n := by
  rw [basicOpenChart, thickeningMap_comp_locallyRingedSpaceMap, ← chartRingMap_eq_levelRingHom,
    ← chartIsoLRS_inv_comp_ofRestrict, Category.assoc]

end ChartTower

section Glue

variable (hI : I.FG) {ι : Type u} (r : ι → R)
    [∀ i, IsAdicRing (awayCompletionIdeal I (r i))]
    (hcov : (⨆ i, basicOpen I (r i)) = ⊤)
    (U : ι → Opens X.toTopCat)
    (hr : ∀ i, basicOpen I (r i) ≤ (Opens.map (commonBase I f)).obj (U i))
    (B : ι → Type u) [∀ i, CommRing (B i)]
    (e : ∀ i, X.restrict (U i).isOpenEmbedding ≅
      Spec.locallyRingedSpaceObj (CommRingCat.of (B i)))

/-- The morphism attached to the chart `D(r i)` by the affine case (issue 1062), abbreviated. -/
def chartHom (i : ι) : locallyRingedSpaceObj (awayCompletionIdeal I (r i)) ⟶ X :=
  chartSpfHomAmbient I f hf (U i) (r i) (hr i) hI (B i) (e i)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The chart morphisms agree on the pullbacks of the cover**, which is the hypothesis
`glueMorphisms` takes. This is `chartSpfHomAmbient_overlap` — stated along the two *legs*
`Spf R{1/(r i · r j)} ⟶ Spf R{1/r i}`, `⟶ Spf R{1/r j}` — transported to the two pullback
projections by the leg identifications of `BasicOpenChartOverlapLegs.lean`, which were built for
exactly this. The manoeuvre has a worked precedent one file away —
`GeneralFibreProductExposeXAlgebraData.lean` rewrites `pullback.fst` by
`basicOpenChartOverlapIso_inv_comp_furtherLeft` in its `hfst` step — and it is the `Right` half
that is used here for the first time. The transport is a cancellation of an isomorphism, not a
transport of a statement across one. -/
theorem chartHom_pullback_compat (i j : ι) :
    letI := isOpenImmersion_basicOpenChart I (r i) hI
    letI := isOpenImmersion_basicOpenChart I (r j) hI
    pullback.fst (basicOpenChart I (r i)) (basicOpenChart I (r j)) ≫
        chartHom I f hf hI r U hr B e i =
      pullback.snd (basicOpenChart I (r i)) (basicOpenChart I (r j)) ≫
        chartHom I f hf hI r U hr B e j := by
  letI := isOpenImmersion_basicOpenChart I (r i) hI
  letI := isOpenImmersion_basicOpenChart I (r j) hI
  rw [← basicOpenChartOverlapIso_inv_comp_furtherLeft I (r i) (r j) hI,
    ← basicOpenChartOverlapIso_inv_comp_furtherRight I (r i) (r j) hI,
    Category.assoc, Category.assoc, chartHom, chartHom,
    chartSpfHomAmbient_overlap I f hf (r i) (r j) hI (U i) (hr i) (B i) (e i) (U j) (hr j) (B j)
      (e j)]

/-- **The morphism `Spf R ⟶ X` glued from the chart morphisms** (EGA I, 10.6.10). Cite
`thickeningMap_comp_spfHomOfFamily` and `spfHomOfFamily_uniq` rather than unfolding this. -/
def spfHomOfFamily : locallyRingedSpaceObj I ⟶ X :=
  (basicOpenCover I r hI hcov).glueMorphisms (chartHom I f hf hI r U hr B e)
    (fun i j => chartHom_pullback_compat I f hf hI r U hr B e i j)

omit [TopologicalSpace R] [IsAdicRing I] [∀ i, IsAdicRing (awayCompletionIdeal I (r i))] in
include hcov in
/-- **The charts of a covering family cover every thickening.** The base map of `thickeningMap` is
a homeomorphism, and `chartOpen I r n` is where `D(r)` goes under it (`thickeningOpen_basicOpen`),
so a family of basic opens covering `|Spf R|` has charts covering `Spec (R ⧸ Iⁿ⁺¹)` at every
level. -/
theorem iSup_chartOpen_eq_top (n : ℕ) : (⨆ i, chartOpen I (r i) n) = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  obtain ⟨i, hi⟩ := exists_mem_basicOpen_of_iSup_eq_top I r hcov ((thickeningTopIso I n).inv y)
  refine Opens.mem_iSup.mpr ⟨i, ?_⟩
  have hy : y ∈ thickeningOpen I n (basicOpen I (r i)) := hi
  rwa [thickeningOpen_basicOpen] at hy

set_option linter.style.setOption false in
-- The cover of the thickening is given by `chartOpen`, which is stated about the *scheme*
-- `Spec (CommRingCat.of _)`, while `thickeningMap` and the joint-epi lemma are stated about
-- `Spec.locallyRingedSpaceObj (CommRingCat.of _)`. The two are `rfl` but not at `instances`
-- transparency; same accommodation as `ThickeningChartSpfHom.lean`'s.
set_option backward.isDefEq.respectTransparency false in
/-- **The computation rule** (EGA I, 10.6.10): the glued morphism restricts on the `n`-th
thickening to the `n`-th member of the family it was built from.

This is not a corollary of `map_glueMorphisms`, which only pins the restrictions of the glued
morphism to the *charts*; the equation here is between morphisms out of the thickening, and is
checked one chart at a time. The chart of `D(r i)` inside the thickening is where
`thickeningMap_comp_basicOpenChart` and `thickeningMap_comp_chartSpfHomAmbient` meet, and the
charts cover the thickening by `iSup_chartOpen_eq_top`. -/
theorem thickeningMap_comp_spfHomOfFamily (n : ℕ) :
    thickeningMap I n ≫ spfHomOfFamily I f hf hI r hcov U hr B e = f n := by
  refine LocallyRingedSpace.hom_ext_of_iSup_eq_top
    (Z := Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))))
    (fun i => chartOpen I (r i) n) (iSup_chartOpen_eq_top I r hcov n) fun i => ?_
  refine (Iso.cancel_iso_inv_left (chartIsoLRS I (r i) hI n) _ _).mp ?_
  rw [← thickeningMap_comp_basicOpenChart_assoc, ← basicOpenCover_cmap I r hI hcov i,
    spfHomOfFamily, FormalScheme.OpenCover.map_glueMorphisms, chartHom,
    thickeningMap_comp_chartSpfHomAmbient]

/-- **…and it is the only morphism with those restrictions.** Free from `hom_ext_thickeningMap_lrs`
(issue 1064): the thickenings of `Spf R` are jointly epimorphic. -/
theorem spfHomOfFamily_uniq (g : locallyRingedSpaceObj I ⟶ X)
    (hg : ∀ n : ℕ, thickeningMap I n ≫ g = f n) :
    g = spfHomOfFamily I f hf hI r hcov U hr B e :=
  hom_ext_thickeningMap_lrs _ _ fun n =>
    (hg n).trans (thickeningMap_comp_spfHomOfFamily I f hf hI r hcov U hr B e n).symm

end Glue

/-!
### EGA I, 10.6.10

With the refinement of `ThickeningBasicOpenRefinement.lean` in hand, none of the chart data has to
be supplied by the caller: an affine open cover of `X` is enough.
-/

section Capstone

variable (hI : I.FG) {ι : Type u} (U : ι → Opens X.toTopCat) (hU : ⨆ i, U i = ⊤)
    (B : ι → Type u) [∀ i, CommRing (B i)]
    (e : ∀ i, X.restrict (U i).isOpenEmbedding ≅
      Spec.locallyRingedSpaceObj (CommRingCat.of (B i)))

include hf hI hU B e in
/-- **`Spf R` is the colimit of its infinitesimal thickenings** (EGA I, 10.6.10): a compatible
family of morphisms `Spec (R ⧸ Iⁿ⁺¹) ⟶ X` comes from a unique morphism `Spf R ⟶ X`.

The hypotheses on `X` are exactly: it is a locally ringed space, and it carries a cover by opens
`U i` each *equipped* with an identification `X|_{U i} ≅ Spec (B i)`. The identifications are data
rather than a property because `X` is a bare locally ringed space, so `IsAffineOpen` is not
available; a scheme supplies them from its own affine cover, and
`FormalSchemes/SpfHomScheme.lean` does exactly that — `existsUnique_hom_thickeningMap_scheme`
is this theorem with `U`, `hU`, `B` and `e` read off `Scheme.local_affine`, leaving `hI` as the
only hypothesis.

The proof supplies the gluing data of `spfHomOfFamily` from `exists_basicOpen_refinement`: one
basic open `D(r x)` through each point of `|Spf R|`, chosen inside the pullback of some `U i`. -/
theorem existsUnique_hom_thickeningMap :
    ∃! g : locallyRingedSpaceObj I ⟶ X, ∀ n : ℕ, thickeningMap I n ≫ g = f n := by
  obtain ⟨r, idx, hcov, hle⟩ := exists_basicOpen_refinement I f U hU
  haveI hadic : ∀ x : FormalSpectrum I, IsAdicRing (awayCompletionIdeal I (r x)) := fun x =>
    isAdicRing_awayCompletionIdeal I (r x) hI
  refine ⟨spfHomOfFamily I f hf hI r hcov (fun x => U (idx x)) hle (fun x => B (idx x))
      (fun x => e (idx x)), fun n => ?_, fun g hg => ?_⟩
  · exact thickeningMap_comp_spfHomOfFamily I f hf hI r hcov _ hle _ _ n
  · exact spfHomOfFamily_uniq I f hf hI r hcov _ hle _ _ g hg

end Capstone

/-!
### Non-vacuity

The construction above is run end to end at `FormalLineWitness.lean`'s formal affine line
`ℤ⟦X⟧ = ℤ[X]^{(X)}`, whose formal spectrum is `Spec ℤ`, with the two-piece cover `D(2)`, `D(3)`.
Everything the general theorem quantifies over is non-degenerate there:

* the ideal is not `⊥`: `formalLineIdeal ≠ ⊥` (`formalLineIdeal_ne_bot`,
  `FormalLineWitness.lean`), so the tower of thickenings `Spec (ℤ⟦X⟧ ⧸ Iⁿ⁺¹)` is not constant;
* the space is not a point: `|Spf ℤ⟦X⟧| ≃ₜ Spec ℤ` (`homeoSpecInt`) has at least two points,
  namely the primes above `2` and above `3` (`nontrivial_formalSpectrum`, `FormalLineWitness.lean`)
  — which is exactly what the `2`-adic witness makes false, and the reason this one exists;
* the cover has **two distinct pieces** (`twoChart_ne`, `FormalLineTwoChartCover.lean`), they
  genuinely cover (`iSup_twoChart`), and neither is the whole space (`twoChart_ne_top`);
* the pieces **overlap**: `D(2) ⊓ D(3) ≠ ⊥` (`twoChart_inf_ne_bot`), `D(2·3)` is neither `⊥` nor
  `⊤`, and neither is its chart at any level of the tower
  (`basicOpen_formalLine_overlap_ne_bot`, `chartOpen_formalLine_overlap_ne_top`,
  `ChartSpfHomOverlap.lean`) — so the compatibility hypothesis discharged by
  `chartHom_pullback_compat` is a condition over a nonempty formal scheme, not a vacuous one;
* the two affine opens of the target are **different and proper**: `D(2)`, `D(3) ⊆ Spec ℤ` are
  distinct opens (`formalLineOpen_ne`, the target-side counterpart of `twoChart_ne`), each is
  proper and nonempty (`openTwo_ne_top`, `openThree_ne_top` and their `_ne_bot` companions), and
  their coordinate rings `ℤ[1/2]`, `ℤ[1/3]` are different rings. In particular `U = ⊤` is
  excluded on both sides.

The `X` of this witness is affine, and for a while that was true of every witness on the tree —
four rows on this umbrella recorded it as an open gap. It is closed in
`FormalSchemes/SpfHomNonAffineWitness.lean`, which runs `existsUnique_hom_thickeningMap` at the
affine line over `ℤ` with a doubled origin, covered by its two charts: a target that
`FormalSchemes/SpecTwoPatchNonAffine.lean` proves is **not affine**. It never bore on non-vacuity
of anything proved here — the construction never looks at `X` outside the chart opens, and the
gluing above happens on the *source*, where the two-piece cover is genuinely two-piece — but
**together** the two witnesses exercise the covering situation on both sides at once. Neither does
alone: `existsUnique_hom_thickeningMap_formalLine` and `existsUnique_hom_thickeningMap_nonAffine`
both take a cover of the target only, and obtain their source data inside from
`exists_basicOpen_refinement`, so in each of them it may be a single piece. The source-side half is
carried by `spfHomFormalLine` below, which calls `spfHomOfFamily` directly with `formalLineElem`,
`iSup_basicOpen_formalLineElem` and `formalLine_hr` supplied by hand; the target-side half is
carried by the non-affine witness.

The first bullet is the youngest, and it is worth saying why. `[IsAdicRing I]` does **not**
exclude `I = ⊥`: at `⊥` the class degenerates to discreteness of `R` (`is_bot_adic_iff`, the whole
content of `instIsAdicRingBotOfDiscreteTopology`, `FormalSchemes/AdicRing.lean`), and every
thickening `Spec (R ⧸ Iⁿ⁺¹)` is `Spec R`. For a while the list above established non-degeneracy of
the two covers and of the space but *not* of the ideal, and said so. `formalLineIdeal_ne_bot`
closes that, so the whole list now names theorems.
-/

section Witness

open Polynomial

attribute [local instance] isAdicRing_formalLineIdeal

/-- The two elements `2`, `3` of `ℤ⟦X⟧`, spelled exactly as `FormalLineWitness.lean`'s `twoChart`
spells them so that `iSup_twoChart` applies on the nose. -/
def formalLineElem : Bool → AdicCompletion polyXIdeal ℤ[X] := fun b => if b then 2 else 3

theorem isAdicRing_awayCompletionIdeal_formalLineElem (b : Bool) :
    IsAdicRing (awayCompletionIdeal formalLineIdeal (formalLineElem b)) :=
  isAdicRing_awayCompletionIdeal _ _ (polyXIdeal_fg.map _)

attribute [local instance] isAdicRing_awayCompletionIdeal_formalLineElem

/-- **`D(2)` and `D(3)` cover `|Spf ℤ⟦X⟧|`**, in the form the gluing takes its covering hypothesis
in. This is `iSup_twoChart`. -/
theorem iSup_basicOpen_formalLineElem :
    (⨆ b, basicOpen formalLineIdeal (formalLineElem b)) = ⊤ :=
  iSup_twoChart

/-- The two affine opens `D(2)`, `D(3)` of the target `Spec ℤ`. -/
def formalLineOpen : Bool → Opens witnessTarget.toTopCat :=
  fun b => if b then openTwo else openThree

/-- **The two affine opens of the target are distinct.** The prime `(2) ⊆ ℤ` lies outside `D(2)`
and inside `D(3)`, since `2 ∤ 3`. This is the target-side counterpart of `twoChart_ne`
(`FormalSchemes/FormalLineTwoChartCover.lean`), which says the same of the two opens of the
*source*: without it the non-vacuity claim below would be reading distinctness off the two
coordinate rings, which is not the same statement. -/
theorem formalLineOpen_ne : formalLineOpen true ≠ formalLineOpen false := by
  haveI := Int.span_two_isMaximal
  have hnot : (⟨Ideal.span {(2 : ℤ)}, inferInstance⟩ : PrimeSpectrum ℤ) ∉ formalLineOpen true := by
    rw [formalLineOpen, if_pos rfl]
    exact fun hc => hc (Ideal.mem_span_singleton_self _)
  have hmem : (⟨Ideal.span {(2 : ℤ)}, inferInstance⟩ : PrimeSpectrum ℤ) ∈ formalLineOpen false := by
    rw [formalLineOpen, if_neg (by simp)]
    intro hc
    have h23 : (2 : ℤ) ∣ 3 := Ideal.mem_span_singleton.mp hc
    norm_num at h23
  intro h
  rw [h] at hnot
  exact hnot hmem

/-- Their coordinate rings, `ℤ[1/2]` and `ℤ[1/3]` — genuinely different rings, which is what makes
the two chart morphisms being glued unrelated except through the family. -/
def formalLineChartRing : Bool → Type := fun b =>
  if b then Localization.Away (2 : ℤ) else Localization.Away (3 : ℤ)

instance (b : Bool) : CommRing (formalLineChartRing b) := by
  cases b <;> exact inferInstanceAs (CommRing (Localization.Away _))

/-- The refinement hypothesis at both charts: `witness_hr_two` and `witness_hr_three`. -/
theorem formalLine_hr (b : Bool) :
    basicOpen formalLineIdeal (formalLineElem b) ≤
      (Opens.map (commonBase formalLineIdeal witnessFamily.1)).obj (formalLineOpen b) := by
  cases b with
  | true => exact witness_hr_two
  | false => exact witness_hr_three

/-- The affine identifications of the two target opens, from `basicOpenIsoSpecAway`. -/
def formalLineChartIso (b : Bool) :
    witnessTarget.restrict (formalLineOpen b).isOpenEmbedding ≅
      Spec.locallyRingedSpaceObj (CommRingCat.of (formalLineChartRing b)) := by
  cases b with
  | true => exact openTwoIsoSpecLRS
  | false => exact openThreeIsoSpecLRS

/-- **The glued morphism `Spf ℤ⟦X⟧ ⟶ Spec ℤ`**, assembled from the two chart morphisms over `D(2)`
and `D(3)` — the general construction run on a cover with two distinct pieces, nonempty overlap,
and two different affine opens of the target. -/
def spfHomFormalLine : locallyRingedSpaceObj formalLineIdeal ⟶ witnessTarget :=
  spfHomOfFamily formalLineIdeal witnessFamily.1 witnessFamily.2 (polyXIdeal_fg.map _)
    formalLineElem iSup_basicOpen_formalLineElem formalLineOpen formalLine_hr formalLineChartRing
    formalLineChartIso

/-- **The computation rule at the witness**: the glued morphism restricts on every thickening of
`Spf ℤ⟦X⟧` to the corresponding member of the witness family. -/
theorem thickeningMap_comp_spfHomFormalLine (n : ℕ) :
    thickeningMap formalLineIdeal n ≫ spfHomFormalLine = witnessFamily.1 n :=
  thickeningMap_comp_spfHomOfFamily formalLineIdeal witnessFamily.1 witnessFamily.2
    (polyXIdeal_fg.map _) formalLineElem iSup_basicOpen_formalLineElem formalLineOpen
    formalLine_hr formalLineChartRing formalLineChartIso n

/-- **`D(2)` and `D(3)` cover the target `Spec ℤ` as well**: a prime containing both `2` and `3`
would contain `3 - 2 = 1`. This is the hypothesis the capstone takes in place of the chart data —
an affine open cover of `X`, and nothing else. -/
theorem iSup_formalLineOpen : (⨆ b, formalLineOpen b) = ⊤ := by
  rw [eq_top_iff]
  rintro p -
  refine Opens.mem_iSup.mpr ?_
  by_contra hcon
  have hnot : ∀ b, p ∉ formalLineOpen b := fun b hb => hcon ⟨b, hb⟩
  have h2 : (2 : ℤ) ∈ p.asIdeal := by
    have h := hnot true
    rw [formalLineOpen, if_pos rfl] at h
    exact not_not.mp h
  have h3 : (3 : ℤ) ∈ p.asIdeal := by
    have h := hnot false
    rw [formalLineOpen, if_neg (by simp)] at h
    exact not_not.mp h
  refine p.asIdeal.ne_top_iff_one.mp p.isPrime.ne_top ?_
  have hone : (1 : ℤ) = 3 - 2 := by norm_num
  rw [hone]
  exact sub_mem h3 h2

/-- **EGA I, 10.6.10 at the witness.** The capstone itself, instantiated: `Spec ℤ` covered by the
two proper affine opens `D(2)`, `D(3)`, and the witness family on the thickenings of `Spf ℤ⟦X⟧`.
Nothing but the cover of the target is supplied — the elements `2`, `3` of `ℤ⟦X⟧`, the index map
and the containments are produced inside by `exists_basicOpen_refinement`, so this exercises the
refinement step as well as the gluing. -/
theorem existsUnique_hom_thickeningMap_formalLine :
    ∃! g : locallyRingedSpaceObj formalLineIdeal ⟶ witnessTarget,
      ∀ n : ℕ, thickeningMap formalLineIdeal n ≫ g = witnessFamily.1 n :=
  existsUnique_hom_thickeningMap formalLineIdeal witnessFamily.1 witnessFamily.2
    (polyXIdeal_fg.map _) formalLineOpen iSup_formalLineOpen formalLineChartRing formalLineChartIso

/-- …and it is the only morphism `Spf ℤ⟦X⟧ ⟶ Spec ℤ` that does. -/
theorem spfHomFormalLine_uniq (g : locallyRingedSpaceObj formalLineIdeal ⟶ witnessTarget)
    (hg : ∀ n : ℕ, thickeningMap formalLineIdeal n ≫ g = witnessFamily.1 n) :
    g = spfHomFormalLine :=
  spfHomOfFamily_uniq formalLineIdeal witnessFamily.1 witnessFamily.2 (polyXIdeal_fg.map _)
    formalLineElem iSup_basicOpen_formalLineElem formalLineOpen formalLine_hr formalLineChartRing
    formalLineChartIso g hg

end Witness

end FormalSpectrum

end
