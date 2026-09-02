import FormalSchemes.ChartSpfHomColimitTarget
import FormalSchemes.SpfHomOfFamily
import FormalSchemes.OpenImmersionIsoOfRangeEq

set_option linter.style.header false

/-!
# EGA I, 10.6.10 at a cover that need not be affine, and the locality of the colimit property

`FormalSchemes/SpfHomOfFamily.lean` proves that a compatible family
`f n : Spec (R ⧸ Iⁿ⁺¹) ⟶ X` comes from a unique `Spf R ⟶ X` when `X` carries a cover by opens
`U i` equipped with identifications `X|_{U i} ≅ Spec (B i)`. The affineness of the cover enters
that proof at exactly one place, and `FormalSchemes/ChartSpfHomColimitTarget.lean` isolates it: the
chart morphism `Spf R{1/r} ⟶ X` needs its chart to satisfy
`FormalSpectrum.IsThickeningColimitTarget`, and nothing else in the chain looks at the chart at
all.

This file runs the gluing step at that hypothesis. The result is the statement the chain was
always proving:

```lean
FormalSpectrum.isThickeningColimitTarget_of_cover :
  (⨆ i, U i = ⊤) → (∀ i, X|_{U i} ≅ Y i) → (∀ i, IsThickeningColimitTarget (Y i)) →
    IsThickeningColimitTarget X
```

**the colimit property of formal spectra is local on the target.** The affine-target theorem of
umbrella 59 and the formal-affine-target theorem of issue 62m are the two ways of starting it, and
`existsUnique_hom_thickeningMap_spfCover` — EGA I 10.6.10 with the target covered by *formal*
affines, which is what issue 62m is for — is the second of them run through this file.

## What is new and what is transported

Nothing here is new mathematics. `chartHom_pullback_compat`, `spfHomOfFamily`,
`thickeningMap_comp_spfHomOfFamily` and `existsUnique_hom_thickeningMap` are
`SpfHomOfFamily.lean`'s, with `(B i, e i)` replaced by `(Y i, e i, hY i)` and the proofs unchanged;
`iSup_chartOpen_eq_top` and `thickeningMap_comp_basicOpenChart` are *cited* from there rather than
restated, because they never mentioned the cover of the target in the first place.

The one thing that has to be proved rather than transported is that the two entry points agree,
and that is `ColimitTarget.chartSpfHomAmbient_eq`, one file back.

## Main results

* `FormalSpectrum.ColimitTarget.existsUnique_hom_thickeningMap`: EGA I 10.6.10 at a cover by
  targets of the colimit property.
* `FormalSpectrum.isThickeningColimitTarget_of_cover`: the property is local on the target.
* `FormalSpectrum.existsUnique_hom_thickeningMap_spfCover`: EGA I 10.6.10 with the target covered
  by **formal** affines — issue 62m. (`existsUnique_hom_thickeningMap_spf`, one file back, is the
  *affine* formal target; this is the covered one.)
* `FormalSpectrum.thickeningRestrictionEquivSpfCover`: the same, as a bijection.

## Non-vacuity

`Spf ℤ⟦X⟧` — whose underlying space is `Spec ℤ` — is covered by the two **formal** affine opens
`D(2)` and `D(3)`, which are `Spf ℤ⟦X⟧{1/2}` and `Spf ℤ⟦X⟧{1/3}`. Neither is `⊤`, neither is `⊥`,
the two coordinate rings are different, and neither open is the `Spec` of a ring. So the cover
hypothesis of the theorems above is satisfied by a genuinely formal cover with more than one
piece, and `existsUnique_hom_thickeningMap_spfCover` applies at it to a *quantified* family with no
continuity input — which is what `existsUnique_hom_thickeningMap_spf_of_continuous`
(`SpfTargetColimit.lean`) cannot do, its family being definitionally the restriction of a `Spf ψ`.

What this witness does **not** exhibit is a target that is not itself formal-affine: `Spf ℤ⟦X⟧`
satisfies `IsThickeningColimitTarget` directly, by `isThickeningColimitTarget_spf`. Producing a
formal scheme that is provably not affine would need a glued formal model, which this tree does not
have; the closest it has is `SpecTwoPatchNonAffine.lean`, whose patches are `Spec`s. The witness
here therefore exercises the *cover* hypothesis non-degenerately without exercising
non-affineness, and that limitation is recorded rather than papered over.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6 (10.6.10).
* [The Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace FormalSpectrum.ColimitTarget

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable {X : LocallyRingedSpace.{u}}
variable (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X)
    (hf : ∀ n : ℕ, Spec.locallyRingedSpaceMap (stepRingHom I n) ≫ f (n + 1) = f n)

section Glue

variable (hI : I.FG) {ι : Type u} (r : ι → R)
    [∀ i, IsAdicRing (awayCompletionIdeal I (r i))]
    (hcov : (⨆ i, basicOpen I (r i)) = ⊤)
    (U : ι → Opens X.toTopCat)
    (hr : ∀ i, basicOpen I (r i) ≤ (Opens.map (commonBase I f)).obj (U i))
    (Y : ι → LocallyRingedSpace.{u})
    (e : ∀ i, X.restrict (U i).isOpenEmbedding ≅ Y i)
    (hY : ∀ i, IsThickeningColimitTarget (Y i))

/-- The morphism attached to the chart `D(r i)`, abbreviated. -/
def chartHom (i : ι) : locallyRingedSpaceObj (awayCompletionIdeal I (r i)) ⟶ X :=
  chartSpfHomAmbient I f hf (U i) (r i) (hr i) hI (e i) (hY i)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The chart morphisms agree on the pullbacks of the cover**, which is the hypothesis
`FormalScheme.OpenCover.glueMorphisms` takes. `SpfHomOfFamily.lean`'s proof, unchanged: the
overlap agreement is stated along the two legs and transported to the two pullback projections by
the leg identifications of `BasicOpenChartOverlapLegs.lean`. -/
theorem chartHom_pullback_compat (i j : ι) :
    letI := isOpenImmersion_basicOpenChart I (r i) hI
    letI := isOpenImmersion_basicOpenChart I (r j) hI
    pullback.fst (basicOpenChart I (r i)) (basicOpenChart I (r j)) ≫
        chartHom I f hf hI r U hr Y e hY i =
      pullback.snd (basicOpenChart I (r i)) (basicOpenChart I (r j)) ≫
        chartHom I f hf hI r U hr Y e hY j := by
  letI := isOpenImmersion_basicOpenChart I (r i) hI
  letI := isOpenImmersion_basicOpenChart I (r j) hI
  rw [← basicOpenChartOverlapIso_inv_comp_furtherLeft I (r i) (r j) hI,
    ← basicOpenChartOverlapIso_inv_comp_furtherRight I (r i) (r j) hI,
    Category.assoc, Category.assoc, chartHom, chartHom,
    chartSpfHomAmbient_overlap I f hf (U i) (r i) (hr i) hI (e i) (r j) (hY i) (U j) (hr j) (e j)
      (hY j)]

/-- **The morphism `Spf R ⟶ X` glued from the chart morphisms** (EGA I, 10.6.10). Cite
`thickeningMap_comp_spfHomOfFamily` and `spfHomOfFamily_uniq` rather than unfolding this. -/
def spfHomOfFamily : locallyRingedSpaceObj I ⟶ X :=
  (basicOpenCover I r hI hcov).glueMorphisms (chartHom I f hf hI r U hr Y e hY)
    (fun i j => chartHom_pullback_compat I f hf hI r U hr Y e hY i j)

set_option linter.style.setOption false in
-- The cover of the thickening is given by `chartOpen`, stated about the *scheme*
-- `Spec (CommRingCat.of _)`, while `thickeningMap` and the joint-epi lemma are stated about
-- `Spec.locallyRingedSpaceObj (CommRingCat.of _)`. The two are `rfl` but not at `instances`
-- transparency; the same accommodation `SpfHomOfFamily.lean` makes.
set_option backward.isDefEq.respectTransparency false in
/-- **The computation rule** (EGA I, 10.6.10): the glued morphism restricts on the `n`-th
thickening to the `n`-th member of the family it was built from. `SpfHomOfFamily.lean`'s proof,
with the two lemmas about the *source* — `iSup_chartOpen_eq_top` and
`thickeningMap_comp_basicOpenChart` — cited from there rather than restated. -/
theorem thickeningMap_comp_spfHomOfFamily (n : ℕ) :
    thickeningMap I n ≫ spfHomOfFamily I f hf hI r hcov U hr Y e hY = f n := by
  refine LocallyRingedSpace.hom_ext_of_iSup_eq_top
    (Z := Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))))
    (fun i => chartOpen I (r i) n) (iSup_chartOpen_eq_top I r hcov n) fun i => ?_
  refine (Iso.cancel_iso_inv_left (chartIsoLRS I (r i) hI n) _ _).mp ?_
  rw [← thickeningMap_comp_basicOpenChart_assoc, ← basicOpenCover_cmap I r hI hcov i,
    spfHomOfFamily, FormalScheme.OpenCover.map_glueMorphisms, chartHom,
    thickeningMap_comp_chartSpfHomAmbient]

/-- **…and it is the only morphism with those restrictions**, from `hom_ext_thickeningMap_lrs`. -/
theorem spfHomOfFamily_uniq (g : locallyRingedSpaceObj I ⟶ X)
    (hg : ∀ n : ℕ, thickeningMap I n ≫ g = f n) :
    g = spfHomOfFamily I f hf hI r hcov U hr Y e hY :=
  hom_ext_thickeningMap_lrs _ _ fun n =>
    (hg n).trans (thickeningMap_comp_spfHomOfFamily I f hf hI r hcov U hr Y e hY n).symm

end Glue

section Capstone

variable (hI : I.FG) {ι : Type u} (U : ι → Opens X.toTopCat) (hU : ⨆ i, U i = ⊤)
    (Y : ι → LocallyRingedSpace.{u})
    (e : ∀ i, X.restrict (U i).isOpenEmbedding ≅ Y i)
    (hY : ∀ i, IsThickeningColimitTarget (Y i))

include hf hI hU e hY in
/-- **`Spf R` is the colimit of its infinitesimal thickenings** (EGA I, 10.6.10), at a target
covered by opens each identified with a space having the colimit property.

At `Y i = Spec (B i)` this is `FormalSpectrum.existsUnique_hom_thickeningMap`, by
`isThickeningColimitTarget_spec`; at `Y i = Spf (J i)` it is
`existsUnique_hom_thickeningMap_spfCover`, by `isThickeningColimitTarget_spf`. The proof is the
landed one: `exists_basicOpen_refinement` supplies one basic open `D(r x)` through each point of
`|Spf R|`, chosen inside the pullback of some `U i`. -/
theorem existsUnique_hom_thickeningMap :
    ∃! g : locallyRingedSpaceObj I ⟶ X, ∀ n : ℕ, thickeningMap I n ≫ g = f n := by
  obtain ⟨r, idx, hcov, hle⟩ := exists_basicOpen_refinement I f U hU
  haveI hadic : ∀ x : FormalSpectrum I, IsAdicRing (awayCompletionIdeal I (r x)) := fun x =>
    isAdicRing_awayCompletionIdeal I (r x) hI
  refine ⟨spfHomOfFamily I f hf hI r hcov (fun x => U (idx x)) hle (fun x => Y (idx x))
      (fun x => e (idx x)) (fun x => hY (idx x)), fun n => ?_, fun g hg => ?_⟩
  · exact thickeningMap_comp_spfHomOfFamily I f hf hI r hcov _ hle _ _ _ n
  · exact spfHomOfFamily_uniq I f hf hI r hcov _ hle _ _ _ g hg

end Capstone

end FormalSpectrum.ColimitTarget

namespace FormalSpectrum

variable {X : LocallyRingedSpace.{u}}

/-- **The colimit property of formal spectra is local on the target.** If `X` is covered by opens
each identified with a space that has it, then `X` has it.

This is the statement the whole chart-and-glue chain of umbrella 59 was proving; until
`IsThickeningColimitTarget` existed it could only be stated with `Spec (B i)` in place of `Y i`,
which is `surjective_restrictToThickeningsLRS`. Iterating it is harmless but pointless — an open
cover of a cover piece refines to an open cover of `X`. -/
theorem isThickeningColimitTarget_of_cover {ι : Type u} (U : ι → Opens X.toTopCat)
    (hU : ⨆ i, U i = ⊤) (Y : ι → LocallyRingedSpace.{u})
    (e : ∀ i, X.restrict (U i).isOpenEmbedding ≅ Y i)
    (hY : ∀ i, IsThickeningColimitTarget (Y i)) : IsThickeningColimitTarget X := by
  intro S _ _ J _ hJ F
  obtain ⟨g, hg, -⟩ := ColimitTarget.existsUnique_hom_thickeningMap J F.1 F.2 hJ U hU Y e hY
  exact ⟨g, Subtype.ext (funext hg)⟩

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X)
    (hf : ∀ n : ℕ, Spec.locallyRingedSpaceMap (stepRingHom I n) ≫ f (n + 1) = f n)
    (hI : I.FG) {ι : Type u} (U : ι → Opens X.toTopCat) (hU : ⨆ i, U i = ⊤)
    {C : ι → Type u} [∀ i, CommRing (C i)] [∀ i, TopologicalSpace (C i)]
    (L : ∀ i, Ideal (C i)) [∀ i, IsAdicRing (L i)] (hL : ∀ i, (L i).FG)
    (e : ∀ i, X.restrict (U i).isOpenEmbedding ≅ locallyRingedSpaceObj (L i))

include hf hI hU hL e in
/-- **EGA I, 10.6.10 with the target covered by formal affines** (issue 62m). A compatible family
`Spec (R ⧸ Iⁿ⁺¹) ⟶ X` comes from a unique `Spf R ⟶ X`, for `X` a locally ringed space carrying a
cover by opens `U i` each *equipped* with an identification `X|_{U i} ≅ Spf (L i)`.

This is `existsUnique_hom_thickeningMap` with the `Spec`-shaped affineness datum replaced by a
`Spf`-shaped one. The finite generation `hL` is what
`surjective_restrictToThickeningsLRS_spf` needs of a formal-affine target; `hI` is what the
refinement of the *source* needs, and both theorems need it. -/
theorem existsUnique_hom_thickeningMap_spfCover :
    ∃! g : locallyRingedSpaceObj I ⟶ X, ∀ n : ℕ, thickeningMap I n ≫ g = f n :=
  ColimitTarget.existsUnique_hom_thickeningMap I f hf hI U hU _ e fun i =>
    isThickeningColimitTarget_spf (L i) (hL i)

include hf hI hU hL e in
/-- **The same, as a bijection.** Restriction to the thickenings is a bijection from `Spf R ⟶ X`
onto the compatible families, for a target covered by formal affines. Compare
`thickeningRestrictionEquivLRS`, which is this at a `Spec`-shaped cover. -/
def thickeningRestrictionEquivSpfCover :
    (locallyRingedSpaceObj I ⟶ X) ≃ ThickeningFamilyLRS I X :=
  thickeningRestrictionEquivOfColimitTarget I
    (isThickeningColimitTarget_of_cover U hU _ e fun i =>
      isThickeningColimitTarget_spf (L i) (hL i)) hI

section Witness

/-! ### Non-vacuity: a target with a genuinely formal cover

See the module docstring for what this witness does and does not exclude. -/

open Polynomial

attribute [local instance] isAdicRing_formalLineIdeal
attribute [local instance] isAdicRing_awayCompletionIdeal_formalLineElem

/-- **The two-piece formal-affine cover of `Spf ℤ⟦X⟧`**: the basic opens `D(2)` and `D(3)`. They
cover by `iSup_basicOpen_formalLineElem`, and neither is `⊥` or `⊤` — `D(3)` by
`basicOpen_formalLine_three_ne_bot`/`_ne_top`, `D(2)` by `chartOpen_formalLine_ne_bot`/`_ne_top`
read at level `0`, where `chartOpen` is the image of `D(2)` in the thickening. -/
def formalLineFormalOpen (b : Bool) :
    Opens (locallyRingedSpaceObj formalLineIdeal).toTopCat :=
  basicOpen formalLineIdeal (formalLineElem b)

/-- **Each piece of that cover is a formal affine**, namely `Spf ℤ⟦X⟧{1/2}` and `Spf ℤ⟦X⟧{1/3}`.
The identification is `LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq` between the basic-open
chart — an open immersion of range `D(r)`, `range_basicOpenChart_base` — and the tautological
inclusion of the open, whose range is the open. -/
def formalLineFormalChartIso (b : Bool) :
    (locallyRingedSpaceObj formalLineIdeal).restrict (formalLineFormalOpen b).isOpenEmbedding ≅
      locallyRingedSpaceObj (awayCompletionIdeal formalLineIdeal (formalLineElem b)) :=
  letI := isOpenImmersion_basicOpenChart formalLineIdeal (formalLineElem b) (polyXIdeal_fg.map _)
  (LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq
    (basicOpenChart formalLineIdeal (formalLineElem b))
    ((locallyRingedSpaceObj formalLineIdeal).ofRestrict
      (formalLineFormalOpen b).isOpenEmbedding)
    (by
      rw [range_basicOpenChart_base formalLineIdeal (formalLineElem b) (polyXIdeal_fg.map _),
        LocallyRingedSpace.range_ofRestrict]
      rfl)).symm

/-- **Every piece of the cover has the colimit property**, by `isThickeningColimitTarget_spf`: the
ideal of definition of `ℤ⟦X⟧{1/r}` is finitely generated because `polyXIdeal` is. -/
theorem isThickeningColimitTarget_formalLineChart (b : Bool) :
    IsThickeningColimitTarget
      (locallyRingedSpaceObj (awayCompletionIdeal formalLineIdeal (formalLineElem b))) :=
  isThickeningColimitTarget_spf _
    (awayCompletionIdeal_fg formalLineIdeal (formalLineElem b)
      (polyXIdeal_fg.map _))

/-- **The witness of `isThickeningColimitTarget_of_cover`**: `Spf ℤ⟦X⟧` has the colimit property
*through a two-piece formal cover*, with no `Spec` anywhere in the hypotheses.

It is also true directly, by `isThickeningColimitTarget_spf` — this space is a formal affine. That
is the honest limit of the witness, and it is why the statement below is a *use* of the cover
theorem rather than a new fact: what it exhibits is that the cover hypothesis is satisfiable by a
cover that is genuinely formal and genuinely has more than one piece. -/
theorem isThickeningColimitTarget_formalLine_of_cover :
    IsThickeningColimitTarget (locallyRingedSpaceObj formalLineIdeal) :=
  isThickeningColimitTarget_of_cover formalLineFormalOpen iSup_basicOpen_formalLineElem _
    formalLineFormalChartIso isThickeningColimitTarget_formalLineChart

/-- **The same target, without the cover.** `Spf ℤ⟦X⟧` is a formal affine, so
`isThickeningColimitTarget_spf` gives the conclusion of
`isThickeningColimitTarget_formalLine_of_cover` directly. Recording both is the point: they are
the two entry points of `isThickeningColimitTarget_of_cover`, and that they agree at the one space
where both apply is the check that the cover route computes the right thing.

The ideal of definition is not `⊥` (`formalLineIdeal_ne_bot`), so the tower of thickenings being
quantified over is not the constant one. -/
theorem isThickeningColimitTarget_formalLine :
    IsThickeningColimitTarget (locallyRingedSpaceObj formalLineIdeal) :=
  isThickeningColimitTarget_spf formalLineIdeal (polyXIdeal_fg.map _)

/-- **EGA I, 10.6.10 at a formal cover, run end to end.** For *any* compatible family of morphisms
out of the thickenings of `Spf ℤ⟦X⟧` into `Spf ℤ⟦X⟧`, there is a unique morphism it comes from.

The family is quantified and carries no continuity witness, which is what
`existsUnique_hom_thickeningMap_spf_of_continuous` cannot do: its family is definitionally the
restriction of a `Spf ψ`. -/
theorem existsUnique_hom_thickeningMap_formalLine_spfCover
    (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj
        (CommRingCat.of (AdicCompletion polyXIdeal ℤ[X] ⧸ formalLineIdeal ^ (n + 1))) ⟶
      locallyRingedSpaceObj formalLineIdeal)
    (hf : ∀ n : ℕ, Spec.locallyRingedSpaceMap (stepRingHom formalLineIdeal n) ≫ f (n + 1) = f n) :
    ∃! g : locallyRingedSpaceObj formalLineIdeal ⟶ locallyRingedSpaceObj formalLineIdeal,
      ∀ n : ℕ, thickeningMap formalLineIdeal n ≫ g = f n :=
  existsUnique_hom_thickeningMap_spfCover formalLineIdeal f hf (polyXIdeal_fg.map _)
    formalLineFormalOpen iSup_basicOpen_formalLineElem _
    (fun b => awayCompletionIdeal_fg formalLineIdeal (formalLineElem b)
      (polyXIdeal_fg.map _))
    formalLineFormalChartIso

end Witness

end FormalSpectrum

end
