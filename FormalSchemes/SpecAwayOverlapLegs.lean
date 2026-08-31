import FormalSchemes.SpecAwayOverlap

set_option linter.style.header false

/-!
# The legs of the affine basic-open overlap identification (EGA I, 10.8)

`FormalSchemes.SpecAwayOverlap` identifies the affine chart `Spec R_{fg}` with the fibre product
`pullback (specAwayMap f) (specAwayMap g)` of the two chart inclusions, and records the two
compatibilities with the inclusions *into `Spec R`*: `specAwayOverlapIso_hom_fst_comp` says that
the identification followed by the first projection and then `specAwayMap f` is `specAwayMap (fg)`.

That is not enough to compute with. A glue datum's `t_fac` field composes `t'` with a bare
projection `pullback.snd`, with no inclusion into an ambient object after it — indeed at an
arbitrary index there is no ambient object, which is the whole reason
`FormalSchemes.ChartedSchemeDatum` exists. So the projections themselves have to be identified,
and this file does that: each is `Spec` of the further-localization map, `R_f ⟶ R_{fg}`.

This is the `Spec`-side mirror of `FormalSchemes.BasicOpenChartOverlapLegs`, whose
`FormalSpectrum.basicOpenChartOverlapIso_hom_fst` / `_hom_snd` play the same role one completion
further up.

## The argument, in one line

`specAwayMap f` is an open immersion, hence a monomorphism, and
`specAwayOverlapIso_hom_fst_comp` is precisely the statement that the two candidate maps become
equal after composing with it. So `cancel_mono` closes it, once the further-localization map is
known to commute with the two structure maps from `R` — which is
`IsLocalization.Away.awayToAwayRight_eq`.

## The further-localization maps are Mathlib's

The two ring maps `R_f ⟶ R_{fg}` and `R_g ⟶ R_{fg}` are **not** defined here. They are
`IsLocalization.Away.awayToAwayRight f g` and `IsLocalization.Away.awayToAwayLeft g f`
(`Mathlib/RingTheory/Localization/Away/Basic.lean`), and their compatibility with the structure
maps from `R` is `awayToAwayRight_eq` / `awayToAwayLeft_eq` there.

Using Mathlib's spelling rather than a local one is not tidiness. The sheaf condition for
`𝒪_{Spec R}` along a cover by basic opens — Mathlib's
`Localization.existsUnique_algebraMap_eq_of_span_eq_top`, and the tool a `desc` out of a glued
`Spec` eventually consumes — states its overlap hypothesis in exactly these two maps. A local
alias would have to be bridged into that statement at every use site.

## Main definitions and results

* `AlgebraicGeometry.specAwayFurtherLeft` / `specAwayFurtherRight`: the spectra of Mathlib's two
  further-localization maps, the two chart inclusions of the overlap into the single charts.
* `AlgebraicGeometry.specAwayFurtherLeft_comp` / `specAwayFurtherRight_comp`: each followed by the
  corresponding chart inclusion is the chart inclusion at the product.
* `AlgebraicGeometry.specAwayOverlapIso_hom_fst` / `_hom_snd`: the leg identifications, the point
  of the file.
* `AlgebraicGeometry.specAwayOverlapIso_inv_comp_left` / `_inv_comp_right`: the same read backwards
  along the identification, which is the form a `t_fac` proof rewrites with.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] (f g : R)

/-! ### The two legs -/

/-- **The first leg of the overlap**, `Spec R_{fg} ⟶ Spec R_f`. -/
abbrev specAwayFurtherLeft :
    Spec.locallyRingedSpaceObj (CommRingCat.of (Localization.Away (f * g))) ⟶
      Spec.locallyRingedSpaceObj (CommRingCat.of (Localization.Away f)) :=
  Spec.locallyRingedSpaceMap (CommRingCat.ofHom (IsLocalization.Away.awayToAwayRight f g))

/-- **The second leg of the overlap**, `Spec R_{fg} ⟶ Spec R_g`. -/
abbrev specAwayFurtherRight :
    Spec.locallyRingedSpaceObj (CommRingCat.of (Localization.Away (f * g))) ⟶
      Spec.locallyRingedSpaceObj (CommRingCat.of (Localization.Away g)) :=
  Spec.locallyRingedSpaceMap (CommRingCat.ofHom (IsLocalization.Away.awayToAwayLeft g f))

/-- The first leg followed by the first chart inclusion is the chart inclusion at the product.
This is `Spec` of `IsLocalization.Away.awayToAwayRight_eq`. -/
@[reassoc]
theorem specAwayFurtherLeft_comp :
    specAwayFurtherLeft f g ≫ specAwayMap f = specAwayMap (f * g) := by
  rw [← Spec.locallyRingedSpaceMap_comp, ← CommRingCat.ofHom_comp,
    show (IsLocalization.Away.awayToAwayRight (S := Localization.Away f)
        (P := Localization.Away (f * g)) f g).comp (algebraMap R (Localization.Away f)) =
      algebraMap R (Localization.Away (f * g)) from
      RingHom.ext fun a => IsLocalization.Away.awayToAwayRight_eq f g a]

/-- The second leg followed by the second chart inclusion is the chart inclusion at the product. -/
@[reassoc]
theorem specAwayFurtherRight_comp :
    specAwayFurtherRight f g ≫ specAwayMap g = specAwayMap (f * g) := by
  rw [← Spec.locallyRingedSpaceMap_comp, ← CommRingCat.ofHom_comp,
    show (IsLocalization.Away.awayToAwayLeft (S := Localization.Away g)
        (P := Localization.Away (f * g)) g f).comp (algebraMap R (Localization.Away g)) =
      algebraMap R (Localization.Away (f * g)) from
      RingHom.ext fun a => IsLocalization.Away.awayToAwayLeft_eq g f a]

/-- **The first leg identification.** The overlap identification followed by the first projection
of the fibre product is the further localization `Spec R_{fg} ⟶ Spec R_f`.

Both sides become `specAwayMap (f * g)` after composing with the monomorphism `specAwayMap f` —
the left by `specAwayOverlapIso_hom_fst_comp` and the right by `specAwayFurtherLeft_comp`. -/
theorem specAwayOverlapIso_hom_fst :
    (specAwayOverlapIso f g).hom ≫ pullback.fst (specAwayMap f) (specAwayMap g) =
      specAwayFurtherLeft f g := by
  rw [← cancel_mono (specAwayMap f), Category.assoc, specAwayOverlapIso_hom_fst_comp,
    specAwayFurtherLeft_comp]

/-- **The second leg identification.** -/
theorem specAwayOverlapIso_hom_snd :
    (specAwayOverlapIso f g).hom ≫ pullback.snd (specAwayMap f) (specAwayMap g) =
      specAwayFurtherRight f g := by
  rw [← cancel_mono (specAwayMap g), Category.assoc, specAwayOverlapIso_hom_snd_comp,
    specAwayFurtherRight_comp]

/-- The first leg read backwards along the identification: this is the form a `t_fac` proof
rewrites a bare `pullback.fst` with. -/
theorem specAwayOverlapIso_inv_comp_left :
    (specAwayOverlapIso f g).inv ≫ specAwayFurtherLeft f g =
      pullback.fst (specAwayMap f) (specAwayMap g) := by
  rw [← specAwayOverlapIso_hom_fst, Iso.inv_hom_id_assoc]

/-- The second leg read backwards along the identification. -/
theorem specAwayOverlapIso_inv_comp_right :
    (specAwayOverlapIso f g).inv ≫ specAwayFurtherRight f g =
      pullback.snd (specAwayMap f) (specAwayMap g) := by
  rw [← specAwayOverlapIso_hom_snd, Iso.inv_hom_id_assoc]

end AlgebraicGeometry

end
