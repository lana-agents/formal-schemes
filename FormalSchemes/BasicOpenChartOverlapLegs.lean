import FormalSchemes.BasicOpenChartOverlap

set_option linter.style.header false

/-!
# The legs of the basic-open chart overlap (EGA I, §10.8, §10.15)

For an adic ring `(A, I)` with `I` finitely generated and elements `f g : A`, the merged
`FormalSchemes/BasicOpenChartOverlap.lean` identifies the fibre product of the two basic-open
charts `Spf A{1/f} ⟶ Spf A` and `Spf A{1/g} ⟶ Spf A` with the chart at the product,

```
basicOpenChartOverlapIso : Spf A{1/(f·g)} ≅ pullback (basicOpenChart I f) (basicOpenChart I g),
```

together with the compatibilities of that identification with the maps **down to `Spf A`**. What it
does not say is what the two pullback *projections* are ring-theoretically. This file supplies
that: each projection is `Spf` of the evident further-localization homomorphism.

The point is that the geometric triple-overlap field `xt'` of `AffineChartedFibreDatumX`
(`FormalSchemes/GeneralFibreProductExposeX.lean`) is a morphism between exactly such pullbacks, and
its law `xt_fac` is a statement about `pullback.fst` / `pullback.snd`. Presenting the pullback as an
affine chart (the merged overlap iso) is therefore not enough on its own — one also needs the
projections as `FormalSpectrum.locallyRingedSpaceMap` of concrete ring maps, which is what the
`_hom_fst` / `_hom_snd` identifications below provide.

## Main definitions and results

* `FormalSpectrum.awayMulLocHomLeft` / `awayMulLocHomRight`: the further-localization ring maps
  `A_f →+* A_{f·g}` and `A_g →+* A_{f·g}` (`f`, resp. `g`, is already a unit in `A_{f·g}`).
* `FormalSpectrum.awayCompletionMulHomLeft` / `awayCompletionMulHomRight`: their completions,
  `A{1/f} →+* A{1/(f·g)}` and `A{1/g} →+* A{1/(f·g)}`.
* `FormalSpectrum.basicOpenChartFurtherLeft` / `basicOpenChartFurtherRight`: `Spf` of those, the
  chart inclusions `Spf A{1/(f·g)} ⟶ Spf A{1/f}` and `Spf A{1/(f·g)} ⟶ Spf A{1/g}`.
* `FormalSpectrum.basicOpenChartFurtherLeft_comp` / `basicOpenChartFurtherRight_comp`: the affine
  factorizations `D(f·g) ↪ D(f) ↪ Spf A` and `D(f·g) ↪ D(g) ↪ Spf A` of the chart at `f·g`.
* `FormalSpectrum.basicOpenChartOverlapIso_hom_fst` / `_hom_snd`: **the leg identifications**, and
  their `inv`-side forms `basicOpenChartOverlapIso_inv_comp_furtherLeft` / `_furtherRight`.

## Route

Both leg identifications reduce to the affine factorizations, because `basicOpenChart I f` is an
open immersion and hence a mono: `cancel_mono` turns
`overlapIso.hom ≫ pullback.fst = basicOpenChartFurtherLeft` into
`overlapIso.hom ≫ pullback.fst ≫ basicOpenChart I f =
basicOpenChartFurtherLeft ≫ basicOpenChart I f`, whose left side is the merged
`basicOpenChartOverlapIso_hom_fst_comp = basicOpenChart I (f * g)` and whose right side is
`basicOpenChartFurtherLeft_comp`. No pullback reasoning is left; the content is
the functoriality of `Spf` applied to the ring identity
`awayCompletionMulHomLeft ∘ awayCompletionHom I f = awayCompletionHom I (f * g)`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8, §10.15.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (I : Ideal R) (f g : R)

/-!
### The further-localization ring maps
-/

/-- For any `f g : R`, the element `g` becomes a unit in `Localization.Away (f * g)`: the product
`f * g` is a unit there, and a divisor of a unit is a unit. This is the right-hand companion of
`isUnit_algebraMap_away_left`. -/
theorem isUnit_algebraMap_away_right :
    IsUnit (algebraMap R (Localization.Away (f * g)) g) := by
  have h : IsUnit (algebraMap R (Localization.Away (f * g)) (f * g)) :=
    IsLocalization.Away.algebraMap_isUnit (f * g)
  rw [map_mul] at h
  exact isUnit_of_mul_isUnit_right h

/-- **The further localization `R_f →+* R_{f·g}`.** Since `f` is a unit in `R_{f·g}`
(`isUnit_algebraMap_away_left`), the universal property of `R_f` supplies a unique `R`-algebra map
to `R_{f·g}`. Geometrically it is the inclusion `D(f·g) = D(f) ∩ D(g) ⊆ D(f)`. -/
def awayMulLocHomLeft : Localization.Away f →+* Localization.Away (f * g) :=
  IsLocalization.Away.lift f (isUnit_algebraMap_away_left f g)

/-- **The further localization `R_g →+* R_{f·g}`**, the right-hand companion of
`awayMulLocHomLeft`; geometrically the inclusion `D(f·g) ⊆ D(g)`. -/
def awayMulLocHomRight : Localization.Away g →+* Localization.Away (f * g) :=
  IsLocalization.Away.lift g (isUnit_algebraMap_away_right f g)

/-- The further localization on the left is a map under `R`. -/
theorem awayMulLocHomLeft_comp_algebraMap :
    (awayMulLocHomLeft f g).comp (algebraMap R (Localization.Away f)) =
      algebraMap R (Localization.Away (f * g)) :=
  IsLocalization.Away.lift_comp f (isUnit_algebraMap_away_left f g)

/-- The further localization on the right is a map under `R`. -/
theorem awayMulLocHomRight_comp_algebraMap :
    (awayMulLocHomRight f g).comp (algebraMap R (Localization.Away g)) =
      algebraMap R (Localization.Away (f * g)) :=
  IsLocalization.Away.lift_comp g (isUnit_algebraMap_away_right f g)

/-- `I·R_f` is carried onto `I·R_{f·g}` by the left further localization. -/
theorem map_awayMulLocHomLeft :
    (I.map (algebraMap R (Localization.Away f))).map (awayMulLocHomLeft f g) =
      I.map (algebraMap R (Localization.Away (f * g))) := by
  rw [Ideal.map_map, awayMulLocHomLeft_comp_algebraMap]

/-- `I·R_g` is carried onto `I·R_{f·g}` by the right further localization. -/
theorem map_awayMulLocHomRight :
    (I.map (algebraMap R (Localization.Away g))).map (awayMulLocHomRight f g) =
      I.map (algebraMap R (Localization.Away (f * g))) := by
  rw [Ideal.map_map, awayMulLocHomRight_comp_algebraMap]

/-!
### The further-localization maps on completed localizations
-/

/-- **The further completed localization `A{1/f} →+* A{1/(f·g)}`**, the completion of
`awayMulLocHomLeft`. -/
def awayCompletionMulHomLeft (hI : I.FG) :
    awayCompletion I f →+* awayCompletion I (f * g) :=
  AdicCompletion.mapCompletion (awayMulLocHomLeft f g) (map_awayMulLocHomLeft I f g).le (hI.map _)

/-- **The further completed localization `A{1/g} →+* A{1/(f·g)}`**, the completion of
`awayMulLocHomRight`. -/
def awayCompletionMulHomRight (hI : I.FG) :
    awayCompletion I g →+* awayCompletion I (f * g) :=
  AdicCompletion.mapCompletion (awayMulLocHomRight f g) (map_awayMulLocHomRight I f g).le
    (hI.map _)

/-- The left further completed localization is continuous: it carries the ideal of definition of
`A{1/f}` into that of `A{1/(f·g)}`. This is the hypothesis `FormalSpectrum.locallyRingedSpaceMap`
consumes. -/
theorem le_comap_awayCompletionMulHomLeft (hI : I.FG) :
    awayCompletionIdeal I f ≤
      (awayCompletionIdeal I (f * g)).comap (awayCompletionMulHomLeft I f g hI) :=
  Ideal.map_le_iff_le_comap.mp
    (AdicCompletion.idealOfDefinition_map_le (awayMulLocHomLeft f g)
      (map_awayMulLocHomLeft I f g).le (hI.map _))

/-- The right further completed localization is continuous. -/
theorem le_comap_awayCompletionMulHomRight (hI : I.FG) :
    awayCompletionIdeal I g ≤
      (awayCompletionIdeal I (f * g)).comap (awayCompletionMulHomRight I f g hI) :=
  Ideal.map_le_iff_le_comap.mp
    (AdicCompletion.idealOfDefinition_map_le (awayMulLocHomRight f g)
      (map_awayMulLocHomRight I f g).le (hI.map _))

/-- The left further completed localization is a map under `R`: composing it with the structural
map `R → A{1/f}` gives the structural map `R → A{1/(f·g)}`. This is the whole ring-theoretic
content of the leg identifications. -/
theorem awayCompletionMulHomLeft_comp_awayCompletionHom (hI : I.FG) :
    (awayCompletionMulHomLeft I f g hI).comp (awayCompletionHom I f) =
      awayCompletionHom I (f * g) := by
  refine RingHom.ext fun r => ?_
  rw [RingHom.comp_apply, awayCompletionHom, awayCompletionHom, RingHom.comp_apply,
    awayCompletionMulHomLeft, AdicCompletion.mapCompletion_algebraMap, RingHom.comp_apply]
  exact congrArg _ (RingHom.congr_fun (awayMulLocHomLeft_comp_algebraMap f g) r)

/-- The right further completed localization is a map under `R`. -/
theorem awayCompletionMulHomRight_comp_awayCompletionHom (hI : I.FG) :
    (awayCompletionMulHomRight I f g hI).comp (awayCompletionHom I g) =
      awayCompletionHom I (f * g) := by
  refine RingHom.ext fun r => ?_
  rw [RingHom.comp_apply, awayCompletionHom, awayCompletionHom, RingHom.comp_apply,
    awayCompletionMulHomRight, AdicCompletion.mapCompletion_algebraMap, RingHom.comp_apply]
  exact congrArg _ (RingHom.congr_fun (awayMulLocHomRight_comp_algebraMap f g) r)

/-!
### The chart inclusions `Spf A{1/(f·g)} ⟶ Spf A{1/f}`, `⟶ Spf A{1/g}`
-/

/-- **The left further basic-open chart** `Spf A{1/(f·g)} ⟶ Spf A{1/f}`: `Spf` of
`awayCompletionMulHomLeft`. Geometrically the chart of `Spf A{1/f}` on the basic open cut out by
(the image of) `g`. -/
def basicOpenChartFurtherLeft (hI : I.FG) :
    locallyRingedSpaceObj (awayCompletionIdeal I (f * g)) ⟶
      locallyRingedSpaceObj (awayCompletionIdeal I f) :=
  locallyRingedSpaceMap (awayCompletionIdeal I f) (awayCompletionIdeal I (f * g))
    (awayCompletionMulHomLeft I f g hI) (le_comap_awayCompletionMulHomLeft I f g hI)

/-- **The right further basic-open chart** `Spf A{1/(f·g)} ⟶ Spf A{1/g}`. -/
def basicOpenChartFurtherRight (hI : I.FG) :
    locallyRingedSpaceObj (awayCompletionIdeal I (f * g)) ⟶
      locallyRingedSpaceObj (awayCompletionIdeal I g) :=
  locallyRingedSpaceMap (awayCompletionIdeal I g) (awayCompletionIdeal I (f * g))
    (awayCompletionMulHomRight I f g hI) (le_comap_awayCompletionMulHomRight I f g hI)

/-- **The chart at `f·g` factors through the chart at `f`**: `D(f·g) ↪ D(f) ↪ Spf A` is the chart at
`f·g`. This is `Spf` of `awayCompletionMulHomLeft_comp_awayCompletionHom`. -/
@[reassoc]
theorem basicOpenChartFurtherLeft_comp (hI : I.FG) :
    basicOpenChartFurtherLeft I f g hI ≫ basicOpenChart I f = basicOpenChart I (f * g) := by
  have hIK : I ≤ (awayCompletionIdeal I (f * g)).comap
      ((awayCompletionMulHomLeft I f g hI).comp (awayCompletionHom I f)) := by
    rw [awayCompletionMulHomLeft_comp_awayCompletionHom]
    exact le_comap_awayCompletionHom I (f * g)
  rw [basicOpenChartFurtherLeft, basicOpenChart, basicOpenChart,
    ← locallyRingedSpaceMap_comp I (awayCompletionIdeal I f) (awayCompletionIdeal I (f * g))
      (awayCompletionHom I f) (awayCompletionMulHomLeft I f g hI)
      (le_comap_awayCompletionHom I f) (le_comap_awayCompletionMulHomLeft I f g hI) hIK]
  exact locallyRingedSpaceMap_congr _ _ _ _ _ _
    (awayCompletionMulHomLeft_comp_awayCompletionHom I f g hI)

/-- **The chart at `f·g` factors through the chart at `g`**. -/
@[reassoc]
theorem basicOpenChartFurtherRight_comp (hI : I.FG) :
    basicOpenChartFurtherRight I f g hI ≫ basicOpenChart I g = basicOpenChart I (f * g) := by
  have hIK : I ≤ (awayCompletionIdeal I (f * g)).comap
      ((awayCompletionMulHomRight I f g hI).comp (awayCompletionHom I g)) := by
    rw [awayCompletionMulHomRight_comp_awayCompletionHom]
    exact le_comap_awayCompletionHom I (f * g)
  rw [basicOpenChartFurtherRight, basicOpenChart, basicOpenChart,
    ← locallyRingedSpaceMap_comp I (awayCompletionIdeal I g) (awayCompletionIdeal I (f * g))
      (awayCompletionHom I g) (awayCompletionMulHomRight I f g hI)
      (le_comap_awayCompletionHom I g) (le_comap_awayCompletionMulHomRight I f g hI) hIK]
  exact locallyRingedSpaceMap_congr _ _ _ _ _ _
    (awayCompletionMulHomRight_comp_awayCompletionHom I f g hI)

/-!
### The leg identifications
-/

/-- **The first leg of the basic-open chart overlap.** Under the identification of the overlap with
the chart at `f · g`, the first pullback projection is the further basic-open chart
`Spf A{1/(f·g)} ⟶ Spf A{1/f}`. Proved by cancelling the mono `basicOpenChart I f`, which reduces the
statement to the affine factorization `basicOpenChartFurtherLeft_comp`. -/
@[reassoc]
theorem basicOpenChartOverlapIso_hom_fst (hI : I.FG) :
    letI := isOpenImmersion_basicOpenChart I f hI
    letI := isOpenImmersion_basicOpenChart I g hI
    (basicOpenChartOverlapIso I f g hI).hom ≫
        pullback.fst (basicOpenChart I f) (basicOpenChart I g) =
      basicOpenChartFurtherLeft I f g hI := by
  letI := isOpenImmersion_basicOpenChart I f hI
  letI := isOpenImmersion_basicOpenChart I g hI
  rw [← cancel_mono (basicOpenChart I f), Category.assoc,
    basicOpenChartOverlapIso_hom_fst_comp I f g hI, basicOpenChartFurtherLeft_comp I f g hI]

/-- **The second leg of the basic-open chart overlap**: the second pullback projection is the
further basic-open chart `Spf A{1/(f·g)} ⟶ Spf A{1/g}`. -/
@[reassoc]
theorem basicOpenChartOverlapIso_hom_snd (hI : I.FG) :
    letI := isOpenImmersion_basicOpenChart I f hI
    letI := isOpenImmersion_basicOpenChart I g hI
    (basicOpenChartOverlapIso I f g hI).hom ≫
        pullback.snd (basicOpenChart I f) (basicOpenChart I g) =
      basicOpenChartFurtherRight I f g hI := by
  letI := isOpenImmersion_basicOpenChart I f hI
  letI := isOpenImmersion_basicOpenChart I g hI
  rw [← cancel_mono (basicOpenChart I g), Category.assoc,
    basicOpenChartOverlapIso_hom_snd_comp I f g hI, basicOpenChartFurtherRight_comp I f g hI]

/-- The `inv`-side form of the first leg identification: going out of the pullback through the
overlap identification and then into `Spf A{1/f}` is the first projection. -/
@[reassoc]
theorem basicOpenChartOverlapIso_inv_comp_furtherLeft (hI : I.FG) :
    letI := isOpenImmersion_basicOpenChart I f hI
    letI := isOpenImmersion_basicOpenChart I g hI
    (basicOpenChartOverlapIso I f g hI).inv ≫ basicOpenChartFurtherLeft I f g hI =
      pullback.fst (basicOpenChart I f) (basicOpenChart I g) := by
  letI := isOpenImmersion_basicOpenChart I f hI
  letI := isOpenImmersion_basicOpenChart I g hI
  rw [← basicOpenChartOverlapIso_hom_fst I f g hI, Iso.inv_hom_id_assoc]

/-- The `inv`-side form of the second leg identification. -/
@[reassoc]
theorem basicOpenChartOverlapIso_inv_comp_furtherRight (hI : I.FG) :
    letI := isOpenImmersion_basicOpenChart I f hI
    letI := isOpenImmersion_basicOpenChart I g hI
    (basicOpenChartOverlapIso I f g hI).inv ≫ basicOpenChartFurtherRight I f g hI =
      pullback.snd (basicOpenChart I f) (basicOpenChart I g) := by
  letI := isOpenImmersion_basicOpenChart I f hI
  letI := isOpenImmersion_basicOpenChart I g hI
  rw [← basicOpenChartOverlapIso_hom_snd I f g hI, Iso.inv_hom_id_assoc]

end FormalSpectrum

end
