import FormalSchemes.BothDatumFibreAdicOverBase
import FormalSchemes.GeneralFibreProductLiftAdic
import FormalSchemes.GeneralFibreProductLiftUniqueAdic

set_option linter.style.header false

/-!
# The general fibre product is unique up to canonical isomorphism

Two two-sided fibre-product datums `D D' : BothChartedFibreDatumXY R I hI` over the same adic base
`(R, I)` that present *the same* `X` and `Y` — an isomorphism `eX : D.xGlued ≅ D'.xGlued` over
`Spf I`, and likewise `eY` — have canonically isomorphic fibre products:

```
compareIso : D.generalFibreProduct ≅ D'.generalFibreProduct
```

compatible with both projections, `compareIso.hom ≫ D'.pr₁ = D.pr₁ ≫ eX.hom`.

## Why this could not be stated before

Both halves of the general fibre product's universal property —
`BothChartedFibreDatumXY.fibreLiftAdic` (existence, issue 794) and
`fibreLift_unique_adicOverBase` (uniqueness, issue 518) — apply only to a source `Z` carrying a
witness `FormalScheme.AdicOverBaseLocallyFG Z s`. The mediating morphisms here go *out of* a fibre
product, so both directions need that witness at `D.generalFibreProduct` itself. That is
`BothChartedFibreDatumXY.adicOverBase_fibreStructMap`
(`FormalSchemes.BothDatumFibreAdicOverBase`, issue 832); before it existed this file's statements
had no well-formed spelling, let alone a proof.

## The argument

Entirely formal, and it is the standard "two objects with the same universal property" argument
carried out in this tower's vocabulary. `compareHom` is `D'`'s mediating morphism for the legs
`D.pr₁ ≫ eX.hom` and `D.pr₂ ≫ eY.hom`; `compareInv` is `D`'s for `D'.pr₁ ≫ eX.inv` and
`D'.pr₂ ≫ eY.inv`. The base compatibilities are `heX`/`heY` for the forward direction and
`Iso.inv_comp_eq` applied to them for the backward one. Each round trip is
`fibreLift_unique_adicOverBase` against the identity, whose three hypotheses are the two projection
laws `fibreLiftAdic_comp_pr₁`/`_comp_pr₂` chased through `Iso.hom_inv_id` and one reassociation.

Note that `fibreLiftAdic` and `fibreLift_unique_adicOverBase` both work with morphisms of **locally
ringed spaces**, so `compareIso` is an iso in `LocallyRingedSpace` and the identities are
`𝟙 D.generalFibreProduct.toLocallyRingedSpace`. Upgrading it to an isomorphism of `FormalScheme`s
is a separate step and is not taken here.

## Main results

* `AlgebraicGeometry.BothChartedFibreDatumXY.compareHom` / `compareInv`: the two mediating
  morphisms, with `compareHom_comp_pr₁`/`_comp_pr₂` and `compareInv_comp_pr₁`/`_comp_pr₂` their
  projection laws.
* `AlgebraicGeometry.BothChartedFibreDatumXY.compareHom_comp_compareInv` /
  `compareInv_comp_compareHom`: the two round trips.
* `AlgebraicGeometry.BothChartedFibreDatumXY.compareIso`: **the canonical isomorphism.**

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
-/

noncomputable section

open CategoryTheory TopologicalSpace Topology FormalSpectrum
open CompletedTensorProduct

universe u

namespace AlgebraicGeometry

namespace BothChartedFibreDatumXY

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable [TopologicalSpace R] [IsAdicRing I]
variable (D D' : BothChartedFibreDatumXY R I hI)

section
variable
  (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
    ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
  (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
    ∀ p p' (h : p ≠ p'),
      D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
  (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
    ∀ p p' (h : p ≠ p'),
      D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
        eqToHom (hV p' p h.symm).symm)
  (hV' : letI := D'.commRingA; letI := D'.algebraA; letI := D'.commRingB; letI := D'.algebraB
    ∀ p p' (h : p ≠ p'), D'.V p p' h = bothAlgDataV hI D'.gX D'.gY p p' h)
  (hf' : letI := D'.commRingA; letI := D'.algebraA; letI := D'.commRingB; letI := D'.algebraB
    ∀ p p' (h : p ≠ p'),
      D'.f p p' h = eqToHom (hV' p p' h) ≫ bothAlgDataF hI D'.gX D'.gY p p' h)
  (ht' : letI := D'.commRingA; letI := D'.algebraA; letI := D'.commRingB; letI := D'.algebraB
    ∀ p p' (h : p ≠ p'),
      D'.t p p' h = eqToHom (hV' p p' h) ≫ bothAlgDataT hI D'.gX D'.gY D'.τX D'.τY p p' h ≫
        eqToHom (hV' p' p h.symm).symm)
  (eX : D.xGlued.toLocallyRingedSpace ≅ D'.xGlued.toLocallyRingedSpace)
  (eY : D.yGlued.toLocallyRingedSpace ≅ D'.yGlued.toLocallyRingedSpace)
  (heX : eX.hom ≫ D'.xStructMap = D.xStructMap)
  (heY : eY.hom ≫ D'.yStructMap = D.yStructMap)

/-- **The forward comparison morphism.** `D'`'s mediating morphism for the legs `D.pr₁ ≫ eX.hom`
and `D.pr₂ ≫ eY.hom`, which is available because `D.generalFibreProduct` is adic over its own base
(`adicOverBase_fibreStructMap`). -/
def compareHom :
    letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
    letI := D.topologyA; letI := D.isAdicA; letI := D.topologyB; letI := D.isAdicB
    D.generalFibreProduct.toLocallyRingedSpace ⟶ D'.generalFibreProduct.toLocallyRingedSpace :=
  letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
  letI := D.topologyA; letI := D.isAdicA; letI := D.topologyB; letI := D.isAdicB
  D'.fibreLiftAdic (D.pr₁ hV hf ht ≫ eX.hom) (D.pr₂ hV hf ht ≫ eY.hom)
    (D.pr₁ hV hf ht ≫ D.xStructMap) (D.adicOverBase_fibreStructMap hV hf ht)
    (by rw [Category.assoc, heX]) hV' hf' ht'
    (by rw [Category.assoc, Category.assoc, heX, heY]; exact D.cone_comm hV hf ht)

/-- **The backward comparison morphism**, the mirror of `compareHom` with the roles of `D` and `D'`
exchanged and `eX`, `eY` inverted. -/
def compareInv :
    letI := D'.commRingA; letI := D'.algebraA; letI := D'.commRingB; letI := D'.algebraB
    letI := D'.topologyA; letI := D'.isAdicA; letI := D'.topologyB; letI := D'.isAdicB
    D'.generalFibreProduct.toLocallyRingedSpace ⟶ D.generalFibreProduct.toLocallyRingedSpace :=
  letI := D'.commRingA; letI := D'.algebraA; letI := D'.commRingB; letI := D'.algebraB
  letI := D'.topologyA; letI := D'.isAdicA; letI := D'.topologyB; letI := D'.isAdicB
  D.fibreLiftAdic (D'.pr₁ hV' hf' ht' ≫ eX.inv) (D'.pr₂ hV' hf' ht' ≫ eY.inv)
    (D'.pr₁ hV' hf' ht' ≫ D'.xStructMap) (D'.adicOverBase_fibreStructMap hV' hf' ht')
    (by rw [Category.assoc, (Iso.inv_comp_eq (α := eX)).mpr heX.symm]) hV hf ht
    (by rw [Category.assoc, Category.assoc, (Iso.inv_comp_eq (α := eX)).mpr heX.symm,
        (Iso.inv_comp_eq (α := eY)).mpr heY.symm]
        exact D'.cone_comm hV' hf' ht')

local notation "F" => compareHom D D' hV hf ht hV' hf' ht' eX eY heX heY
local notation "G" => compareInv D D' hV hf ht hV' hf' ht' eX eY heX heY

/-- **`compareHom` transports the first projection.** -/
theorem compareHom_comp_pr₁ :
    letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
    letI := D.topologyA; letI := D.isAdicA; letI := D.topologyB; letI := D.isAdicB
    F ≫ D'.pr₁ hV' hf' ht' = D.pr₁ hV hf ht ≫ eX.hom :=
  letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
  letI := D.topologyA; letI := D.isAdicA; letI := D.topologyB; letI := D.isAdicB
  D'.fibreLiftAdic_comp_pr₁ (D.pr₁ hV hf ht ≫ eX.hom) (D.pr₂ hV hf ht ≫ eY.hom)
    (D.pr₁ hV hf ht ≫ D.xStructMap) (D.adicOverBase_fibreStructMap hV hf ht) _ hV' hf' ht' _

/-- **`compareHom` transports the second projection.** -/
theorem compareHom_comp_pr₂ :
    letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
    letI := D.topologyA; letI := D.isAdicA; letI := D.topologyB; letI := D.isAdicB
    F ≫ D'.pr₂ hV' hf' ht' = D.pr₂ hV hf ht ≫ eY.hom :=
  letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
  letI := D.topologyA; letI := D.isAdicA; letI := D.topologyB; letI := D.isAdicB
  D'.fibreLiftAdic_comp_pr₂ (D.pr₁ hV hf ht ≫ eX.hom) (D.pr₂ hV hf ht ≫ eY.hom)
    (D.pr₁ hV hf ht ≫ D.xStructMap) (D.adicOverBase_fibreStructMap hV hf ht) _ hV' hf' ht' _

/-- **`compareInv` transports the first projection.** -/
theorem compareInv_comp_pr₁ :
    letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
    letI := D.topologyA; letI := D.isAdicA; letI := D.topologyB; letI := D.isAdicB
    G ≫ D.pr₁ hV hf ht = D'.pr₁ hV' hf' ht' ≫ eX.inv :=
  letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
  letI := D.topologyA; letI := D.isAdicA; letI := D.topologyB; letI := D.isAdicB
  D.fibreLiftAdic_comp_pr₁ (D'.pr₁ hV' hf' ht' ≫ eX.inv) (D'.pr₂ hV' hf' ht' ≫ eY.inv)
    (D'.pr₁ hV' hf' ht' ≫ D'.xStructMap) (D'.adicOverBase_fibreStructMap hV' hf' ht') _ hV hf ht _

/-- **`compareInv` transports the second projection.** -/
theorem compareInv_comp_pr₂ :
    letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
    letI := D.topologyA; letI := D.isAdicA; letI := D.topologyB; letI := D.isAdicB
    G ≫ D.pr₂ hV hf ht = D'.pr₂ hV' hf' ht' ≫ eY.inv :=
  letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
  letI := D.topologyA; letI := D.isAdicA; letI := D.topologyB; letI := D.isAdicB
  D.fibreLiftAdic_comp_pr₂ (D'.pr₁ hV' hf' ht' ≫ eX.inv) (D'.pr₂ hV' hf' ht' ≫ eY.inv)
    (D'.pr₁ hV' hf' ht' ≫ D'.xStructMap) (D'.adicOverBase_fibreStructMap hV' hf' ht') _ hV hf ht _

/-- **First round trip.** By uniqueness of the mediating morphism out of `D.generalFibreProduct`,
which is an admissible source by `adicOverBase_fibreStructMap`. -/
theorem compareHom_comp_compareInv :
    letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
    letI := D.topologyA; letI := D.isAdicA; letI := D.topologyB; letI := D.isAdicB
    F ≫ G = 𝟙 D.generalFibreProduct.toLocallyRingedSpace := by
  letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
  letI := D.topologyA; letI := D.isAdicA; letI := D.topologyB; letI := D.isAdicB
  have h₁ : (F ≫ G) ≫ D.pr₁ hV hf ht = 𝟙 _ ≫ D.pr₁ hV hf ht := by
    rw [Category.assoc, compareInv_comp_pr₁, ← Category.assoc, compareHom_comp_pr₁,
      Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  have h₂ : (F ≫ G) ≫ D.pr₂ hV hf ht = 𝟙 _ ≫ D.pr₂ hV hf ht := by
    rw [Category.assoc, compareInv_comp_pr₂, ← Category.assoc, compareHom_comp_pr₂,
      Category.assoc, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  refine D.fibreLift_unique_adicOverBase hV hf ht _ _ (D.pr₁ hV hf ht ≫ D.xStructMap)
    (D.adicOverBase_fibreStructMap hV hf ht) h₁ h₂ ?_
  rw [← Category.assoc, h₁, Category.id_comp]

/-- **Second round trip**, the mirror of `compareHom_comp_compareInv`. -/
theorem compareInv_comp_compareHom :
    letI := D'.commRingA; letI := D'.algebraA; letI := D'.commRingB; letI := D'.algebraB
    letI := D'.topologyA; letI := D'.isAdicA; letI := D'.topologyB; letI := D'.isAdicB
    G ≫ F = 𝟙 D'.generalFibreProduct.toLocallyRingedSpace := by
  letI := D'.commRingA; letI := D'.algebraA; letI := D'.commRingB; letI := D'.algebraB
  letI := D'.topologyA; letI := D'.isAdicA; letI := D'.topologyB; letI := D'.isAdicB
  have h₁ : (G ≫ F) ≫ D'.pr₁ hV' hf' ht' = 𝟙 _ ≫ D'.pr₁ hV' hf' ht' := by
    rw [Category.assoc, compareHom_comp_pr₁, ← Category.assoc, compareInv_comp_pr₁,
      Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  have h₂ : (G ≫ F) ≫ D'.pr₂ hV' hf' ht' = 𝟙 _ ≫ D'.pr₂ hV' hf' ht' := by
    rw [Category.assoc, compareHom_comp_pr₂, ← Category.assoc, compareInv_comp_pr₂,
      Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  refine D'.fibreLift_unique_adicOverBase hV' hf' ht' _ _ (D'.pr₁ hV' hf' ht' ≫ D'.xStructMap)
    (D'.adicOverBase_fibreStructMap hV' hf' ht') h₁ h₂ ?_
  rw [← Category.assoc, h₁, Category.id_comp]

/-- **The general fibre product is unique up to canonical isomorphism.** Two datums presenting the
same `X` and `Y` over the same adic base have canonically isomorphic fibre products; the
isomorphism is compatible with both projections by `compareHom_comp_pr₁`/`_comp_pr₂`. -/
def compareIso :
    letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
    letI := D.topologyA; letI := D.isAdicA; letI := D.topologyB; letI := D.isAdicB
    D.generalFibreProduct.toLocallyRingedSpace ≅ D'.generalFibreProduct.toLocallyRingedSpace :=
  letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
  letI := D.topologyA; letI := D.isAdicA; letI := D.topologyB; letI := D.isAdicB
  { hom := F
    inv := G
    hom_inv_id := compareHom_comp_compareInv D D' hV hf ht hV' hf' ht' eX eY heX heY
    inv_hom_id := compareInv_comp_compareHom D D' hV hf ht hV' hf' ht' eX eY heX heY }

end

end BothChartedFibreDatumXY

end AlgebraicGeometry

end
