import FormalSchemes.BothDatumFibreAdicOverBase
import FormalSchemes.GeneralFibreProductLiftAdic
import FormalSchemes.GeneralFibreProductLiftUniqueAdic

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The general fibre product is unique up to canonical isomorphism

Two two-sided fibre-product datums `D₁ D₂ : BothChartedFibreDatumXY R I hI` present *the same*
pair of factors when their glued factors are isomorphic over the base: isomorphisms of locally
ringed spaces `eX : X₁ ≅ X₂`, `eY : Y₁ ≅ Y₂` commuting with the two structural morphisms to
`Spf R`. This file shows that their fibre products are then canonically isomorphic,

```
compareIso : X₁ ×_{Spf R} Y₁ ≅ X₂ ×_{Spf R} Y₂
```

compatibly with both projections, and that the comparison is inverse to the comparison built from
`eX.symm`, `eY.symm`. This is the statement that `X ×_{Spf R} Y` does not depend on the *charts*
used to present `X` and `Y` — only on `X`, `Y` and their structural morphisms.

## What made this reachable

The universal property has had both halves since issues 794 (`fibreLiftAdic`, existence) and 518
(`fibreLift_unique_adicOverBase`, uniqueness), but each applies only to a source `Z` carrying
`FormalScheme.AdicOverBaseLocallyFG Z s`. Issue 832 supplied that witness **for the fibre product
itself** (`FormalSchemes.BothDatumFibreAdicOverBase`), which is what makes a fibre product an
admissible source, and hence what makes it possible to lift *out of* `X₁ ×_{Spf R} Y₁` and into
`X₂ ×_{Spf R} Y₂` at all. Before that witness existed neither `compareHom` nor the round trips
could be phrased.

## The argument

`compareHom` is `D₂.fibreLiftAdic` applied to the legs `pr₁ ≫ eX.hom` and `pr₂ ≫ eY.hom` out of
`D₁`'s fibre product. Its base morphism is taken to be `D₁`'s own `pr₁ ≫ xStructMap` rather than
the transported `(pr₁ ≫ eX.hom) ≫ D₂.xStructMap`; this is exactly what `fibreLiftAdic`'s
`s`/`hbase` parameterisation exists for (see its module docstring, "Which hypothesis, and why this
one"), and it lets issue 832's witness be handed over in the spelling it was proved in, with no
transport along an equality of morphisms into `Spf I`.

Note which hypotheses belong to which datum: the adic-over-base witness `hZadic` is `D₁`'s,
because `D₁`'s fibre product is the *source*, while the concreteness hypotheses `hV`/`hf`/`ht`
passed to `fibreLiftAdic` are `D₂`'s, because the lift is glued from `D₂`'s charts.

The round trip `compareHom eX eY ≫ compareHom eX.symm eY.symm` and the identity both restrict to
`pr₁` and `pr₂` in the same way, so `fibreLift_unique_adicOverBase` — again with `D₁`'s fibre
product as the source, again on issue 832's witness — identifies them. That is
`FormalSchemes.GeneralFibreProductLiftAdicSelf`'s `fibreLiftAdic_self` argument with `D₁ = D₂`
relaxed to two datums; the same remark applies about the right-hand side being the
**`LocallyRingedSpace`** identity `𝟙 D₁.generalFibreProduct.toLocallyRingedSpace`, since that is
the category `fibreLift_unique_adicOverBase` compares morphisms in.

`compareIso`'s `inv_hom_id` field is `compareHom_comp_compareHom` at `eX.symm`, `eY.symm`: the
statement it produces mentions `eX.symm.symm`, which is definitionally `eX` by structure eta, and
its two structural-compatibility arguments are `hX`, `hY` up to proof irrelevance.

## Spelling

`D₁` and `D₂` are **implicit**, inferred from `eX`, rather than explicit as house style would have
them. Dot notation cannot serve two datums symmetrically, and every declaration here already takes
six near-identical concreteness hypotheses; making the datums explicit as well buys nothing.

## Main results

* `BothChartedFibreDatumXY.inv_comp_xStructMap` / `inv_comp_yStructMap`: the backward structural
  compatibilities, free from the forward ones.
* `BothChartedFibreDatumXY.compareHom`: the comparison morphism.
* `BothChartedFibreDatumXY.compareHom_comp_pr₁` / `_comp_pr₂`: its two projection triangles.
* `BothChartedFibreDatumXY.compareHom_comp_compareHom`: the round trip is the identity.
* `BothChartedFibreDatumXY.compareIso`: **the canonical isomorphism**, with
  `compareIso_hom_comp_pr₁`/`_pr₂` and `compareIso_inv_comp_pr₁`/`_pr₂`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
-/

noncomputable section

open CategoryTheory TopologicalSpace Topology FormalSpectrum
open CompletedTensorProduct

universe u

namespace AlgebraicGeometry.BothChartedFibreDatumXY

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable [TopologicalSpace R] [IsAdicRing I]
variable {D₁ D₂ : BothChartedFibreDatumXY R I hI}
variable (eX : D₁.xGlued.toLocallyRingedSpace ≅ D₂.xGlued.toLocallyRingedSpace)
variable (eY : D₁.yGlued.toLocallyRingedSpace ≅ D₂.yGlued.toLocallyRingedSpace)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The backward structural compatibility on the `X`-side is free.** If `eX` commutes with the
two structural morphisms in the forward direction then so does `eX.symm`. -/
theorem inv_comp_xStructMap (hX : eX.hom ≫ D₂.xStructMap = D₁.xStructMap) :
    eX.inv ≫ D₁.xStructMap = D₂.xStructMap := by
  rw [← hX, Iso.inv_hom_id_assoc]

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The backward structural compatibility on the `Y`-side is free.** The `Y`-analogue of
`inv_comp_xStructMap`. -/
theorem inv_comp_yStructMap (hY : eY.hom ≫ D₂.yStructMap = D₁.yStructMap) :
    eY.inv ≫ D₁.yStructMap = D₂.yStructMap := by
  rw [← hY, Iso.inv_hom_id_assoc]

variable (hX : eX.hom ≫ D₂.xStructMap = D₁.xStructMap)
variable (hY : eY.hom ≫ D₂.yStructMap = D₁.yStructMap)
variable
  (hV₁ : letI := D₁.commRingA; letI := D₁.algebraA; letI := D₁.commRingB; letI := D₁.algebraB
    ∀ p p' (h : p ≠ p'), D₁.V p p' h = bothAlgDataV hI D₁.gX D₁.gY p p' h)
  (hf₁ : letI := D₁.commRingA; letI := D₁.algebraA; letI := D₁.commRingB; letI := D₁.algebraB
    ∀ p p' (h : p ≠ p'),
      D₁.f p p' h = eqToHom (hV₁ p p' h) ≫ bothAlgDataF hI D₁.gX D₁.gY p p' h)
  (ht₁ : letI := D₁.commRingA; letI := D₁.algebraA; letI := D₁.commRingB; letI := D₁.algebraB
    ∀ p p' (h : p ≠ p'),
      D₁.t p p' h = eqToHom (hV₁ p p' h) ≫ bothAlgDataT hI D₁.gX D₁.gY D₁.τX D₁.τY p p' h ≫
        eqToHom (hV₁ p' p h.symm).symm)
variable
  (hV₂ : letI := D₂.commRingA; letI := D₂.algebraA; letI := D₂.commRingB; letI := D₂.algebraB
    ∀ p p' (h : p ≠ p'), D₂.V p p' h = bothAlgDataV hI D₂.gX D₂.gY p p' h)
  (hf₂ : letI := D₂.commRingA; letI := D₂.algebraA; letI := D₂.commRingB; letI := D₂.algebraB
    ∀ p p' (h : p ≠ p'),
      D₂.f p p' h = eqToHom (hV₂ p p' h) ≫ bothAlgDataF hI D₂.gX D₂.gY p p' h)
  (ht₂ : letI := D₂.commRingA; letI := D₂.algebraA; letI := D₂.commRingB; letI := D₂.algebraB
    ∀ p p' (h : p ≠ p'),
      D₂.t p p' h = eqToHom (hV₂ p p' h) ≫ bothAlgDataT hI D₂.gX D₂.gY D₂.τX D₂.τY p p' h ≫
        eqToHom (hV₂ p' p h.symm).symm)

/-- **The comparison morphism** `X₁ ×_{Spf R} Y₁ ⟶ X₂ ×_{Spf R} Y₂` induced by isomorphisms
`eX : X₁ ≅ X₂`, `eY : Y₁ ≅ Y₂` of the factors over the base.

It is `D₂`'s mediating morphism for the legs `pr₁ ≫ eX.hom` and `pr₂ ≫ eY.hom`, which is available
because issue 832 makes `D₁`'s fibre product adic over its own base and hence an admissible source.
The base morphism is `D₁`'s `pr₁ ≫ xStructMap`, so that witness is used in the spelling it was
proved in; `hbase` absorbs the transport. -/
def compareHom :
    D₁.generalFibreProduct.toLocallyRingedSpace ⟶ D₂.generalFibreProduct.toLocallyRingedSpace :=
  D₂.fibreLiftAdic (D₁.pr₁ hV₁ hf₁ ht₁ ≫ eX.hom) (D₁.pr₂ hV₁ hf₁ ht₁ ≫ eY.hom)
    (D₁.pr₁ hV₁ hf₁ ht₁ ≫ D₁.xStructMap) (D₁.adicOverBase_fibreStructMap hV₁ hf₁ ht₁)
    (by rw [Category.assoc, hX]) hV₂ hf₂ ht₂
    (by rw [Category.assoc, Category.assoc, hX, hY, D₁.cone_comm hV₁ hf₁ ht₁])

/-- **The comparison morphism recovers the `X`-leg after the first projection.** -/
@[reassoc]
theorem compareHom_comp_pr₁ :
    compareHom eX eY hX hY hV₁ hf₁ ht₁ hV₂ hf₂ ht₂ ≫ D₂.pr₁ hV₂ hf₂ ht₂ =
      D₁.pr₁ hV₁ hf₁ ht₁ ≫ eX.hom :=
  D₂.fibreLiftAdic_comp_pr₁ _ _ _ _ _ hV₂ hf₂ ht₂ _

/-- **The comparison morphism recovers the `Y`-leg after the second projection.** -/
@[reassoc]
theorem compareHom_comp_pr₂ :
    compareHom eX eY hX hY hV₁ hf₁ ht₁ hV₂ hf₂ ht₂ ≫ D₂.pr₂ hV₂ hf₂ ht₂ =
      D₁.pr₂ hV₁ hf₁ ht₁ ≫ eY.hom :=
  D₂.fibreLiftAdic_comp_pr₂ _ _ _ _ _ hV₂ hf₂ ht₂ _

/-- **The round trip is the identity.** The comparison built from `eX`, `eY` followed by the one
built from `eX.symm`, `eY.symm` restricts to both projections exactly as the identity does, so
`fibreLift_unique_adicOverBase` — applied with `D₁`'s fibre product as the source, on issue 832's
adic-over-base witness — identifies the two.

The identity is the `LocallyRingedSpace` one, since that is the category
`fibreLift_unique_adicOverBase` compares morphisms in. -/
theorem compareHom_comp_compareHom
    (hX' : eX.inv ≫ D₁.xStructMap = D₂.xStructMap)
    (hY' : eY.inv ≫ D₁.yStructMap = D₂.yStructMap) :
    compareHom eX eY hX hY hV₁ hf₁ ht₁ hV₂ hf₂ ht₂ ≫
        compareHom eX.symm eY.symm hX' hY' hV₂ hf₂ ht₂ hV₁ hf₁ ht₁ =
      𝟙 D₁.generalFibreProduct.toLocallyRingedSpace := by
  have hpr₁ : (compareHom eX eY hX hY hV₁ hf₁ ht₁ hV₂ hf₂ ht₂ ≫
      compareHom eX.symm eY.symm hX' hY' hV₂ hf₂ ht₂ hV₁ hf₁ ht₁) ≫ D₁.pr₁ hV₁ hf₁ ht₁ =
      𝟙 D₁.generalFibreProduct.toLocallyRingedSpace ≫ D₁.pr₁ hV₁ hf₁ ht₁ := by
    rw [Category.assoc, compareHom_comp_pr₁, ← Category.assoc, compareHom_comp_pr₁,
      Category.assoc, Iso.symm_hom, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  refine D₁.fibreLift_unique_adicOverBase hV₁ hf₁ ht₁ _ _
    (D₁.pr₁ hV₁ hf₁ ht₁ ≫ D₁.xStructMap) (D₁.adicOverBase_fibreStructMap hV₁ hf₁ ht₁)
    hpr₁ ?_ ?_
  · rw [Category.assoc, compareHom_comp_pr₂, ← Category.assoc, compareHom_comp_pr₂,
      Category.assoc, Iso.symm_hom, Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · rw [← Category.assoc, hpr₁, Category.id_comp]

/-- **The general fibre product is unique up to canonical isomorphism.** Isomorphisms of the two
factors over `Spf R` induce an isomorphism of the fibre products, compatible with both projections
(`compareIso_hom_comp_pr₁`/`_pr₂`, `compareIso_inv_comp_pr₁`/`_pr₂`).

`inv_hom_id` is `compareHom_comp_compareHom` at `eX.symm`, `eY.symm`: the `eX.symm.symm` it
produces is definitionally `eX` by structure eta, and its compatibility arguments are `hX`, `hY` up
to proof irrelevance. -/
def compareIso :
    D₁.generalFibreProduct.toLocallyRingedSpace ≅ D₂.generalFibreProduct.toLocallyRingedSpace where
  hom := compareHom eX eY hX hY hV₁ hf₁ ht₁ hV₂ hf₂ ht₂
  inv := compareHom eX.symm eY.symm (inv_comp_xStructMap eX hX) (inv_comp_yStructMap eY hY)
    hV₂ hf₂ ht₂ hV₁ hf₁ ht₁
  hom_inv_id := compareHom_comp_compareHom eX eY hX hY hV₁ hf₁ ht₁ hV₂ hf₂ ht₂
    (inv_comp_xStructMap eX hX) (inv_comp_yStructMap eY hY)
  inv_hom_id := compareHom_comp_compareHom eX.symm eY.symm (inv_comp_xStructMap eX hX)
    (inv_comp_yStructMap eY hY) hV₂ hf₂ ht₂ hV₁ hf₁ ht₁ hX hY

@[simp]
theorem compareIso_hom :
    (compareIso eX eY hX hY hV₁ hf₁ ht₁ hV₂ hf₂ ht₂).hom =
      compareHom eX eY hX hY hV₁ hf₁ ht₁ hV₂ hf₂ ht₂ :=
  rfl

@[simp]
theorem compareIso_inv :
    (compareIso eX eY hX hY hV₁ hf₁ ht₁ hV₂ hf₂ ht₂).inv =
      compareHom eX.symm eY.symm (inv_comp_xStructMap eX hX) (inv_comp_yStructMap eY hY)
        hV₂ hf₂ ht₂ hV₁ hf₁ ht₁ :=
  rfl

/-- **The comparison isomorphism recovers the `X`-leg after the first projection.** -/
@[reassoc]
theorem compareIso_hom_comp_pr₁ :
    (compareIso eX eY hX hY hV₁ hf₁ ht₁ hV₂ hf₂ ht₂).hom ≫ D₂.pr₁ hV₂ hf₂ ht₂ =
      D₁.pr₁ hV₁ hf₁ ht₁ ≫ eX.hom :=
  compareHom_comp_pr₁ eX eY hX hY hV₁ hf₁ ht₁ hV₂ hf₂ ht₂

/-- **The comparison isomorphism recovers the `Y`-leg after the second projection.** -/
@[reassoc]
theorem compareIso_hom_comp_pr₂ :
    (compareIso eX eY hX hY hV₁ hf₁ ht₁ hV₂ hf₂ ht₂).hom ≫ D₂.pr₂ hV₂ hf₂ ht₂ =
      D₁.pr₂ hV₁ hf₁ ht₁ ≫ eY.hom :=
  compareHom_comp_pr₂ eX eY hX hY hV₁ hf₁ ht₁ hV₂ hf₂ ht₂

/-- **The inverse comparison recovers the `X`-leg after the first projection.** -/
@[reassoc]
theorem compareIso_inv_comp_pr₁ :
    (compareIso eX eY hX hY hV₁ hf₁ ht₁ hV₂ hf₂ ht₂).inv ≫ D₁.pr₁ hV₁ hf₁ ht₁ =
      D₂.pr₁ hV₂ hf₂ ht₂ ≫ eX.inv := by
  rw [compareIso_inv, compareHom_comp_pr₁, Iso.symm_hom]

/-- **The inverse comparison recovers the `Y`-leg after the second projection.** -/
@[reassoc]
theorem compareIso_inv_comp_pr₂ :
    (compareIso eX eY hX hY hV₁ hf₁ ht₁ hV₂ hf₂ ht₂).inv ≫ D₁.pr₂ hV₁ hf₁ ht₁ =
      D₂.pr₂ hV₂ hf₂ ht₂ ≫ eY.inv := by
  rw [compareIso_inv, compareHom_comp_pr₂, Iso.symm_hom]

end AlgebraicGeometry.BothChartedFibreDatumXY

end
