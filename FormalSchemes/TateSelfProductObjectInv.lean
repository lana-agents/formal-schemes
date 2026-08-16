import FormalSchemes.TateSelfProductCocycleInv
import FormalSchemes.TwoPatchFibreProduct

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The four-chart Tate self-fibre-product `𝔈_q ×_{Spf R} 𝔈_q` (𝔾m-inversion model)

This is the 𝔾m-**inversion** (issue 442/435c) analogue of `TateSelfProductObject`. It assembles the
four-chart glue datum for the self fibre product of the *corrected* (separated) Tate curve model,
over the honest 2-gon gluing, using the inversion transition fields
(`tateSelfProductGlueTInv`/`tateSelfProductGlueTInv'`/`tateSelfProductGlueTInv_fac`/
`tateSelfProductGlueTInv_inv`/`tateSelfProductGlueCocycleInv`) in place of the swap ones. The
transition-independent overlap fields (`tateSelfProductGlueV`/`GlueF`/`GlueF_mono`/`_hasPullback`/
`_isOpenImmersion`) are reused verbatim.

The result `tateSelfProductInv : FormalScheme` is the object that the atomic model flip (issue 446)
repoints the projections, cone and separatedness of `𝔈_q ×_{Spf R} 𝔈_q` onto.

## Main definitions

* `AlgebraicGeometry.tateSelfProductGlueData'Inv`: the inversion four-chart glue datum.
* `AlgebraicGeometry.tateSelfProductLRSGlueDataInv`, `...FormalGlueDataInv`.
* `AlgebraicGeometry.tateSelfProductInv`: the glued fibre product over the corrected model.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
  CompletedTensorProduct

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- On the lifted index `ULift (Bool × Bool)`, distinctness descends to the underlying pairs. -/
private theorem uliftDownNe {i j : ULift.{u} (Bool × Bool)} (h : i ≠ j) : i.down ≠ j.down := by
  intro e
  exact h (by rw [← ULift.up_down i, ← ULift.up_down j, e])

/-- The common chart `Spf(A ⊗̂_R A)`, the four patches to be glued. -/
private abbrev tspUInv : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj
    (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))

/-! ### The glue datum -/

/-- **The four-chart Tate self-fibre-product glue datum (inversion)** as a `GlueData'` on
`ULift (Bool × Bool)`: four copies of `Spf(A ⊗̂_R A)` glued along the merged overlap charts, with
the 𝔾m-inversion transitions `tateSelfProductGlueTInv`, transition-of-transitions
`tateSelfProductGlueTInv'`, its compatibility `tateSelfProductGlueTInv_fac`, and the genuine
three-fold `tateSelfProductGlueCocycleInv`. -/
def tateSelfProductGlueData'Inv (hq : q ∈ I) (hI : I.FG) :
    CategoryTheory.GlueData' LocallyRingedSpace.{u} where
  J := ULift.{u} (Bool × Bool)
  U := fun _ => tspUInv R I q
  V := fun i j h => tateSelfProductGlueV R I q hI i.down j.down (uliftDownNe h)
  f := fun i j h => tateSelfProductGlueF R I q hI i.down j.down (uliftDownNe h)
  f_mono := fun i j h => tateSelfProductGlueF_mono R I q hq hI i.down j.down (uliftDownNe h)
  f_hasPullback := fun i j k hij hik =>
    tateSelfProductGlueF_hasPullback R I q hq hI i.down j.down k.down
      (uliftDownNe hij) (uliftDownNe hik)
  t := fun i j h => tateSelfProductGlueTInv R I q hI i.down j.down (uliftDownNe h)
  t' := fun i j k hij hik hjk => by
    haveI := tateSelfProductGlueF_isOpenImmersion R I q hq hI i.down j.down (uliftDownNe hij)
    haveI := tateSelfProductGlueF_isOpenImmersion R I q hq hI i.down k.down (uliftDownNe hik)
    haveI := tateSelfProductGlueF_isOpenImmersion R I q hq hI j.down k.down (uliftDownNe hjk)
    exact tateSelfProductGlueTInv' R I q hI i.down j.down k.down
      (uliftDownNe hij) (uliftDownNe hik) (uliftDownNe hjk)
  t_fac := fun i j k hij hik hjk => by
    haveI := tateSelfProductGlueF_isOpenImmersion R I q hq hI i.down j.down (uliftDownNe hij)
    haveI := tateSelfProductGlueF_isOpenImmersion R I q hq hI i.down k.down (uliftDownNe hik)
    haveI := tateSelfProductGlueF_isOpenImmersion R I q hq hI j.down k.down (uliftDownNe hjk)
    exact tateSelfProductGlueTInv_fac R I q hI i.down j.down k.down
      (uliftDownNe hij) (uliftDownNe hik) (uliftDownNe hjk)
  t_inv := fun i j h => tateSelfProductGlueTInv_inv R I q hI i.down j.down (uliftDownNe h)
  cocycle := fun i j k hij hik hjk => by
    haveI := tateSelfProductGlueF_isOpenImmersion R I q hq hI i.down j.down (uliftDownNe hij)
    haveI := tateSelfProductGlueF_isOpenImmersion R I q hq hI i.down k.down (uliftDownNe hik)
    haveI := tateSelfProductGlueF_isOpenImmersion R I q hq hI j.down k.down (uliftDownNe hjk)
    haveI := tateSelfProductGlueF_isOpenImmersion R I q hq hI j.down i.down (uliftDownNe hij).symm
    haveI := tateSelfProductGlueF_isOpenImmersion R I q hq hI k.down i.down (uliftDownNe hik).symm
    haveI := tateSelfProductGlueF_isOpenImmersion R I q hq hI k.down j.down (uliftDownNe hjk).symm
    exact tateSelfProductGlueCocycleInv R I q hq hI i.down j.down k.down
      (uliftDownNe hij) (uliftDownNe hik) (uliftDownNe hjk)

/-- **The inversion glue datum as a `LocallyRingedSpace.GlueData`**, via `GlueData.ofGlueData'`
together with the open-immersion field `f_open`. -/
def tateSelfProductLRSGlueDataInv (hq : q ∈ I) (hI : I.FG) : LocallyRingedSpace.GlueData.{u} :=
  { CategoryTheory.GlueData.ofGlueData' (tateSelfProductGlueData'Inv R I q hq hI) with
    f_open := by
      rintro i j
      simp only [CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f']
      split_ifs with h
      · exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (eqToHom _))
      · haveI := tateSelfProductGlueF_isOpenImmersion R I q hq hI i.down j.down (uliftDownNe h)
        exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
          (eqToHom _ ≫ tateSelfProductGlueF R I q hI i.down j.down (uliftDownNe h))) }

/-- **The inversion glue datum as a `FormalScheme.GlueData`**: each of the four pieces is the affine
formal scheme `Spf(A ⊗̂_R A)`. -/
def tateSelfProductFormalGlueDataInv (hq : q ∈ I) (hI : I.FG) : FormalScheme.GlueData.{u} :=
  haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I (annulusAlgebra R I q) (annulusAlgebra R I q) hI
  { toLocallyRingedSpaceGlueData := tateSelfProductLRSGlueDataInv R I q hq hI
    isFormalScheme := fun _ =>
      ⟨FormalScheme.Spf (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
          (annulusAlgebra R I q)),
        ⟨Iso.refl _⟩⟩ }

/-- **The four-chart Tate self-fibre product `𝔈_q ×_{Spf R} 𝔈_q` over the corrected (separated)
model**: the (non-affine) formal scheme obtained by gluing the four copies of `Spf(A ⊗̂_R A)` along
the merged overlap charts and the 𝔾m-inversion transitions. The inversion analogue of
`tateSelfProduct`; consumed by the atomic model flip (issue 446). -/
def tateSelfProductInv (hq : q ∈ I) (hI : I.FG) : FormalScheme.{u} :=
  (tateSelfProductFormalGlueDataInv R I q hq hI).gluedFormalScheme

end AlgebraicGeometry
