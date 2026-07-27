import FormalSchemes.TwoPatchFibreProductObject
import FormalSchemes.CompletedTensorAwayInterchangePr
import FormalSchemes.CompletedTensorMapSpfPr
import FormalSchemes.GlueMorphisms

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The second projection of the two-patch fibre product `X ×_{Spf R} Spf B`

`FormalSchemes.TwoPatchFibreProductObject` assembles the fibre product of the two-patch Tate model
`X = tateTwoPatch` with an affine base `Spf B` as a glued formal scheme `twoPatchFibreProduct`, two
copies of the chart `Spf(A ⊗̂_R B)` (`A = R{x,y}/(x·y−q)`) glued along the base-changed annulus
overlap transition `t = twoPatchFibreProductTransition`. This file builds the **second projection**
`pr₂ : X ×_{Spf R} Spf B ⟶ Spf B`, gluing the affine second projections `Spf(inr) : Spf(A ⊗̂_R B)
⟶ Spf B` across the two charts via `FormalScheme.GlueData.glueMorphisms`.

The compatibility datum `glueMorphisms` consumes on the double overlap is the naturality square

`interchange(x) ≫ inr = t.hom ≫ interchange(y) ≫ inr`

(`twoPatchFibreProduct_pr₂_naturality`), which is assembled from the two merged data:

* the away-localization interchange chart is a morphism over `Spf B`
  (`interchangeOpenImmersion_comp_locallyRingedSpaceMap_inr`,
  `FormalSchemes.CompletedTensorAwayInterchangePr`), and
* the transition `t = mapSpfIso` of the chart transition commutes with the `inr` projection
  (`CompletedTensorProduct.mapSpf_comp_inrMap` below, the raw-`locallyRingedSpaceMap` mirror of the
  merged `mapSpf_comp_fibrePr₂`, `FormalSchemes.CompletedTensorMapSpfPr`).

Everything is phrased in the instance-light world of `FormalSpectrum.locallyRingedSpaceMap` of the
`inr` homomorphisms (of which the affine `fibrePr₂` is `IsAdicHom.spfMap`, i.e. definitionally the
same map), so the base `B` needs no adic-ring hypothesis — matching how `twoPatchFibreProduct`
itself keeps `B` a bare `R`-algebra.

## Main definitions

* `CompletedTensorProduct.mapSpf_comp_inrMap`: the raw-`locallyRingedSpaceMap` naturality of the
  fibre-product map in the second projection.
* `AlgebraicGeometry.twoPatchFibreProduct_pr₂_naturality`: the double-overlap compatibility square.
* `AlgebraicGeometry.twoPatchFibreProductPr₂`: the glued second projection
  `X ×_{Spf R} Spf B ⟶ Spf B`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum
open CompletedTensorProduct CompletedTensorAwayInterchange

universe u

namespace CompletedTensorProduct

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {A B A' B' : Type u}
variable [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable [CommRing A'] [CommRing B'] [Algebra R A'] [Algebra R B']

/-- An `R`-algebra homomorphism carries the extended ideal of definition `I·A` onto `I·A'`; the
topology-free form of `algHom_isAdicHom_map`, needed to state the base map `Spf g` with raw
`locallyRingedSpaceMap`. -/
theorem algHom_map_isAdicHom (f : A →ₐ[R] A') :
    IsAdicHom (I.map (algebraMap R A)) (I.map (algebraMap R A')) f.toRingHom := by
  unfold IsAdicHom
  rw [Ideal.map_map,
    show f.toRingHom.comp (algebraMap R A) = algebraMap R A' from AlgHom.comp_algebraMap f]

/-- **Naturality of the second projection under `mapSpf`, in raw `locallyRingedSpaceMap` form.**
The functorial map `mapSpf hI f g : Spf(A' ⊗̂_R B') ⟶ Spf(A ⊗̂_R B)` composed with the second
projection `Spf(inr) : Spf(A ⊗̂_R B) ⟶ Spf B` equals the second projection of the source chart
followed by the map `Spf g : Spf B' ⟶ Spf B` on the base. This is the mirror of the merged
`mapSpf_comp_fibrePr₂` phrased with raw `locallyRingedSpaceMap` of the two `inr`s, so it needs no
adic-ring instance on `B`/`B'` and slots directly into the glued fibre-product projection. -/
theorem mapSpf_comp_inrMap (hI : I.FG) (f : A →ₐ[R] A') (g : B →ₐ[R] B') :
    haveI := isAdicRing R I A B hI
    haveI := isAdicRing R I A' B' hI
    mapSpf hI f g ≫ FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R B))
        (idealOfDefinition R I A B) (inr R I A B).toRingHom inr_isAdicHom.le_comap =
      FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R B'))
          (idealOfDefinition R I A' B') (inr R I A' B').toRingHom inr_isAdicHom.le_comap ≫
        FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R B)) (I.map (algebraMap R B'))
          g.toRingHom (algHom_map_isAdicHom g).le_comap := by
  haveI := isAdicRing R I A B hI
  haveI := isAdicRing R I A' B' hI
  simp only [mapSpf, IsAdicHom.spfMap]
  rw [← FormalSpectrum.locallyRingedSpaceMap_comp (I := I.map (algebraMap R B))
      (J := idealOfDefinition R I A B) (K := idealOfDefinition R I A' B')
      (φ := (inr R I A B).toRingHom) (ψ := map hI f g)
      (hIJ := inr_isAdicHom.le_comap) (hJK := (map_isAdicHom hI f g).le_comap)
      (hIK := (inr_isAdicHom.comp (map_isAdicHom hI f g)).le_comap),
    ← FormalSpectrum.locallyRingedSpaceMap_comp (I := I.map (algebraMap R B))
      (J := I.map (algebraMap R B')) (K := idealOfDefinition R I A' B')
      (φ := g.toRingHom) (ψ := (inr R I A' B').toRingHom)
      (hIJ := (algHom_map_isAdicHom g).le_comap) (hJK := inr_isAdicHom.le_comap)
      (hIK := ((algHom_map_isAdicHom g).comp inr_isAdicHom).le_comap)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _
    (RingHom.ext fun b => map_inr hI f g b)

end CompletedTensorProduct

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable (B : Type u) [CommRing B] [Algebra R B]

/-- The affine second projection `Spf((A_·) ⊗̂_R B) ⟶ Spf B`, as the raw `locallyRingedSpaceMap` of
`inr : B → (A_·) ⊗̂_R B`. Written raw so no adic-ring instance on `B` is needed. -/
def pr₂Chart (A : Type u) [CommRing A] [Algebra R A] :
    locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I A B) ⟶
      locallyRingedSpaceObj (I.map (algebraMap R B)) :=
  FormalSpectrum.locallyRingedSpaceMap (I.map (algebraMap R B))
    (CompletedTensorProduct.idealOfDefinition R I A B)
    (CompletedTensorProduct.inr R I A B).toRingHom CompletedTensorProduct.inr_isAdicHom.le_comap

/-- **The double-overlap compatibility square of the second projection.** The `x`-overlap chart
followed by the second projection equals the base-changed transition `t.hom` followed by the
`y`-overlap chart and the second projection — the datum `glueMorphisms` consumes to define `pr₂`
across the two charts. -/
theorem twoPatchFibreProduct_pr₂_naturality (hI : I.FG) :
    interchangeOpenImmersion (B := B) I (overlapX R I q) hI ≫
        pr₂Chart R I B (annulusAlgebra R I q) =
      (twoPatchFibreProductTransition R I q B hI).hom ≫
        interchangeOpenImmersion (B := B) I (overlapY R I q) hI ≫
          pr₂Chart R I B (annulusAlgebra R I q) := by
  simp only [pr₂Chart]
  rw [interchangeOpenImmersion_comp_locallyRingedSpaceMap_inr I (overlapX R I q) hI,
    interchangeOpenImmersion_comp_locallyRingedSpaceMap_inr I (overlapY R I q) hI,
    twoPatchFibreProductTransition, mapSpfIso_hom,
    mapSpf_comp_inrMap hI (annulusFibreChartTransitionAlg R I q hI).symm.toAlgHom
      (AlgEquiv.refl (R := R) (A₁ := B)).symm.toAlgHom]
  have hg : (((AlgEquiv.refl (R := R) (A₁ := B)).symm.toAlgHom : B →ₐ[R] B)).toRingHom =
      RingHom.id B := by
    ext b; simp
  rw [FormalSpectrum.locallyRingedSpaceMap_congr (φ₂ := RingHom.id B)
      (h₂ := (Ideal.comap_id (I.map (algebraMap R B))).ge) (hφ := hg),
    FormalSpectrum.locallyRingedSpaceMap_id, Category.comp_id]

/-- The reverse double-overlap compatibility square (`y`-side): derived from
`twoPatchFibreProduct_pr₂_naturality` by cancelling `t.inv ≫ t.hom`. -/
theorem twoPatchFibreProduct_pr₂_naturality' (hI : I.FG) :
    interchangeOpenImmersion (B := B) I (overlapY R I q) hI ≫
        pr₂Chart R I B (annulusAlgebra R I q) =
      (twoPatchFibreProductTransition R I q B hI).inv ≫
        interchangeOpenImmersion (B := B) I (overlapX R I q) hI ≫
          pr₂Chart R I B (annulusAlgebra R I q) := by
  rw [twoPatchFibreProduct_pr₂_naturality R I q B hI, ← Category.assoc,
    Iso.inv_hom_id, Category.id_comp]

/-- **The second projection of the two-patch fibre product** `pr₂ : X ×_{Spf R} Spf B ⟶ Spf B`,
glued from the two affine second projections `Spf(inr)` via
`FormalScheme.GlueData.glueMorphisms`, using the double-overlap compatibility squares. -/
def twoPatchFibreProductPr₂ (hI : I.FG) :
    (twoPatchFibreProduct R I q B hI).toLocallyRingedSpace ⟶
      locallyRingedSpaceObj (I.map (algebraMap R B)) :=
  (twoPatchFibreProductFormalGlueData R I q B hI).glueMorphisms
    (fun _ => pr₂Chart R I B (annulusAlgebra R I q)) (by
      intro i j
      rcases i with ⟨_ | _⟩ <;> rcases j with ⟨_ | _⟩
      · simp only [CategoryTheory.GlueData.t_id, Category.id_comp]
      · have h01 : ({ down := false } : ULift.{u} Bool) ≠ { down := true } := by decide
        have h10 : ({ down := true } : ULift.{u} Bool) ≠ { down := false } := by decide
        simp only [twoPatchFibreProductFormalGlueData, twoPatchFibreProductLRSGlueData,
          twoPatchFibreProductGlueData', CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', dif_neg h01, dif_neg h10, Category.assoc,
          eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        congr 1
        exact twoPatchFibreProduct_pr₂_naturality R I q B hI
      · have h01 : ({ down := false } : ULift.{u} Bool) ≠ { down := true } := by decide
        have h10 : ({ down := true } : ULift.{u} Bool) ≠ { down := false } := by decide
        simp only [twoPatchFibreProductFormalGlueData, twoPatchFibreProductLRSGlueData,
          twoPatchFibreProductGlueData', CategoryTheory.GlueData.ofGlueData',
          CategoryTheory.GlueData'.f', dif_neg h01, dif_neg h10, Category.assoc,
          eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        congr 1
        exact twoPatchFibreProduct_pr₂_naturality' R I q B hI
      · simp only [CategoryTheory.GlueData.t_id, Category.id_comp])

end AlgebraicGeometry
