/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartAlgebraScheme
import FormalSchemes.ChartedSchemeDatumDesc
import FormalSchemes.ProjectiveLineGlue

/-!
# The structure morphism of the scheme of a chart algebra

For a commutative chart algebra `B : ProjectiveLine.ChartModule.AlgStr M` on `ℙ¹_A`, the rings of
sections over the charts and the overlap are algebras over the coordinate rings `A[X]`, `A[Y]`,
`A[T, T⁻¹]` (`ProjectiveLine.ChartModule.AlgStr.polyHom0`,
`ProjectiveLine.ChartModule.AlgStr.polyHom1`, `ProjectiveLine.ChartModule.AlgStr.laurentHom`,
sending the coordinates to the chart coordinates of `B`), compatibly with restriction
(`ProjectiveLine.ChartModule.AlgStr.r0Hom_polyHom0`,
`ProjectiveLine.ChartModule.AlgStr.r1Hom_polyHom1`). Hence the chart morphisms
`Spec B₀ → Spec A[X] = U₀ ⊆ ℙ¹_A` and `Spec B₁ → U₁ ⊆ ℙ¹_A`
(`ProjectiveLine.ChartModule.AlgStr.chartMap0`, `ProjectiveLine.ChartModule.AlgStr.chartMap1`)
agree on the overlap, and glue (`AlgebraicGeometry.ChartedSchemeDatum.desc`) to the
**structure morphism** `ProjectiveLine.ChartModule.AlgStr.toP1` of the relative spectrum
`ProjectiveLine.ChartModule.AlgStr.scheme`, restricting to the chart morphisms on the charts
(`ProjectiveLine.ChartModule.AlgStr.schemeι_toP1_zero`,
`ProjectiveLine.ChartModule.AlgStr.schemeι_toP1_one`).
-/

universe u

open Polynomial AlgebraicGeometry CategoryTheory
open scoped LaurentPolynomial

namespace ProjectiveLine

namespace ChartModule

open BTensor

variable {A : Type u} [CommRing A]

namespace AlgStr

variable {M : ChartModule A} (B : AlgStr M)

/-- The constants `A → B₀`, `a ↦ a • 1`. -/
noncomputable def const0 : A →+* B.Ring0 where
  toFun a := (a • B.one.1.1 : M.M0)
  map_one' := show (1 : A) • (B.one.1.1 : M.M0) = B.one.1.1 from one_smul A _
  map_mul' a b := by
    change (a * b) • B.one.1.1 = B.mul.f0 (tm M.x0 M.x0 (a • B.one.1.1) (b • B.one.1.1))
    rw [tm_smul_left, tm_smul_right, map_smul, map_smul, B.one_mul0, mul_smul]
  map_zero' := show (0 : A) • (B.one.1.1 : M.M0) = (0 : M.M0) from zero_smul A _
  map_add' a b :=
    show (a + b) • (B.one.1.1 : M.M0) =
      a • B.one.1.1 + b • B.one.1.1 from add_smul a b _

/-- The constants `A → B₁`, `a ↦ a • 1`. -/
noncomputable def const1 : A →+* B.Ring1 where
  toFun a := (a • B.one.1.2 : M.M1)
  map_one' := show (1 : A) • (B.one.1.2 : M.M1) = B.one.1.2 from one_smul A _
  map_mul' a b := by
    change (a * b) • B.one.1.2 = B.mul.f1 (tm M.x1 M.x1 (a • B.one.1.2) (b • B.one.1.2))
    rw [tm_smul_left, tm_smul_right, map_smul, map_smul, B.one_mul1, mul_smul]
  map_zero' := show (0 : A) • (B.one.1.2 : M.M1) = (0 : M.M1) from zero_smul A _
  map_add' a b :=
    show (a + b) • (B.one.1.2 : M.M1) =
      a • B.one.1.2 + b • B.one.1.2 from add_smul a b _

/-- The constants `A → B₀₁`, `a ↦ a • 1`. -/
noncomputable def const01 : A →+* B.Ring01 where
  toFun a := (a • M.r0 B.one.1.1 : M.M01)
  map_one' := show (1 : A) • (M.r0 B.one.1.1 : M.M01) = M.r0 B.one.1.1 from one_smul A _
  map_mul' a b := by
    change (a * b) • M.r0 B.one.1.1 = B.mul.f01 (tm (M.t : M.M01 →ₗ[A] M.M01)
      (M.t : M.M01 →ₗ[A] M.M01) (a • M.r0 B.one.1.1) (b • M.r0 B.one.1.1))
    rw [tm_smul_left, tm_smul_right, map_smul, map_smul, B.one_mul01, mul_smul]
  map_zero' := show (0 : A) • (M.r0 B.one.1.1 : M.M01) = (0 : M.M01) from zero_smul A _
  map_add' a b :=
    show (a + b) • (M.r0 B.one.1.1 : M.M01) =
      a • M.r0 B.one.1.1 + b • M.r0 B.one.1.1 from add_smul a b _

lemma r0Hom_const0 (a : A) : B.r0Hom (B.const0 a) = B.const01 a :=
  map_smul M.r0 a B.one.1.1

lemma r1Hom_const1 (a : A) : B.r1Hom (B.const1 a) = B.const01 a := by
  change M.r1 (a • B.one.1.2) = a • M.r0 B.one.1.1
  rw [map_smul, (TwoCech.mem_H0.1 B.one.2)]

/-- `A[X] → B₀`, `X ↦ X₀`. -/
noncomputable def polyHom0 : A[X] →+* B.Ring0 := Polynomial.eval₂RingHom B.const0 B.X0

/-- `A[Y] → B₁`, `Y ↦ X₁`. -/
noncomputable def polyHom1 : A[X] →+* B.Ring1 := Polynomial.eval₂RingHom B.const1 B.X1

/-- `A[T, T⁻¹] → B₀₁`, `T ↦ T₀₁`. -/
noncomputable def laurentHom : A[T;T⁻¹] →+* B.Ring01 :=
  LaurentPolynomial.eval₂ B.const01 B.isUnit_T01.unit

lemma isUnit_T01_unit_inv : (↑B.isUnit_T01.unit⁻¹ : B.Ring01) = B.Tinv :=
  Units.inv_eq_of_mul_eq_one_right B.T01_mul_Tinv

lemma r0Hom_polyHom0 (p : A[X]) : B.r0Hom (B.polyHom0 p) = B.laurentHom (toLaurent p) := by
  have h : B.r0Hom.comp B.polyHom0 = B.laurentHom.comp toLaurent := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · simp [polyHom0, laurentHom, r0Hom_const0]
    · simp [polyHom0, laurentHom, r0Hom_X0]
  exact RingHom.congr_fun h p

lemma r1Hom_polyHom1 (q : A[X]) :
    B.r1Hom (B.polyHom1 q) = B.laurentHom (LaurentPolynomial.invert (toLaurent q)) := by
  have h : B.r1Hom.comp B.polyHom1 =
      B.laurentHom.comp
        ((LaurentPolynomial.invert : A[T;T⁻¹] ≃ₐ[A] A[T;T⁻¹]).toRingEquiv.toRingHom.comp
        toLaurent) := by
    refine Polynomial.ringHom_ext (fun a ↦ ?_) ?_
    · simp [polyHom1, laurentHom, r1Hom_const1]
    · simp only [polyHom1, laurentHom, RingHom.coe_comp, Function.comp_apply,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, r1Hom_X1, Polynomial.toLaurent_X]
      change _ = LaurentPolynomial.eval₂ _ _ (LaurentPolynomial.invert (LaurentPolynomial.T 1))
      rw [LaurentPolynomial.invert_T]
      have := LaurentPolynomial.eval₂_T_neg_n B.const01 B.isUnit_T01.unit 1
      simp only [Nat.cast_one, pow_one] at this
      rw [this, isUnit_T01_unit_inv]
  exact RingHom.congr_fun h q


/-! ### The chart morphisms to `ℙ¹_A` -/

/-- The ring map of the first chart, `Γ(ℙ¹_A, U₀) → B₀`. -/
noncomputable def chartHom0 : R A 0 ⟶ CommRingCat.of B.Ring0 :=
  CommRingCat.ofHom (B.polyHom0.comp (chartSections A 0).toRingHom)

/-- The ring map of the second chart, `Γ(ℙ¹_A, U₁) → B₁`. -/
noncomputable def chartHom1 : R A 1 ⟶ CommRingCat.of B.Ring1 :=
  CommRingCat.ofHom (B.polyHom1.comp (chartSections A 1).toRingHom)

/-- The ring map of the overlap, `Γ(ℙ¹_A, U₀ ∩ U₁) → B₀₁`. -/
noncomputable def overlapHom : R01 A ⟶ CommRingCat.of B.Ring01 :=
  CommRingCat.ofHom (B.laurentHom.comp (overlapSections A).toRingHom)

lemma chartHom0_r0Hom : B.chartHom0 ≫ CommRingCat.ofHom B.r0Hom = ρ A 0 ≫ B.overlapHom := by
  ext s
  change B.r0Hom (B.polyHom0 (chartSections A 0 s)) =
    B.laurentHom (overlapSections A
      ((ProjectiveLine.scheme A).presheaf.map (homOfLE inf_le_left).op s))
  rw [overlapSections_res_zero, r0Hom_polyHom0]

lemma chartHom1_r1Hom : B.chartHom1 ≫ CommRingCat.ofHom B.r1Hom = ρ A 1 ≫ B.overlapHom := by
  ext s
  change B.r1Hom (B.polyHom1 (chartSections A 1 s)) =
    B.laurentHom (overlapSections A
      ((ProjectiveLine.scheme A).presheaf.map (homOfLE inf_le_right).op s))
  rw [overlapSections_res_one, r1Hom_polyHom1]

/-- The first chart `Spec B₀ → Spec A[X] = U₀ ⊆ ℙ¹_A`. -/
noncomputable def chartMap0 : Spec (CommRingCat.of B.Ring0) ⟶ ProjectiveLine.scheme A :=
  Spec.map B.chartHom0 ≫ chartι A 0

/-- The second chart `Spec B₁ → Spec A[Y] = U₁ ⊆ ℙ¹_A`. -/
noncomputable def chartMap1 : Spec (CommRingCat.of B.Ring1) ⟶ ProjectiveLine.scheme A :=
  Spec.map B.chartHom1 ≫ chartι A 1

lemma specMap_comp_chartMap0 {S : CommRingCat.{u}} (χ : CommRingCat.of B.Ring01 ⟶ S)
    (u0 : CommRingCat.of B.Ring0 ⟶ S) (h0 : ∀ b, u0 b = χ (B.r0Hom b)) :
    Spec.map u0 ≫ B.chartMap0 = Spec.map (B.overlapHom ≫ χ) ≫ Spec.map (ρ A 0) ≫ chartι A 0 := by
  have e0 : u0 = CommRingCat.ofHom B.r0Hom ≫ χ := by ext b; exact h0 b
  rw [chartMap0, ← Category.assoc, ← Spec.map_comp, e0, ← Category.assoc, chartHom0_r0Hom,
    Category.assoc, Spec.map_comp, Category.assoc]

lemma specMap_comp_chartMap1 {S : CommRingCat.{u}} (χ : CommRingCat.of B.Ring01 ⟶ S)
    (u1 : CommRingCat.of B.Ring1 ⟶ S) (h1 : ∀ b, u1 b = χ (B.r1Hom b)) :
    Spec.map u1 ≫ B.chartMap1 = Spec.map (B.overlapHom ≫ χ) ≫ Spec.map (ρ A 1) ≫ chartι A 1 := by
  have e1 : u1 = CommRingCat.ofHom B.r1Hom ≫ χ := by ext b; exact h1 b
  rw [chartMap1, ← Category.assoc, ← Spec.map_comp, e1, ← Category.assoc, chartHom1_r1Hom,
    Category.assoc, Spec.map_comp, Category.assoc]

/-- **The two chart morphisms agree over the overlap**: two maps out of `B₀` and `B₁` which factor
through the restrictions to the overlap ring by the same map give the same morphism to `ℙ¹_A`. -/
lemma specMap_comp_chartMap_eq {S : CommRingCat.{u}} (χ : CommRingCat.of B.Ring01 ⟶ S)
    (u0 : CommRingCat.of B.Ring0 ⟶ S) (u1 : CommRingCat.of B.Ring1 ⟶ S)
    (h0 : ∀ b, u0 b = χ (B.r0Hom b)) (h1 : ∀ b, u1 b = χ (B.r1Hom b)) :
    Spec.map u0 ≫ B.chartMap0 = Spec.map u1 ≫ B.chartMap1 := by
  rw [B.specMap_comp_chartMap0 χ u0 h0, B.specMap_comp_chartMap1 χ u1 h1, chartι_comp]

/-- `B₀[1/X] ≃ B₀₁`. -/
noncomputable def locEquiv0 : Localization.Away B.X0 ≃+* B.Ring01 :=
  letI := B.r0Hom.toAlgebra
  haveI := B.isLocalization_r0
  (IsLocalization.algEquiv (Submonoid.powers B.X0) (Localization.Away B.X0) B.Ring01).toRingEquiv

/-- `B₁[1/Y] ≃ B₀₁`. -/
noncomputable def locEquiv1 : Localization.Away B.X1 ≃+* B.Ring01 :=
  letI := B.r1Hom.toAlgebra
  haveI := B.isLocalization_r1
  (IsLocalization.algEquiv (Submonoid.powers B.X1) (Localization.Away B.X1) B.Ring01).toRingEquiv

lemma overlapEquiv_eq : B.overlapEquiv = B.locEquiv0.trans B.locEquiv1.symm := rfl

lemma locEquiv0_algebraMap (b : B.Ring0) :
    B.locEquiv0 (algebraMap B.Ring0 (Localization.Away B.X0) b) = B.r0Hom b := by
  letI := B.r0Hom.toAlgebra
  haveI := B.isLocalization_r0
  exact (IsLocalization.algEquiv (Submonoid.powers B.X0) (Localization.Away B.X0)
    B.Ring01).commutes b

lemma locEquiv1_algebraMap (b : B.Ring1) :
    B.locEquiv1 (algebraMap B.Ring1 (Localization.Away B.X1) b) = B.r1Hom b := by
  letI := B.r1Hom.toAlgebra
  haveI := B.isLocalization_r1
  exact (IsLocalization.algEquiv (Submonoid.powers B.X1) (Localization.Away B.X1)
    B.Ring01).commutes b

lemma compat01 :
    Spec.map (CommRingCat.ofHom (algebraMap B.Ring0 (Localization.Away B.X0))) ≫ B.chartMap0 =
      Spec.map (CommRingCat.ofHom B.overlapEquiv.symm.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap B.Ring1 (Localization.Away B.X1))) ≫
          B.chartMap1 := by
  rw [← Category.assoc, ← Spec.map_comp]
  refine B.specMap_comp_chartMap_eq (CommRingCat.ofHom B.locEquiv0.symm.toRingHom) _ _
    (fun b ↦ ?_) (fun b ↦ ?_)
  · change _ = B.locEquiv0.symm (B.r0Hom b)
    rw [← locEquiv0_algebraMap, RingEquiv.symm_apply_apply]
    rfl
  · change B.overlapEquiv.symm (algebraMap B.Ring1 (Localization.Away B.X1) b) =
      B.locEquiv0.symm (B.r1Hom b)
    rw [overlapEquiv_eq, RingEquiv.symm_trans_apply, RingEquiv.symm_symm, locEquiv1_algebraMap]

lemma compat10 :
    Spec.map (CommRingCat.ofHom (algebraMap B.Ring1 (Localization.Away B.X1))) ≫ B.chartMap1 =
      Spec.map (CommRingCat.ofHom B.overlapEquiv.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap B.Ring0 (Localization.Away B.X0))) ≫
          B.chartMap0 := by
  rw [← Category.assoc, ← Spec.map_comp]
  refine (B.specMap_comp_chartMap_eq (CommRingCat.ofHom B.locEquiv1.symm.toRingHom) _ _
    (fun b ↦ ?_) (fun b ↦ ?_)).symm
  · change B.overlapEquiv (algebraMap B.Ring0 (Localization.Away B.X0) b) =
      B.locEquiv1.symm (B.r0Hom b)
    rw [overlapEquiv_eq, RingEquiv.trans_apply, locEquiv0_algebraMap]
  · change _ = B.locEquiv1.symm (B.r1Hom b)
    rw [← locEquiv1_algebraMap, RingEquiv.symm_apply_apply]
    rfl

/-- The chart morphisms, indexed by the charts of the gluing datum. -/
noncomputable def chartFamily (i : B.datum.J) :
    Spec.locallyRingedSpaceObj (CommRingCat.of (B.datum.C i)) ⟶
      (ProjectiveLine.scheme A).toLocallyRingedSpace :=
  match i with
  | ⟨false⟩ => B.chartMap0.toLRSHom
  | ⟨true⟩ => B.chartMap1.toLRSHom

lemma chartFamily_compat (i j : B.datum.J) (hij : i ≠ j) :
    specAwayMap (B.datum.g i j) ≫ B.chartFamily i =
      (specGlueIso (B.datum.g i j) (B.datum.g j i) (B.datum.θ i j hij)).hom ≫
        specAwayMap (B.datum.g j i) ≫ B.chartFamily j := by
  rcases i with ⟨_ | _⟩ <;> rcases j with ⟨_ | _⟩
  · exact absurd rfl hij
  · exact congrArg Scheme.Hom.toLRSHom B.compat01
  · exact congrArg Scheme.Hom.toLRSHom B.compat10
  · exact absurd rfl hij

/-- **The structure morphism** `B.scheme ⟶ ℙ¹_A` of the relative spectrum of a chart algebra,
glued from the chart morphisms `Spec B_k → U_k`. -/
noncomputable def toP1 : B.scheme ⟶ ProjectiveLine.scheme A :=
  ⟨B.datum.desc B.chartFamily B.chartFamily_compat⟩

lemma schemeι_toP1_zero : B.schemeι ⟨false⟩ ≫ B.toP1 = B.chartMap0 :=
  Scheme.Hom.ext' (B.datum.specι_desc B.chartFamily B.chartFamily_compat ⟨false⟩)

lemma schemeι_toP1_one : B.schemeι ⟨true⟩ ≫ B.toP1 = B.chartMap1 :=
  Scheme.Hom.ext' (B.datum.specι_desc B.chartFamily B.chartFamily_compat ⟨true⟩)

end AlgStr

end ChartModule

end ProjectiveLine
