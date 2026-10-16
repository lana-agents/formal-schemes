/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ProjectiveLineCharts
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# The projective line `ℙ¹_A` as a scheme

`ProjectiveLine.scheme A` is `Proj A[x₀, x₁]` (Mathlib's `AlgebraicGeometry.Proj`), with the
standard grading by total degree. It is separated (Mathlib) and proper over `Spec (A[x₀, x₁])₀`
(`ProjectiveLine.isProper_toSpecZero`). This file sets up its standard affine covering:

* `ProjectiveLine.U A k = D₊(x_k)`, affine (`ProjectiveLine.isAffineOpen_U`), with
  `U 0 ⊔ U 1 = ⊤` (`ProjectiveLine.U_sup`) and `U 0 ⊓ U 1 = D₊(x₀x₁)` affine;
* `ProjectiveLine.chartSections A k : Γ(ℙ¹_A, U k) ≃+* A[X]` and
  `ProjectiveLine.overlapSections A : Γ(ℙ¹_A, U 0 ⊓ U 1) ≃+* A[T;T⁻¹]`;
* `ProjectiveLine.overlapSections_res_zero`, `ProjectiveLine.overlapSections_res_one`: under these
  identifications the restriction maps are `p ↦ p(T)` and `q ↦ q(T⁻¹)`.

This is the covering used in Stacks, Section 30.8 (Tag 01XS), to compute the cohomology of
projective space by Čech cohomology (Stacks, Lemma 30.8.1, Tag 01XT).
-/

universe u

open AlgebraicGeometry CategoryTheory HomogeneousLocalization

namespace ProjectiveLine

variable (A : Type u) [CommRing A]

/-- The projective line `ℙ¹_A = Proj A[x₀, x₁]`. -/
noncomputable abbrev scheme : Scheme.{u} := Proj (grading A)

/-- The standard affine chart `D₊(x_k)` of `ℙ¹_A`. -/
noncomputable def U (k : Fin 2) : (scheme A).Opens :=
  Proj.basicOpen (grading A) (MvPolynomial.X k)

lemma isAffineOpen_U (k : Fin 2) : IsAffineOpen (U A k) :=
  Proj.isAffineOpen_basicOpen (grading A) (MvPolynomial.X k) (X_mem k) one_pos

lemma U_inf : U A 0 ⊓ U A 1 =
    Proj.basicOpen (grading A) (MvPolynomial.X 0 * MvPolynomial.X 1) :=
  (Proj.basicOpen_mul _ _ _).symm

lemma isAffineOpen_U_inf : IsAffineOpen (U A 0 ⊓ U A 1) := by
  rw [U_inf]
  exact Proj.isAffineOpen_basicOpen (grading A) _
    (SetLike.mul_mem_graded (X_mem 0) (X_mem 1)) two_pos

lemma adjoin_X_eq_top :
    Algebra.adjoin (grading A 0) (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) A)) =
      ⊤ := by
  rw [eq_top_iff]
  rintro p -
  induction p using MvPolynomial.induction_on with
  | C a => exact Subalgebra.algebraMap_mem _ (constZero A a)
  | add p q hp hq => exact add_mem hp hq
  | mul_X p i hp => exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)

instance : Algebra.FiniteType (grading A 0) (MvPolynomial (Fin 2) A) :=
  ⟨Subalgebra.fg_def.2 ⟨_, Set.finite_range _, adjoin_X_eq_top A⟩⟩

/-- `ℙ¹_A` is proper over `Spec (A[x₀, x₁])₀ = Spec A`. -/
instance isProper_toSpecZero : IsProper (Proj.toSpecZero (grading A)) := inferInstance

lemma U_sup : U A 0 ⊔ U A 1 = ⊤ := by
  have h := Proj.iSup_basicOpen_eq_top' (grading A) (fun k : Fin 2 ↦ MvPolynomial.X k)
    (fun k ↦ ⟨1, X_mem k⟩) (adjoin_X_eq_top A)
  rw [← h]
  refine le_antisymm (sup_le (le_iSup (fun k : Fin 2 ↦ U A k) 0) (le_iSup (fun k ↦ U A k) 1))
    (iSup_le fun k ↦ ?_)
  fin_cases k
  · exact le_sup_left
  · exact le_sup_right

/-- `Γ(ℙ¹_A, D₊(x_k)) ≃ A[X]`. -/
noncomputable def chartSections (k : Fin 2) : Γ(scheme A, U A k) ≃+* Polynomial A :=
  (Proj.basicOpenIsoAway (grading A) (MvPolynomial.X k) (X_mem k)
    one_pos).symm.commRingCatIsoToRingEquiv.trans (chartEquiv k)

lemma X01_mem : (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) A) ∈ grading A 2 :=
  SetLike.mul_mem_graded (X_mem 0) (X_mem 1)

/-- `Γ(ℙ¹_A, D₊(x₀) ∩ D₊(x₁)) ≃ A[T;T⁻¹]`. -/
noncomputable def overlapSections : Γ(scheme A, U A 0 ⊓ U A 1) ≃+* LaurentPolynomial A :=
  ((scheme A).presheaf.mapIso (eqToIso (U_inf A).symm).op ≪≫
    (Proj.basicOpenIsoAway (grading A) _ (X01_mem A) two_pos).symm).commRingCatIsoToRingEquiv.trans
    overlapEquiv

lemma inv_awayToSection {f : MvPolynomial (Fin 2) A} {m : ℕ} (hf : f ∈ grading A m) (hm : 0 < m)
    (a : Away (grading A) f) :
    (Proj.basicOpenIsoAway (grading A) f hf hm).inv (Proj.awayToSection (grading A) f a) = a := by
  rw [← Proj.basicOpenIsoAway_hom _ _ hf hm, ← CommRingCat.comp_apply, Iso.hom_inv_id,
    CommRingCat.id_apply]

lemma exists_awayToSection {f : MvPolynomial (Fin 2) A} {m : ℕ} (hf : f ∈ grading A m)
    (hm : 0 < m) (s : Γ(scheme A, Proj.basicOpen (grading A) f)) :
    ∃ a, Proj.awayToSection (grading A) f a = s :=
  ⟨(Proj.basicOpenIsoAway (grading A) f hf hm).inv s, by
    rw [← Proj.basicOpenIsoAway_hom _ _ hf hm, ← CommRingCat.comp_apply, Iso.inv_hom_id,
      CommRingCat.id_apply]⟩

lemma chartSections_awayToSection (k : Fin 2) (a : Away (grading A) (MvPolynomial.X k)) :
    chartSections A k (Proj.awayToSection (grading A) _ a) = chartEquiv k a := by
  change chartEquiv k ((Proj.basicOpenIsoAway (grading A) _ (X_mem k) one_pos).inv _) = _
  rw [inv_awayToSection]

lemma overlapSections_apply (t : Γ(scheme A, U A 0 ⊓ U A 1)) :
    overlapSections A t = overlapEquiv ((Proj.basicOpenIsoAway (grading A) _ (X01_mem A)
      two_pos).inv ((scheme A).presheaf.map (eqToHom (U_inf A).symm).op t)) := rfl

lemma overlapSections_res_zero (s : Γ(scheme A, U A 0)) :
    overlapSections A ((scheme A).presheaf.map (homOfLE inf_le_left).op s) =
      Polynomial.toLaurent (chartSections A 0 s) := by
  obtain ⟨a, rfl⟩ := exists_awayToSection A (X_mem 0) one_pos s
  have h := ConcreteCategory.congr_hom (Proj.awayMap_awayToSection (grading A)
    (f := MvPolynomial.X 0) (X_mem 1) (hx := X01_eq)) a
  have e : ∀ t, (scheme A).presheaf.map (eqToHom (U_inf A).symm).op
      ((scheme A).presheaf.map (homOfLE (inf_le_left : U A 0 ⊓ U A 1 ≤ _)).op t) =
      (scheme A).presheaf.map (homOfLE (Proj.basicOpen_mono (grading A) _ _
        ⟨_, X01_eq⟩)).op t := fun t ↦ by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  rw [overlapSections_apply, e]
  erw [← h]
  rw [CommRingCat.comp_apply, inv_awayToSection, chartSections_awayToSection]
  exact overlapEquiv_awayRes0 a

lemma overlapSections_res_one (s : Γ(scheme A, U A 1)) :
    overlapSections A ((scheme A).presheaf.map (homOfLE inf_le_right).op s) =
      LaurentPolynomial.invert (Polynomial.toLaurent (chartSections A 1 s)) := by
  obtain ⟨a, rfl⟩ := exists_awayToSection A (X_mem 1) one_pos s
  have h := ConcreteCategory.congr_hom (Proj.awayMap_awayToSection (grading A)
    (f := MvPolynomial.X 1) (X_mem 0) (hx := X01_eq')) a
  have e : ∀ t, (scheme A).presheaf.map (eqToHom (U_inf A).symm).op
      ((scheme A).presheaf.map (homOfLE (inf_le_right : U A 0 ⊓ U A 1 ≤ _)).op t) =
      (scheme A).presheaf.map (homOfLE (Proj.basicOpen_mono (grading A) _ _
        ⟨_, X01_eq'⟩)).op t := fun t ↦ by
    rw [← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  rw [overlapSections_apply, e]
  erw [← h]
  rw [CommRingCat.comp_apply, inv_awayToSection, chartSections_awayToSection]
  exact overlapEquiv_awayRes1 a

end ProjectiveLine
