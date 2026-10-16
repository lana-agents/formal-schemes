/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ProjectiveLineScheme
import FormalSchemes.ProjectiveLineTwist
import FormalSchemes.TwoSetTwist

/-!
# Serre's twisting sheaves on `ℙ¹_A`

On `ℙ¹_A = Proj A[x₀, x₁]` (`FormalSchemes.ProjectiveLineScheme`) with its covering by
`U₀ = D₊(x₀)` and `U₁ = D₊(x₁)`, the transition function of `𝒪(d)` from the trivialisation by
`x₁ᵈ` on `U₁` to the one by `x₀ᵈ` on `U₀` is `(x₁/x₀)ᵈ = Tᵈ` on `U₀ ∩ U₁ = Spec A[T, T⁻¹]`
(Stacks, Section 27.10, Tag 01MM). So:

* `ProjectiveLine.serreTwist A F d` is the twist `F(d)` of an `𝒪_{ℙ¹}`-module `F` along the two
  charts by `Tᵈ` (`AlgebraicGeometry.Scheme.Modules.twist`);
* `ProjectiveLine.twistingSheaf A d = 𝒪(d)` is the twist of the structure sheaf;
* `ProjectiveLine.cechH0TwistingSheafEquiv`, `ProjectiveLine.cechH1TwistingSheafEquiv`: the Čech
  cohomology of `𝒪(d)` for the standard covering is the cohomology of
  `A[X] × A[X] → A[T, T⁻¹]`, `(p, q) ↦ p(T) - Tᵈ q(T⁻¹)`, computed in
  `FormalSchemes.ProjectiveLineTwist` (Stacks, Lemma 30.8.1, Tag 01XT);
* `ProjectiveLine.globalSectionsTwistingSheafEquiv`: `Γ(ℙ¹_A, 𝒪(d))` is that `H⁰`, so it vanishes
  for `d < 0` (`ProjectiveLine.subsingleton_globalSections_twistingSheaf`) and is `Aᵈ⁺¹` for
  `d ≥ 0` (`ProjectiveLine.globalSectionsTwistingSheafEquivPi`); and `Ȟ¹(𝒪(d)) = 0` for
  `d ≥ -1` (`ProjectiveLine.subsingleton_cechH1_twistingSheaf`).

The statements are phrased with the unfolded form `twist (structureSheaf A) (U A 0) (U A 1)
(transition A d)` of `ProjectiveLine.twistingSheaf A d`, which is definitionally equal to it.
-/

universe u

open AlgebraicGeometry CategoryTheory Opposite AlgebraicGeometry.Scheme.Modules

namespace ProjectiveLine

variable (A : Type u) [CommRing A]

/-- The structure sheaf of `ℙ¹_A`, as an `𝒪`-module. -/
noncomputable abbrev structureSheaf : (scheme A).Modules :=
  SheafOfModules.unit (scheme A).ringCatSheaf

/-- The sections of the structure sheaf as a module are the sections of the scheme. -/
noncomputable def structureSheafSectionsEquiv (W : (scheme A).Opens) :
    Γ(structureSheaf A, W) ≃+ Γ(scheme A, W) :=
  AddEquiv.refl _

/-- The transition function `Tᵈ = (x₁/x₀)ᵈ` of `𝒪(d)` on `U₀ ∩ U₁`. -/
noncomputable def transition (d : ℤ) : Γ(scheme A, U A 0 ⊓ U A 1) :=
  (overlapSections A).symm (LaurentPolynomial.T d)

lemma overlapSections_transition (d : ℤ) :
    overlapSections A (transition A d) = LaurentPolynomial.T d := by
  simp [transition]

lemma isUnit_transition (d : ℤ) : IsUnit (transition A d) :=
  IsUnit.of_mul_eq_one (transition A (-d)) <| (overlapSections A).injective <| by
    rw [map_mul, overlapSections_transition, overlapSections_transition, ← LaurentPolynomial.T_add,
      add_neg_cancel, LaurentPolynomial.T_zero, map_one]

/-- **Serre twist** `F(d)` of an `𝒪_{ℙ¹_A}`-module: `F|_{U₀}` and `F|_{U₁}` reglued along
multiplication by `Tᵈ` on `U₀ ∩ U₁`. -/
noncomputable abbrev serreTwist (F : (scheme A).Modules) (d : ℤ) : (scheme A).Modules :=
  twist F (U A 0) (U A 1) (transition A d)

/-- **Serre's twisting sheaf** `𝒪(d)` on `ℙ¹_A`. -/
noncomputable abbrev twistingSheaf (d : ℤ) : (scheme A).Modules :=
  serreTwist A (structureSheaf A) d

/-! ### The Čech cohomology of `𝒪(d)` -/

/-- `Γ(𝒪, U_k) ≃ A[X]`, as abelian groups. -/
noncomputable def chartSectionsℤ (k : Fin 2) :
    Γ(structureSheaf A, U A k) ≃ₗ[ℤ] Polynomial A :=
  ((structureSheafSectionsEquiv A _).trans (chartSections A k).toAddEquiv).toIntLinearEquiv

/-- `Γ(𝒪, U₀ ∩ U₁) ≃ A[T;T⁻¹]`, as abelian groups. -/
noncomputable def overlapSectionsℤ :
    Γ(structureSheaf A, U A 0 ⊓ U A 1) ≃ₗ[ℤ] LaurentPolynomial A :=
  ((structureSheafSectionsEquiv A _).trans (overlapSections A).toAddEquiv).toIntLinearEquiv

lemma cech_square_zero :
    (res0 A).restrictScalars ℤ ∘ₗ (chartSectionsℤ A 0).toLinearMap =
      (overlapSectionsℤ A).toLinearMap ∘ₗ
        resℤ (structureSheaf A) (inf_le_left : U A 0 ⊓ U A 1 ≤ U A 0) := by
  refine LinearMap.ext fun s ↦ ?_
  exact (overlapSections_res_zero A s).symm

lemma cech_square_one (d : ℤ) :
    (resInf A d).restrictScalars ℤ ∘ₗ (chartSectionsℤ A 1).toLinearMap =
      (overlapSectionsℤ A).toLinearMap ∘ₗ
        (smulℤ (structureSheaf A) (transition A d) ∘ₗ
          resℤ (structureSheaf A) (inf_le_right : U A 0 ⊓ U A 1 ≤ U A 1)) := by
  refine LinearMap.ext fun s ↦ ?_
  change LaurentPolynomial.T d * LaurentPolynomial.invert (Polynomial.toLaurent _) =
    overlapSections A (transition A d * _)
  rw [map_mul, overlapSections_transition]
  congr 1
  exact (overlapSections_res_one A s).symm

/-- **Čech `H⁰` of `𝒪(d)`**: for the standard covering of `ℙ¹_A` it is the kernel `H0 A d` of
`(p, q) ↦ p(T) - Tᵈ q(T⁻¹)` on `A[X] × A[X]` (`FormalSchemes.ProjectiveLineTwist`). -/
noncomputable def cechH0TwistingSheafEquiv (d : ℤ) :
    cechH0 (twist (structureSheaf A) (U A 0) (U A 1) (transition A d)) (U A 0) (U A 1) ≃ₗ[ℤ]
      (H0 A d).restrictScalars ℤ :=
  ((twistCechH0Equiv (M := structureSheaf A) (U := U A 0) (V := U A 1)
    (isUnit_transition A d)).trans
    (TwoCech.equivH0 (f := resℤ (structureSheaf A) (inf_le_left : U A 0 ⊓ U A 1 ≤ U A 0))
      (g := smulℤ (structureSheaf A) (transition A d) ∘ₗ
        resℤ (structureSheaf A) (inf_le_right : U A 0 ⊓ U A 1 ≤ U A 1))
      (f' := (res0 A).restrictScalars ℤ) (g' := (resInf A d).restrictScalars ℤ)
      (chartSectionsℤ A 0) (chartSectionsℤ A 1) (overlapSectionsℤ A)
      (cech_square_zero A) (cech_square_one A d))).trans
    (TwoCech.H0RestrictScalarsEquiv _ _)

/-- **Čech `H¹` of `𝒪(d)`**: for the standard covering of `ℙ¹_A` it is the cokernel `H1 A d` of
`(p, q) ↦ p(T) - Tᵈ q(T⁻¹)` (`FormalSchemes.ProjectiveLineTwist`). -/
noncomputable def cechH1TwistingSheafEquiv (d : ℤ) :
    cechH1 (twist (structureSheaf A) (U A 0) (U A 1) (transition A d)) (U A 0) (U A 1) ≃ₗ[ℤ]
      H1 A d :=
  ((twistCechH1Equiv (M := structureSheaf A) (U := U A 0) (V := U A 1)
    (isUnit_transition A d)).trans
    (TwoCech.equivH1 (f := resℤ (structureSheaf A) (inf_le_left : U A 0 ⊓ U A 1 ≤ U A 0))
      (g := smulℤ (structureSheaf A) (transition A d) ∘ₗ
        resℤ (structureSheaf A) (inf_le_right : U A 0 ⊓ U A 1 ≤ U A 1))
      (f' := (res0 A).restrictScalars ℤ) (g' := (resInf A d).restrictScalars ℤ)
      (chartSectionsℤ A 0) (chartSectionsℤ A 1) (overlapSectionsℤ A)
      (cech_square_zero A) (cech_square_one A d))).trans
    (TwoCech.H1RestrictScalarsEquiv _ _)

/-- `Γ(M, ⊤) ≃ Γ(M, U₀ ∪ U₁)` on `ℙ¹_A`. -/
noncomputable def topSectionsEquiv (M : (scheme A).Modules) :
    Γ(M, ⊤) ≃ₗ[ℤ] Γ(M, U A 0 ⊔ U A 1) :=
  (M.presheaf.mapIso (eqToIso (U_sup A)).op).addCommGroupIsoToAddEquiv.toIntLinearEquiv

/-- **Global sections of `𝒪(d)`**: `Γ(ℙ¹_A, 𝒪(d)) ≃ H0 A d`. -/
noncomputable def globalSectionsTwistingSheafEquiv (d : ℤ) :
    Γ(twist (structureSheaf A) (U A 0) (U A 1) (transition A d), ⊤) ≃ₗ[ℤ]
      (H0 A d).restrictScalars ℤ :=
  ((topSectionsEquiv A _).trans (cechH0Equiv _ (U A 0) (U A 1))).trans
    (cechH0TwistingSheafEquiv A d)

/-- `Γ(ℙ¹_A, 𝒪(d)) = 0` for `d < 0` (Stacks, Lemma 30.8.1, Tag 01XT). -/
theorem subsingleton_globalSections_twistingSheaf {d : ℤ} (hd : d < 0) :
    Subsingleton Γ(twist (structureSheaf A) (U A 0) (U A 1) (transition A d), ⊤) := by
  refine (globalSectionsTwistingSheafEquiv A d).toEquiv.subsingleton_congr.mpr ?_
  have : (H0 A d).restrictScalars ℤ = ⊥ := by
    rw [H0_eq_bot hd, Submodule.restrictScalars_bot]
  rw [this]
  infer_instance

/-- **`Γ(ℙ¹_A, 𝒪(e)) ≃ Aᵉ⁺¹`** for `e ≥ 0` (Stacks, Lemma 30.8.1, Tag 01XT). -/
noncomputable def globalSectionsTwistingSheafEquivPi (e : ℕ) :
    Γ(twist (structureSheaf A) (U A 0) (U A 1) (transition A e), ⊤) ≃ₗ[ℤ] (Fin (e + 1) → A) :=
  (globalSectionsTwistingSheafEquiv A e).trans ((H0Equiv (A := A) e).restrictScalars ℤ)

/-- `Ȟ¹(ℙ¹_A, 𝒪(d)) = 0` for `d ≥ -1` (Stacks, Lemma 30.8.1, Tag 01XT). -/
theorem subsingleton_cechH1_twistingSheaf {d : ℤ} (hd : -1 ≤ d) :
    Subsingleton (cechH1 (twist (structureSheaf A) (U A 0) (U A 1) (transition A d))
      (U A 0) (U A 1)) :=
  (cechH1TwistingSheafEquiv A d).toEquiv.subsingleton_congr.mpr (H1_subsingleton hd)

end ProjectiveLine
