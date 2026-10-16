/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartModuleCoker

/-!
# The Grothendieck existence theorem for `ℙ¹_A`

Let `A` be a Noetherian ring, complete with respect to an ideal `I`. Every adic system of coherent
modules on `ℙ¹_A` (`AdicChartSystem I`: coherent `Mₙ` on `ℙ¹_{A/Iⁿ}` with `M_{n+1}/Iⁿ = Mₙ`) is
the system of reductions of a coherent module `N` on `ℙ¹_A`
(`AdicChartSystem.exists_algebraization`): there are compatible chart-surjective morphisms
`N → Mₙ` with kernel `Iⁿ N`. Together with full faithfulness (`ChartModule.toHomSystem_bijective`)
this is the Grothendieck existence theorem for `ℙ¹_A` (Stacks, Lemma 30.24.3, Tag 0885).

The proof is Stacks': present the formal object as a quotient of `𝒪(-d)^ι`
(`AdicChartSystem.exists_compatible_surjection`), present the kernel (an adic system by the uniform
Artin–Rees lemma, `AdicChartSystem.kerSystem`) as a quotient of `𝒪(-e)^ι'`, algebraise the
resulting map `𝒪(-e)^ι' → 𝒪(-d)^ι` by full faithfulness, and take its cokernel.
-/

universe u

open Polynomial LaurentPolynomial

namespace ProjectiveLine

namespace AdicChartSystem

open ChartModule

variable {A : Type u} [CommRing A] {I : Ideal A}

/-- **Grothendieck existence for `ℙ¹_A`** (Stacks, Lemma 30.24.3, Tag 0885, for `X = ℙ¹_A`). -/
theorem exists_algebraization [IsNoetherianRing A] [IsAdicComplete I A] (S : AdicChartSystem I) :
    ∃ (N : ChartModule A) (_ : Module.Finite A[X] (Module.AEval' N.x0))
      (_ : Module.Finite A[X] (Module.AEval' N.x1)) (α : ∀ n, Hom N (S.M n)),
      (∀ n, Function.Surjective (α n).f0 ∧ Function.Surjective (α n).f1 ∧
        LinearMap.ker (α n).f0 = I ^ n • ⊤ ∧ LinearMap.ker (α n).f1 = I ^ n • ⊤) ∧
      ∀ m n (h : m ≤ n), (S.tr h).comp (α n) = α m := by
  classical
  obtain ⟨d, ι, _, _, φ, hφs, hφ⟩ := S.exists_compatible_surjection
  have hs0 : ∀ n, Function.Surjective (φ n).f0 := fun n ↦ (hφs n).1
  have hs1 : ∀ n, Function.Surjective (φ n).f1 := fun n ↦ (hφs n).2
  obtain ⟨c, hc⟩ := S.exists_stab hφ hs0 hs1
  let K := S.kerSystem hφ hs0 hs1 c (fun n n' h ↦ (hc n n' h).1) (fun n n' h ↦ (hc n n' h).2)
  obtain ⟨e, ι', _, _, ψ, hψs, hψ⟩ := K.exists_compatible_surjection
  let F := free (A := A) ι d
  let G' := free (A := A) ι' e
  -- the compatible maps `𝒪(-e)^ι' → G / Iⁿ G` with image `Lₙ`
  let un : ∀ n, Hom G' (F.quot (I ^ n)) := fun n ↦
    ((S.psi φ n).kerι.comp (S.KtoL hφ c n)).comp (ψ n)
  have hun : ∀ m n (h : m ≤ n), (F.quotMap (Ideal.pow_le_pow_right h)).comp (un n) = un m := by
    intro m n h
    have h1 : (F.quotMap (Ideal.pow_le_pow_right h)).comp (S.psi φ n).kerι =
        (S.psi φ m).kerι.comp (S.Lmap hφ h) := Hom.ext' rfl rfl rfl
    simp only [un, ← Hom.comp_assoc]
    rw [h1, Hom.comp_assoc (S.psi φ m).kerι, S.KtoL_comp hφ c h, Hom.comp_assoc,
      Hom.comp_assoc]
    have h2 : (S.Ktr hφ c h).comp (ψ n) = ψ m := hψ m n h
    rw [h2, Hom.comp_assoc]
  haveI := finite_free_x0 (A := A) (ι := ι) d
  haveI := finite_free_x1 (A := A) (ι := ι) d
  haveI := finite_free_x0 (A := A) (ι := ι') e
  haveI := finite_free_x1 (A := A) (ι := ι') e
  obtain ⟨uA, huA⟩ := (toHomSystem_bijective I G' F).2 ⟨un, hun⟩
  have huA' : ∀ n, (F.quotHom (I ^ n)).comp uA = un n := fun n ↦
    congrArg (fun x : HomSystem G' F I ↦ x.1 n) huA
  -- the cokernel
  let π := uA.cokerπ
  have hk0 : ∀ n, LinearMap.ker π.f0 ≤ LinearMap.ker (φ n).f0 := by
    intro n x hx
    rw [uA.ker_cokerπ0] at hx
    obtain ⟨p, rfl⟩ := hx
    rw [LinearMap.mem_ker, ← S.psi_f0_mk]
    have : (Submodule.Quotient.mk (uA.f0 p) : (F.quot (I ^ n)).M0) = (un n).f0 p :=
      congrArg (fun χ : Hom G' (F.quot (I ^ n)) ↦ χ.f0 p) (huA' n)
    rw [this]
    exact ((S.KtoL hφ c n).f0 ((ψ n).f0 p)).2
  have hk1 : ∀ n, LinearMap.ker π.f1 ≤ LinearMap.ker (φ n).f1 := by
    intro n x hx
    rw [uA.ker_cokerπ1] at hx
    obtain ⟨p, rfl⟩ := hx
    rw [LinearMap.mem_ker, ← S.psi_f1_mk]
    have : (Submodule.Quotient.mk (uA.f1 p) : (F.quot (I ^ n)).M1) = (un n).f1 p :=
      congrArg (fun χ : Hom G' (F.quot (I ^ n)) ↦ χ.f1 p) (huA' n)
    rw [this]
    exact ((S.KtoL hφ c n).f1 ((ψ n).f1 p)).2
  let α : ∀ n, Hom uA.coker (S.M n) := fun n ↦
    π.descend uA.cokerπ_surjective0 uA.cokerπ_surjective1 (φ n) (hk0 n) (hk1 n)
  have hα : ∀ n, (α n).comp π = φ n := fun n ↦ Hom.descend_comp _ _ _ _ _ _
  refine ⟨uA.coker, finite_coker_x0 uA, finite_coker_x1 uA, α, fun n ↦ ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro y
    obtain ⟨x, rfl⟩ := hs0 n y
    exact ⟨π.f0 x, congrArg (fun χ : Hom F (S.M n) ↦ χ.f0 x) (hα n)⟩
  · intro y
    obtain ⟨x, rfl⟩ := hs1 n y
    exact ⟨π.f1 x, congrArg (fun χ : Hom F (S.M n) ↦ χ.f1 x) (hα n)⟩
  · apply le_antisymm
    · intro y hy
      obtain ⟨x, rfl⟩ := uA.cokerπ_surjective0 y
      have hx : (φ n).f0 x = 0 := by
        rw [← congrArg (fun χ : Hom F (S.M n) ↦ χ.f0 x) (hα n)]
        exact hy
      have hxL : (Submodule.Quotient.mk x : (F.quot (I ^ n)).M0) ∈
          LinearMap.ker (S.psi φ n).f0 := by
        rw [LinearMap.mem_ker, S.psi_f0_mk]
        exact hx
      obtain ⟨w, hw⟩ := S.KtoL_surjective0 hφ hs0 c n ⟨_, hxL⟩
      obtain ⟨p, rfl⟩ := hψs n |>.1 w
      have h1 : (Submodule.Quotient.mk x : (F.quot (I ^ n)).M0) = (un n).f0 p :=
        (congrArg Subtype.val hw).symm
      rw [← congrArg (fun χ : Hom G' (F.quot (I ^ n)) ↦ χ.f0 p) (huA' n)] at h1
      have h2 : x - uA.f0 p ∈ I ^ n • (⊤ : Submodule A F.M0) :=
        (Submodule.Quotient.eq _).1 h1
      have h3 : π.f0 x = π.f0 (x - uA.f0 p) := by
        rw [map_sub, eq_comm, sub_eq_self]
        exact (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self _ p)
      rw [h3]
      have := Submodule.mem_map_of_mem (f := π.f0) h2
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2
        uA.cokerπ_surjective0] at this
      exact this
    · exact smul_le_ker_of_kill _ _ (S.kill0 n)
  · apply le_antisymm
    · intro y hy
      obtain ⟨x, rfl⟩ := uA.cokerπ_surjective1 y
      have hx : (φ n).f1 x = 0 := by
        rw [← congrArg (fun χ : Hom F (S.M n) ↦ χ.f1 x) (hα n)]
        exact hy
      have hxL : (Submodule.Quotient.mk x : (F.quot (I ^ n)).M1) ∈
          LinearMap.ker (S.psi φ n).f1 := by
        rw [LinearMap.mem_ker, S.psi_f1_mk]
        exact hx
      obtain ⟨w, hw⟩ := S.KtoL_surjective1 hφ hs1 c n ⟨_, hxL⟩
      obtain ⟨p, rfl⟩ := hψs n |>.2 w
      have h1 : (Submodule.Quotient.mk x : (F.quot (I ^ n)).M1) = (un n).f1 p :=
        (congrArg Subtype.val hw).symm
      rw [← congrArg (fun χ : Hom G' (F.quot (I ^ n)) ↦ χ.f1 p) (huA' n)] at h1
      have h2 : x - uA.f1 p ∈ I ^ n • (⊤ : Submodule A F.M1) :=
        (Submodule.Quotient.eq _).1 h1
      have h3 : π.f1 x = π.f1 (x - uA.f1 p) := by
        rw [map_sub, eq_comm, sub_eq_self]
        exact (Submodule.Quotient.mk_eq_zero _).2 (LinearMap.mem_range_self _ p)
      rw [h3]
      have := Submodule.mem_map_of_mem (f := π.f1) h2
      rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2
        uA.cokerπ_surjective1] at this
      exact this
    · exact smul_le_ker_of_kill _ _ (S.kill1 n)
  · intro m n h
    apply π.comp_cancel uA.cokerπ_surjective0 uA.cokerπ_surjective1
    rw [Hom.comp_assoc, hα, hα, hφ m n h]

end AdicChartSystem

end ProjectiveLine
