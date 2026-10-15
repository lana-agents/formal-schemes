/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.AdicSystem
import Mathlib.RingTheory.AdicCompletion.Noetherian

/-!
# The adic system of a finite module, and completeness of finite modules

For a finite `A`-module `M`, the quotients `M ⧸ I^(n+1) M` form an `AdicSystem I`,
`AdicSystem.ofModule I M`, and `AdicSystem.toLimit` is the canonical map from `M` to its limit.
Over an `I`-adically precomplete ring this map is surjective (`AdicSystem.toLimit_surjective`),
by the successive approximation `AdicSystem.exists_coeff`; over a Noetherian ring with `I` in the
Jacobson radical it is injective by the Krull intersection theorem
(`AdicSystem.toLimit_injective`).

Consequently a finite module over an `I`-adically complete Noetherian ring is `I`-adically complete
(`AdicSystem.isAdicComplete_of_finite`; Stacks, Tag 00MA), and more generally finite modules over
a precomplete ring are precomplete (`AdicSystem.isPrecomplete_of_finite`).
-/

universe u v

open CategoryTheory

variable {A : Type u} [CommRing A] (I : Ideal A)

namespace AdicSystem

variable {M : Type v} [AddCommGroup M] [Module A M]

theorem smul_top_quotient (J : Ideal A) (p : Submodule A M) :
    J • (⊤ : Submodule A (M ⧸ p)) = (J • ⊤ : Submodule A M).map p.mkQ := by
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]

theorem ker_factor {p p' : Submodule A M} (h : p ≤ p') :
    LinearMap.ker (Submodule.factor h) = p'.map p.mkQ := by
  rw [← Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective p)
    (LinearMap.ker (Submodule.factor h)), ← LinearMap.ker_comp, Submodule.factor_comp_mk,
    Submodule.ker_mkQ]

theorem pow_succ_smul_le (n : ℕ) :
    (I ^ (n + 1 + 1) • ⊤ : Submodule A M) ≤ I ^ (n + 1) • ⊤ :=
  Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))

variable (M) [Module.Finite A M]

/-- The adic system `(M ⧸ I^(n+1) M)ₙ` of a finite module. -/
abbrev ofModule : AdicSystem.{u, v} I where
  obj n := ModuleCat.of A (M ⧸ (I ^ (n + 1) • ⊤ : Submodule A M))
  map n := ModuleCat.ofHom (Submodule.factor (pow_succ_smul_le (M := M) I n))
  map_surjective n := Submodule.factor_surjective (pow_succ_smul_le (M := M) I n)
  ker_map n := by
    change LinearMap.ker (Submodule.factor (pow_succ_smul_le (M := M) I n)) = _
    rw [ker_factor, smul_top_quotient]
  pow_smul_top n := by
    change I ^ (n + 1) • (⊤ : Submodule A (M ⧸ (I ^ (n + 1) • ⊤ : Submodule A M))) = ⊥
    rw [smul_top_quotient, Submodule.mkQ_map_self]
  finite n := by
    change Module.Finite A (M ⧸ (I ^ (n + 1) • ⊤ : Submodule A M))
    infer_instance

/-- The canonical map from a finite module to the limit of its adic system. -/
def toLimit : M →ₗ[A] (ofModule I M).limit :=
  LinearMap.codRestrict (ofModule I M).limit
    (LinearMap.pi fun n ↦ (I ^ (n + 1) • ⊤ : Submodule A M).mkQ) fun _ _ ↦ rfl

@[simp]
theorem proj_toLimit (n : ℕ) (x : M) :
    (ofModule I M).proj n (toLimit I M x) = Submodule.Quotient.mk x := rfl

/-- Over a precomplete ring, a linear map from a finite module to the limit of an adic system is
surjective as soon as each of its levels is. -/
theorem surjective_of_proj_comp_surjective [IsPrecomplete I A]
    {S : AdicSystem.{u, v} I} (φ : M →ₗ[A] S.limit)
    (hφ : ∀ k, Function.Surjective (S.proj k ∘ₗ φ)) : Function.Surjective φ := by
  obtain ⟨t, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := M)
  have hspan : ∀ k, Submodule.span A (Set.range fun i ↦ S.proj k (φ (s i))) = ⊤ := by
    intro k
    change Submodule.span A (Set.range ((S.proj k ∘ₗ φ) ∘ s)) = ⊤
    rw [Set.range_comp, ← Submodule.map_span, hs, Submodule.map_top,
      LinearMap.range_eq_top.2 (hφ k)]
  intro m
  obtain ⟨a₀, ha₀⟩ := (Submodule.mem_span_range_iff_exists_fun A).1
    ((hspan 0).symm ▸ Submodule.mem_top : S.proj 0 m ∈ _)
  obtain ⟨a, -, ha⟩ := S.exists_coeff _ hspan m 0 a₀ ha₀
  exact ⟨∑ i, a i • s i, by simp [map_sum, map_smul, ha]⟩

/-- Over a precomplete ring, every element of the limit of the adic system of a finite module
comes from the module. -/
theorem toLimit_surjective [IsPrecomplete I A] : Function.Surjective (toLimit I M) :=
  surjective_of_proj_comp_surjective I M (toLimit I M) fun _ ↦ Submodule.mkQ_surjective _

/-- Over a Noetherian ring with `I` in the Jacobson radical, the map from a finite module to the
limit of its adic system is injective (Krull intersection theorem). -/
theorem toLimit_injective [IsNoetherianRing A] (h : I ≤ Ideal.jacobson ⊥) :
    Function.Injective (toLimit I M) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff, ← Ideal.iInf_pow_smul_eq_bot_of_le_jacobson I h]
  intro x hx
  refine Submodule.mem_iInf _ |>.2 fun n ↦ ?_
  have hx' : (Submodule.Quotient.mk x : M ⧸ (I ^ (n + 1) • ⊤ : Submodule A M)) = 0 :=
    (congrArg (fun y ↦ (ofModule I M).proj n y) (LinearMap.mem_ker.1 hx)).trans (map_zero _)
  rw [Submodule.Quotient.mk_eq_zero] at hx'
  exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n)) hx'

theorem toLimit_bijective [IsNoetherianRing A] [IsAdicComplete I A] :
    Function.Bijective (toLimit I M) :=
  ⟨toLimit_injective I M (IsAdicComplete.le_jacobson_bot I), toLimit_surjective I M⟩

/-- A finite module over an `I`-adically precomplete ring is `I`-adically precomplete. -/
theorem isPrecomplete_of_finite [IsPrecomplete I A] : IsPrecomplete I M where
  prec' f hf := by
    let y : (ofModule I M).limit :=
      ⟨fun n ↦ Submodule.Quotient.mk (f (n + 1)), fun n ↦ (hf (by omega : n + 1 ≤ n + 2)).symm⟩
    obtain ⟨L, hL⟩ := toLimit_surjective I M y
    refine ⟨L, fun n ↦ ?_⟩
    cases n with
    | zero => simp [SModEq.top]
    | succ n =>
      have := congrArg (fun z ↦ (ofModule I M).proj n z) hL
      exact this.symm

/-- **A finite module over an `I`-adically complete Noetherian ring is `I`-adically complete**
(Stacks, Lemma 10.96.11, Tag 031B, whose separatedness hypothesis is the Krull intersection
theorem here). -/
theorem isAdicComplete_of_finite [IsNoetherianRing A] [IsAdicComplete I A] :
    IsAdicComplete I M where
  toIsHausdorff := IsHausdorff.of_le_jacobson I M (IsAdicComplete.le_jacobson_bot I)
  toIsPrecomplete := isPrecomplete_of_finite I M

end AdicSystem
