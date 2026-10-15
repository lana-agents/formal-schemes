/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.AdicSystemModule
import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Algebraization of compatible systems of finite algebras

An `AdicAlgSystem I` is a compatible system `(Bₙ)ₙ` of finite `A`-algebras with `Bₙ` killed by
`I^(n+1)` and `Bₙ₊₁ ⧸ I^(n+1) Bₙ₊₁ ≅ Bₙ`: the affine form of a compatible system of coherent
algebras on the thickenings of a formal scheme, which is what the formal patching step of the tame
specialisation argument produces.

Over a Noetherian `I`-adically complete ring `A` such a system algebraizes, uniquely:

* `AdicAlgSystem.limit` is a finite `A`-algebra (`AdicAlgSystem.limit_finite`) with
  `limit ⧸ I^(n+1) ≃ₐ Bₙ` (`AdicAlgSystem.quotAlgEquiv`); this needs only precompleteness;
* a finite `A`-algebra `C` is recovered from its own system `(C ⧸ I^(n+1) C)ₙ`
  (`AdicAlgSystem.ofAlgebra`) as its limit, `AdicAlgSystem.algEquivLimit`.

The proofs reduce to the module statements of `FormalSchemes.AdicSystem` and
`FormalSchemes.AdicSystemModule` (Stacks, Lemma 30.23.1, Tag 087W, and Lemma 10.98.2,
Tag 09B8) through `AdicAlgSystem.toAdicSystem`.
-/

universe u v

open CategoryTheory

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- A compatible system of finite algebras over the thickenings `A ⧸ I^(n+1)`. -/
structure AdicAlgSystem where
  /-- The algebra at level `n`. -/
  B : ℕ → Type v
  [commRing : ∀ n, CommRing (B n)]
  [algebra : ∀ n, Algebra A (B n)]
  /-- The transition map from level `n + 1` to level `n`. -/
  map : ∀ n, B (n + 1) →ₐ[A] B n
  map_surjective : ∀ n, Function.Surjective (map n)
  ker_map : ∀ n, RingHom.ker (map n) = (I ^ (n + 1)).map (algebraMap A (B (n + 1)))
  map_pow_eq_bot : ∀ n, (I ^ (n + 1)).map (algebraMap A (B n)) = ⊥
  finite : ∀ n, Module.Finite A (B n)

namespace AdicAlgSystem

attribute [instance] commRing algebra

variable {I} (S : AdicAlgSystem.{u, v} I)

/-- The underlying adic system of modules. -/
abbrev toAdicSystem : AdicSystem.{u, v} I where
  obj n := ModuleCat.of A (S.B n)
  map n := ModuleCat.ofHom (S.map n).toLinearMap
  map_surjective n := S.map_surjective n
  ker_map n := by
    change LinearMap.ker (S.map n).toLinearMap = _
    rw [Ideal.smul_top_eq_map, ← S.ker_map]
    rfl
  pow_smul_top n := by
    change I ^ (n + 1) • (⊤ : Submodule A (S.B n)) = ⊥
    rw [Ideal.smul_top_eq_map, S.map_pow_eq_bot, Submodule.restrictScalars_bot]
  finite n := S.finite n

/-- The limit `lim Bₙ`, as a subalgebra of the product. -/
def limit : Subalgebra A (∀ n, S.B n) where
  carrier := {x | ∀ n, S.map n (x (n + 1)) = x n}
  mul_mem' {x y} hx hy n := by simp [hx n, hy n]
  add_mem' {x y} hx hy n := by simp [hx n, hy n]
  algebraMap_mem' r n := by simp

/-- The limit algebra and the limit of the underlying adic system are the same module. -/
def limitEquiv : S.limit ≃ₗ[A] S.toAdicSystem.limit where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The projection `lim Bₖ → Bₙ`, an algebra homomorphism. -/
def projAlg (n : ℕ) : S.limit →ₐ[A] S.B n :=
  (Pi.evalAlgHom A S.B n).comp S.limit.val

theorem projAlg_apply (n : ℕ) (x : S.limit) :
    S.projAlg n x = S.toAdicSystem.proj n (S.limitEquiv x) := rfl

theorem mem_smul_top_iff_of_linearEquiv {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (e : M ≃ₗ[A] N) (J : Ideal A) (x : M) :
    e x ∈ (J • ⊤ : Submodule A N) ↔ x ∈ (J • ⊤ : Submodule A M) := by
  have h : (J • ⊤ : Submodule A M).map e.toLinearMap = J • ⊤ := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  rw [← h, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply]

theorem projAlg_surjective (n : ℕ) : Function.Surjective (S.projAlg n) := by
  intro y
  obtain ⟨x, hx⟩ := S.toAdicSystem.proj_surjective n y
  exact ⟨S.limitEquiv.symm x, hx⟩

section Precomplete

variable [IsPrecomplete I A]

/-- **The limit of a compatible system of finite algebras is a finite algebra.** -/
instance limit_finite : Module.Finite A S.limit :=
  Module.Finite.equiv S.limitEquiv.symm

theorem ker_projAlg (n : ℕ) :
    RingHom.ker (S.projAlg n) = (I ^ (n + 1)).map (algebraMap A S.limit) := by
  ext x
  rw [RingHom.mem_ker, ← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map,
    ← mem_smul_top_iff_of_linearEquiv S.limitEquiv, ← AdicSystem.ker_proj, LinearMap.mem_ker,
    projAlg_apply]

/-- **`lim Bₖ ⧸ I^(n+1) ≃ₐ Bₙ`**: the limit algebraizes the system. -/
noncomputable def quotAlgEquiv (n : ℕ) :
    (S.limit ⧸ (I ^ (n + 1)).map (algebraMap A S.limit)) ≃ₐ[A] S.B n :=
  (Ideal.quotientEquivAlgOfEq A (S.ker_projAlg n).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (S.projAlg_surjective n))

end Precomplete

section OfAlgebra

variable (I) (C : Type v) [CommRing C] [Algebra A C]

theorem map_pow_succ_le (n : ℕ) :
    (I ^ (n + 1 + 1)).map (algebraMap A C) ≤ (I ^ (n + 1)).map (algebraMap A C) :=
  Ideal.map_mono (Ideal.pow_le_pow_right (by omega))

theorem map_algebraMap_quotient (J K : Ideal A) :
    J.map (algebraMap A (C ⧸ K.map (algebraMap A C))) =
      (J.map (algebraMap A C)).map (Ideal.Quotient.mk (K.map (algebraMap A C))) := by
  rw [Ideal.map_map]
  rfl

variable [Module.Finite A C]

/-- The system `(C ⧸ I^(n+1) C)ₙ` of a finite algebra. -/
def ofAlgebra : AdicAlgSystem.{u, v} I where
  B n := C ⧸ (I ^ (n + 1)).map (algebraMap A C)
  map n := Ideal.Quotient.factorₐ A (map_pow_succ_le I C n)
  map_surjective n := Ideal.Quotient.factor_surjective (map_pow_succ_le I C n)
  ker_map n := by
    change RingHom.ker (Ideal.Quotient.factor (map_pow_succ_le I C n)) = _
    rw [Ideal.Quotient.factor, Ideal.ker_quotient_lift, Ideal.mk_ker,
      map_algebraMap_quotient]
  map_pow_eq_bot n := by
    rw [map_algebraMap_quotient, Ideal.map_quotient_self]
  finite n := inferInstance

/-- The canonical map from a finite algebra to the limit of its system. -/
def toLimitAlg : C →ₐ[A] (ofAlgebra I C).limit :=
  (AlgHom.pi fun n ↦ Ideal.Quotient.mkₐ A ((I ^ (n + 1)).map (algebraMap A C))).codRestrict
    (ofAlgebra I C).limit fun _ _ ↦ rfl

theorem toLimitAlg_injective [IsNoetherianRing A] (h : I ≤ Ideal.jacobson ⊥) :
    Function.Injective (toLimitAlg I C) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  rw [← Submodule.mem_bot A, ← Ideal.iInf_pow_smul_eq_bot_of_le_jacobson I h]
  refine Submodule.mem_iInf _ |>.2 fun n ↦ ?_
  have hx' : Ideal.Quotient.mk ((I ^ (n + 1)).map (algebraMap A C)) x = 0 :=
    congrArg (fun y ↦ (ofAlgebra I C).projAlg n y) hx
  rw [Ideal.Quotient.eq_zero_iff_mem, ← Submodule.restrictScalars_mem A,
    ← Ideal.smul_top_eq_map] at hx'
  exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_succ n)) hx'

theorem toLimitAlg_surjective [IsPrecomplete I A] : Function.Surjective (toLimitAlg I C) := by
  have h := AdicSystem.surjective_of_proj_comp_surjective I C
    ((ofAlgebra I C).limitEquiv.toLinearMap ∘ₗ (toLimitAlg I C).toLinearMap)
    fun k ↦ Ideal.Quotient.mk_surjective
  intro y
  obtain ⟨x, hx⟩ := h ((ofAlgebra I C).limitEquiv y)
  exact ⟨x, (ofAlgebra I C).limitEquiv.injective hx⟩

/-- **Uniqueness of algebraization**: over a Noetherian `I`-adically complete ring, a finite
algebra is the limit of its own system `(C ⧸ I^(n+1) C)ₙ`. -/
noncomputable def algEquivLimit [IsNoetherianRing A] [IsAdicComplete I A] :
    C ≃ₐ[A] (ofAlgebra I C).limit :=
  AlgEquiv.ofBijective (toLimitAlg I C)
    ⟨toLimitAlg_injective I C (IsAdicComplete.le_jacobson_bot I), toLimitAlg_surjective I C⟩

end OfAlgebra

end AdicAlgSystem
