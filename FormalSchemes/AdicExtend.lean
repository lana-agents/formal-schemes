import FormalSchemes.AdicCompletionLimit
import Mathlib.RingTheory.AdicCompletion.RingHom

set_option linter.style.header false

/-!
# Continuous extension of ring homomorphisms to adic completions

A ring homomorphism `ψ : B →+* S` into an `L`-adically complete ring which is *continuous* for
the `K`-adic topology of `B` — meaning `ψ (K ^ m) ⊆ L ^ m` for all `m` — extends uniquely to
the completion: `AdicCompletion.extendRingHom : AdicCompletion K B →+* S`, restricting to `ψ`
on `B` (`AdicCompletion.extendRingHom_of`).

This is the workhorse behind the universal properties of the restricted power series rings
(evaluation on the formal polydisc) and of the formal multiplicative group (evaluation at a
unit): in each case the map on the dense subring is given by ordinary (Laurent) polynomial
evaluation, and this file provides the passage to the completion.

We also record the common source of the continuity hypothesis: an `R`-algebra homomorphism
`B →ₐ[R] S` maps the powers of the extended ideal `I·B` into the powers of any `L ⊇ I·S`
(`Ideal.map_algebraMap_pow_le_comap`).

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. 0, §7.6.
-/

noncomputable section

open Ideal

universe u

namespace AdicCompletion

variable {B S : Type u} [CommRing B] [CommRing S] (K : Ideal B) (L : Ideal S)
variable [IsAdicComplete L S] (ψ : B →+* S) (hψ : ∀ m : ℕ, K ^ m ≤ (L ^ m).comap ψ)

/-- The level-`m` component of the continuous extension: evaluate in `B ⧸ K ^ m` and push
into `S ⧸ L ^ m`. -/
def extendLevel (m : ℕ) : AdicCompletion K B →+* S ⧸ L ^ m :=
  (Ideal.quotientMap (L ^ m) ψ (hψ m)).comp (AdicCompletion.evalₐ K m).toRingHom

theorem extendLevel_of (m : ℕ) (b : B) :
    extendLevel K L ψ hψ m (AdicCompletion.of K B b) = Ideal.Quotient.mk (L ^ m) (ψ b) := by
  simp only [extendLevel, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe]
  rw [AdicCompletion.evalₐ_of, Ideal.quotientMap_mk]

theorem factorPow_comp_extendLevel {m m' : ℕ} (hle : m ≤ m') :
    (Ideal.Quotient.factorPow L hle).comp (extendLevel K L ψ hψ m') =
      extendLevel K L ψ hψ m := by
  refine RingHom.ext fun x => ?_
  simp only [RingHom.coe_comp, Function.comp_apply, extendLevel]
  have key : ∀ b : B ⧸ K ^ m',
      Ideal.Quotient.factorPow L hle (Ideal.quotientMap (L ^ m') ψ (hψ m') b) =
      Ideal.quotientMap (L ^ m) ψ (hψ m) (Ideal.Quotient.factorPow K hle b) := by
    intro b
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [Ideal.quotientMap_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk,
      Ideal.quotientMap_mk]
  rw [key]
  congr 1
  exact AdicCompletion.factorPow_evalₐ K hle x

/-- **Continuous extension to the completion**: a ring homomorphism into an `L`-adically
complete ring carrying `K ^ m` into `L ^ m` for every `m` extends to the `K`-adic
completion. -/
def extendRingHom : AdicCompletion K B →+* S :=
  IsAdicComplete.liftRingHom L (fun m => extendLevel K L ψ hψ m)
    (fun hle => factorPow_comp_extendLevel K L ψ hψ hle)

theorem mk_extendRingHom (m : ℕ) (x : AdicCompletion K B) :
    Ideal.Quotient.mk (L ^ m) (extendRingHom K L ψ hψ x) = extendLevel K L ψ hψ m x :=
  IsAdicComplete.mk_liftRingHom _ _ _ _ _

/-- The continuous extension restricts to `ψ` on `B`. -/
theorem extendRingHom_of (b : B) :
    extendRingHom K L ψ hψ (AdicCompletion.of K B b) = ψ b := by
  have h : ∀ m : ℕ, Ideal.Quotient.mk (L ^ m)
      (extendRingHom K L ψ hψ (AdicCompletion.of K B b)) =
      Ideal.Quotient.mk (L ^ m) (ψ b) := fun m => by
    rw [mk_extendRingHom, extendLevel_of]
  have hmem : ∀ (m : ℕ) (z : S), z ∈ (L ^ m • ⊤ : Submodule S S) ↔ z ∈ L ^ m := by
    intro m z
    rw [Ideal.smul_top_eq_map (L ^ m), Submodule.restrictScalars_mem, Algebra.algebraMap_self,
      Ideal.map_id]
  refine (IsHausdorff.eq_iff_smodEq (I := L)).mpr fun m => ?_
  rw [SModEq.sub_mem]
  exact (hmem m _).mpr (Ideal.Quotient.eq.mp (h m))

end AdicCompletion

/-- An `R`-algebra homomorphism maps the powers of the extended ideal `I·B` into the powers of
any ideal containing `I·S`: the standard source of the continuity hypothesis of
`AdicCompletion.extendRingHom`. -/
theorem Ideal.map_algebraMap_pow_le_comap {R B S : Type u} [CommRing R] [CommRing B]
    [CommRing S] [Algebra R B] [Algebra R S] (I : Ideal R) (L : Ideal S)
    (hIL : I.map (algebraMap R S) ≤ L) (ψ : B →ₐ[R] S) (m : ℕ) :
    (I.map (algebraMap R B)) ^ m ≤ (L ^ m).comap ψ.toRingHom := by
  rw [← Ideal.map_le_iff_le_comap, ← Ideal.map_pow, Ideal.map_map]
  have hcomp : (ψ.toRingHom.comp (algebraMap R B)) = algebraMap R S := ψ.comp_algebraMap
  rw [hcomp, Ideal.map_pow]
  exact Ideal.pow_right_mono hIL m
