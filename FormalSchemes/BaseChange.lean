import FormalSchemes.CompletedTensor
import FormalSchemes.CompletedTensorAssoc
import FormalSchemes.Completion
import Mathlib.Algebra.MvPolynomial.Basic

set_option linter.style.header false

/-!
# Base change of restricted power series

This file develops the uniqueness half of the universal property of the formal polydisc and,
building on it, the **finite base-change isomorphism** for restricted power series.

The existence half of the universal property is `RestrictedPowerSeries.evalHom` (see
`FormalSchemes/RestrictedPowerSeries.lean`): for a complete adic `R`-algebra `S` and an
`n`-tuple `s`, evaluation of polynomials at `s` extends to `R{X₁, …, Xₙ} →+* S`. Here we prove
the matching uniqueness statement `RestrictedPowerSeries.hom_ext`: two continuous ring
homomorphisms out of `R{X₁, …, Xₙ}` agreeing on the constants and on the coordinates are equal.
This is the direct analogue of `CompletedTensorProduct.hom_ext`, and like it is deduced from the
continuous-extension machinery `AdicCompletion.hom_ext_of_continuous` together with the
polynomial extensionality lemma `MvPolynomial.ringHom_ext`.

## Main results

* `RestrictedPowerSeries.mem_idealOfDefinition_pow_iff`: membership in the powers of the ideal of
  definition, expressed through the module filtration `(I·R[X]) ^ m • ⊤`.
* `RestrictedPowerSeries.of_C_eq_algebraMap`: the completion of a constant polynomial is the
  image of the corresponding scalar.
* `RestrictedPowerSeries.hom_ext`: the uniqueness half of the universal property of the formal
  polydisc.
* `RestrictedPowerSeries.evalHom_mem_pow`: continuity of the evaluation homomorphism `evalHom`.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. 0, §10.7.
-/

noncomputable section

open Ideal

universe u

namespace RestrictedPowerSeries

variable (R : Type u) [CommRing R] (I : Ideal R) (n : ℕ)

/-- Membership in the powers of the ideal of definition of `R{X₁, …, Xₙ}`, expressed through
the module filtration `(I·R[X]) ^ m • ⊤` used by the completion API. -/
theorem mem_idealOfDefinition_pow_iff (m : ℕ) (x : RestrictedPowerSeries R I n) :
    x ∈ (idealOfDefinition R I n) ^ m ↔
      x ∈ ((I.map (algebraMap R (MvPolynomial (Fin n) R))) ^ m • ⊤ :
        Submodule (MvPolynomial (Fin n) R) (RestrictedPowerSeries R I n)) := by
  rw [← Ideal.mem_map_pow_iff_mem_smul_top (I.map (algebraMap R (MvPolynomial (Fin n) R))) m x,
    idealOfDefinition, Ideal.smul_top_eq_map, Submodule.restrictScalars_mem,
    Algebra.algebraMap_self, Ideal.map_id]

/-- The completion map `R[X] → R{X₁, …, Xₙ}` on a polynomial is the algebra structure map. -/
theorem algebraMap_MvPolynomial_apply (p : MvPolynomial (Fin n) R) :
    algebraMap (MvPolynomial (Fin n) R) (RestrictedPowerSeries R I n) p =
      AdicCompletion.of (I.map (algebraMap R (MvPolynomial (Fin n) R)))
        (MvPolynomial (Fin n) R) p := by
  rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]

/-- The completion of a constant polynomial `C r` is the image of `r` under the structure map
`R → R{X₁, …, Xₙ}`. -/
theorem of_C_eq_algebraMap (r : R) :
    AdicCompletion.of (I.map (algebraMap R (MvPolynomial (Fin n) R)))
        (MvPolynomial (Fin n) R) (MvPolynomial.C r) =
      algebraMap R (RestrictedPowerSeries R I n) r := by
  rw [AdicCompletion.algebraMap_apply, MvPolynomial.algebraMap_eq]

section HomExt

variable {R I n}
variable {S : Type u} [CommRing S] (L : Ideal S) [IsAdicComplete L S]

/-- **The universal property of the formal polydisc, uniqueness direction**: two continuous
ring homomorphisms out of `R{X₁, …, Xₙ}` into a complete adic ring — mapping the powers of the
ideal of definition into the powers of `L` — that agree on the constants (the image of `R`) and
on the coordinates `X i` are equal (for `I` finitely generated). This is the companion of the
existence statement `RestrictedPowerSeries.evalHom`. -/
theorem hom_ext (hI : I.FG) {F G : RestrictedPowerSeries R I n →+* S}
    (hF : ∀ (m : ℕ) (x : RestrictedPowerSeries R I n),
      x ∈ (idealOfDefinition R I n) ^ m → F x ∈ L ^ m)
    (hG : ∀ (m : ℕ) (x : RestrictedPowerSeries R I n),
      x ∈ (idealOfDefinition R I n) ^ m → G x ∈ L ^ m)
    (hbase : ∀ r : R, F (algebraMap R (RestrictedPowerSeries R I n) r) =
      G (algebraMap R (RestrictedPowerSeries R I n) r))
    (hgen : ∀ i : Fin n,
      F (AdicCompletion.of (I.map (algebraMap R (MvPolynomial (Fin n) R)))
          (MvPolynomial (Fin n) R) (MvPolynomial.X i)) =
        G (AdicCompletion.of (I.map (algebraMap R (MvPolynomial (Fin n) R)))
          (MvPolynomial (Fin n) R) (MvPolynomial.X i))) :
    F = G := by
  refine AdicCompletion.hom_ext_of_continuous _ L (hI.map _)
    (fun m x hx => hF m x ((mem_idealOfDefinition_pow_iff R I n m x).mpr hx))
    (fun m x hx => hG m x ((mem_idealOfDefinition_pow_iff R I n m x).mpr hx)) ?_
  intro x
  have key : F.comp (algebraMap (MvPolynomial (Fin n) R) (RestrictedPowerSeries R I n)) =
      G.comp (algebraMap (MvPolynomial (Fin n) R) (RestrictedPowerSeries R I n)) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp only [RingHom.coe_comp, Function.comp_apply]
      rw [algebraMap_MvPolynomial_apply, of_C_eq_algebraMap]
      exact hbase r
    · simp only [RingHom.coe_comp, Function.comp_apply]
      rw [algebraMap_MvPolynomial_apply]
      exact hgen i
  have hx2 := DFunLike.congr_fun key x
  simp only [RingHom.coe_comp, Function.comp_apply] at hx2
  rwa [algebraMap_MvPolynomial_apply] at hx2

end HomExt

/-!
### Continuity of the evaluation homomorphism
-/

section Eval

variable {R I n}
variable {S : Type u} [CommRing S] (L : Ideal S) [Algebra R S] [IsAdicComplete L S]
variable (hIL : I.map (algebraMap R S) ≤ L) (s : Fin n → S)

/-- The evaluation homomorphism `evalHom` is the continuous extension of `aeval s`. -/
theorem evalHom_eq_extendRingHom :
    evalHom R I n L hIL s =
      AdicCompletion.extendRingHom (I.map (algebraMap R (MvPolynomial (Fin n) R))) L
        (MvPolynomial.aeval s).toRingHom (aeval_pow_le R I n L hIL s) :=
  rfl

/-- **Continuity of the evaluation homomorphism**: `evalHom` carries the powers of the ideal of
definition into the powers of `L` (for `I` finitely generated). -/
theorem evalHom_mem_pow (hI : I.FG) (m : ℕ) {x : RestrictedPowerSeries R I n}
    (hx : x ∈ (idealOfDefinition R I n) ^ m) :
    evalHom R I n L hIL s x ∈ L ^ m := by
  rw [evalHom_eq_extendRingHom]
  exact AdicCompletion.extendRingHom_continuous _ L _ _ (hI.map _) m x
    ((mem_idealOfDefinition_pow_iff R I n m x).mp hx)

/-- On the image of `R` (the constants), `evalHom` is the structure map `algebraMap R S`. -/
theorem evalHom_algebraMap (r : R) :
    evalHom R I n L hIL s (algebraMap R (RestrictedPowerSeries R I n) r) = algebraMap R S r := by
  rw [← of_C_eq_algebraMap, evalHom_of, MvPolynomial.aeval_C]

/-- **Evaluation as an `R`-algebra homomorphism** `R{X₁, …, Xₙ} →ₐ[R] S`. -/
def evalAlgHom : RestrictedPowerSeries R I n →ₐ[R] S :=
  { evalHom R I n L hIL s with commutes' := evalHom_algebraMap L hIL s }

end Eval

end RestrictedPowerSeries

/-!
### The finite base-change isomorphism

For a commutative `R`-algebra `S` and `I` finitely generated, the completed tensor product of `S`
with the formal polydisc over `R` is the formal polydisc over `S`:
`S ⊗̂_R R{X₁, …, Xₙ} ≃+* S{X₁, …, Xₙ}`. This is the completed-tensor counterpart of the polynomial
base change `S ⊗[R] R[X] ≃ S[X]`, and is the crux of the finite-base-change property of formal
schemes topologically of finite type.

Throughout, write `SX := S{X₁, …, Xₙ} = RestrictedPowerSeries S (I·S) n` and
`T := S ⊗̂_R R{X₁, …, Xₙ} = CompletedTensorProduct R I S (R{X₁, …, Xₙ})`. The forward map is built
from the universal property of the completed tensor product (`CompletedTensorProduct.lift`) with
the structure map `S → SX` and the coefficient map `R{X} → SX`; the inverse is the evaluation map
of `SX` (`RestrictedPowerSeries.evalHom` over the base `S`) sending each coordinate to the
corresponding generator of `T`.
-/

namespace RestrictedPowerSeries

section BaseChange

variable {R : Type u} [CommRing R] {I : Ideal R} {n : ℕ}
variable {S : Type u} [CommRing S] [Algebra R S]

/-- The ideal of definition of `S{X}` is the extension of `I` along `R → S{X}`. -/
theorem baseChange_idealOfDefinition_eq :
    idealOfDefinition S (I.map (algebraMap R S)) n =
      I.map (algebraMap R (RestrictedPowerSeries S (I.map (algebraMap R S)) n)) := by
  rw [idealOfDefinition_eq_map, IsScalarTower.algebraMap_eq R S
    (RestrictedPowerSeries S (I.map (algebraMap R S)) n), ← Ideal.map_map]

/-- The structure map `S → T` of `T = S ⊗̂_R R{X}` as an `S`-algebra is the canonical map `inl`. -/
theorem algebraMap_baseChangeSource_eq :
    algebraMap S (CompletedTensorProduct R I S (RestrictedPowerSeries R I n)) =
      (CompletedTensorProduct.inl R I S (RestrictedPowerSeries R I n)).toRingHom :=
  rfl

/-- The extension of `I·S` along `S → T` is the ideal of definition of `T`. -/
theorem baseChange_map_algebraMap_eq :
    (I.map (algebraMap R S)).map
        (algebraMap S (CompletedTensorProduct R I S (RestrictedPowerSeries R I n))) =
      CompletedTensorProduct.idealOfDefinition R I S (RestrictedPowerSeries R I n) := by
  have h : (algebraMap S (CompletedTensorProduct R I S (RestrictedPowerSeries R I n))).comp
      (algebraMap R S) =
      algebraMap R (CompletedTensorProduct R I S (RestrictedPowerSeries R I n)) :=
    (IsScalarTower.algebraMap_eq R S _).symm
  rw [Ideal.map_map, h, CompletedTensorProduct.idealOfDefinition_eq_map]

/-! #### The coefficient map `R{X} → S{X}` -/

/-- The **coefficient / base-change map** `R{X₁, …, Xₙ} →ₐ[R] S{X₁, …, Xₙ}`: the completion of the
polynomial coefficient extension `R[X] → S[X]`, sending each coordinate `Xᵢ` to `Xᵢ` and each
constant `r` to `algebraMap R S r`. Built as the evaluation of `R{X}` at the coordinates of
`S{X}`. -/
def baseChangeCoeff (hI : I.FG) :
    RestrictedPowerSeries R I n →ₐ[R] RestrictedPowerSeries S (I.map (algebraMap R S)) n :=
  haveI : IsAdicComplete (idealOfDefinition S (I.map (algebraMap R S)) n)
      (RestrictedPowerSeries S (I.map (algebraMap R S)) n) :=
    (isAdicRing S (I.map (algebraMap R S)) n (hI.map _)).toIsAdicComplete
  evalAlgHom (idealOfDefinition S (I.map (algebraMap R S)) n)
    (le_of_eq baseChange_idealOfDefinition_eq.symm)
    (fun i => AdicCompletion.of _ _ (MvPolynomial.X i))

theorem baseChangeCoeff_apply (hI : I.FG) (x : RestrictedPowerSeries R I n) :
    baseChangeCoeff hI x =
      haveI : IsAdicComplete (idealOfDefinition S (I.map (algebraMap R S)) n)
          (RestrictedPowerSeries S (I.map (algebraMap R S)) n) :=
        (isAdicRing S (I.map (algebraMap R S)) n (hI.map _)).toIsAdicComplete
      evalHom R I n (idealOfDefinition S (I.map (algebraMap R S)) n)
        (le_of_eq baseChange_idealOfDefinition_eq.symm)
        (fun i => AdicCompletion.of _ _ (MvPolynomial.X i)) x :=
  rfl

@[simp]
theorem baseChangeCoeff_of_X (hI : I.FG) (i : Fin n) :
    baseChangeCoeff hI (AdicCompletion.of _ _ (MvPolynomial.X i)) =
      (AdicCompletion.of _ _ (MvPolynomial.X i) :
        RestrictedPowerSeries S (I.map (algebraMap R S)) n) := by
  rw [baseChangeCoeff_apply, evalHom_of, MvPolynomial.aeval_X]

/-! #### The two structural maps -/

/-- The **forward base-change map** `T = S ⊗̂_R R{X} →+* S{X}`, given by the universal property of
the completed tensor product with the structure map `S → S{X}` and the coefficient map
`R{X} → S{X}`. -/
def baseChangeHom (hI : I.FG) :
    CompletedTensorProduct R I S (RestrictedPowerSeries R I n) →+*
      RestrictedPowerSeries S (I.map (algebraMap R S)) n :=
  haveI : IsAdicComplete (idealOfDefinition S (I.map (algebraMap R S)) n)
      (RestrictedPowerSeries S (I.map (algebraMap R S)) n) :=
    (isAdicRing S (I.map (algebraMap R S)) n (hI.map _)).toIsAdicComplete
  CompletedTensorProduct.lift (idealOfDefinition S (I.map (algebraMap R S)) n)
    (le_of_eq baseChange_idealOfDefinition_eq.symm)
    (IsScalarTower.toAlgHom R S (RestrictedPowerSeries S (I.map (algebraMap R S)) n))
    (baseChangeCoeff hI)

/-- The **inverse base-change map** `S{X} →+* T = S ⊗̂_R R{X}`, given by evaluation of `S{X}` at the
coordinates `inr (Xᵢ)` of `T` (using the `S`-algebra structure of `T` via `inl`). -/
def baseChangeInvHom (hI : I.FG) :
    RestrictedPowerSeries S (I.map (algebraMap R S)) n →+*
      CompletedTensorProduct R I S (RestrictedPowerSeries R I n) :=
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I S (RestrictedPowerSeries R I n))
      (CompletedTensorProduct R I S (RestrictedPowerSeries R I n)) :=
    (CompletedTensorProduct.isAdicRing R I S (RestrictedPowerSeries R I n) hI).toIsAdicComplete
  evalHom S (I.map (algebraMap R S)) n
    (CompletedTensorProduct.idealOfDefinition R I S (RestrictedPowerSeries R I n))
    (le_of_eq baseChange_map_algebraMap_eq)
    (fun i => CompletedTensorProduct.inr R I S (RestrictedPowerSeries R I n)
      (AdicCompletion.of _ _ (MvPolynomial.X i)))

theorem baseChangeInvHom_apply (hI : I.FG)
    (x : RestrictedPowerSeries S (I.map (algebraMap R S)) n) :
    baseChangeInvHom hI x =
      haveI : IsAdicComplete
          (CompletedTensorProduct.idealOfDefinition R I S (RestrictedPowerSeries R I n))
          (CompletedTensorProduct R I S (RestrictedPowerSeries R I n)) :=
        (CompletedTensorProduct.isAdicRing R I S (RestrictedPowerSeries R I n) hI).toIsAdicComplete
      evalHom S (I.map (algebraMap R S)) n
        (CompletedTensorProduct.idealOfDefinition R I S (RestrictedPowerSeries R I n))
        (le_of_eq baseChange_map_algebraMap_eq)
        (fun i => CompletedTensorProduct.inr R I S (RestrictedPowerSeries R I n)
          (AdicCompletion.of _ _ (MvPolynomial.X i))) x :=
  rfl

/-! #### Continuity of the two maps -/

/-- Continuity of `baseChangeHom`: it carries the powers of the ideal of definition into the
powers of the ideal of definition of the target. -/
theorem baseChangeHom_mem_pow (hI : I.FG) (m : ℕ)
    {x : CompletedTensorProduct R I S (RestrictedPowerSeries R I n)}
    (hx : x ∈
      (CompletedTensorProduct.idealOfDefinition R I S (RestrictedPowerSeries R I n)) ^ m) :
    baseChangeHom hI x ∈ (idealOfDefinition S (I.map (algebraMap R S)) n) ^ m := by
  haveI : IsAdicComplete (idealOfDefinition S (I.map (algebraMap R S)) n)
      (RestrictedPowerSeries S (I.map (algebraMap R S)) n) :=
    (isAdicRing S (I.map (algebraMap R S)) n (hI.map _)).toIsAdicComplete
  unfold baseChangeHom
  exact CompletedTensorProduct.lift_mem_pow _ _ _ _ hI m hx

/-- Continuity of `baseChangeInvHom`. -/
theorem baseChangeInvHom_mem_pow (hI : I.FG) (m : ℕ)
    {x : RestrictedPowerSeries S (I.map (algebraMap R S)) n}
    (hx : x ∈ (idealOfDefinition S (I.map (algebraMap R S)) n) ^ m) :
    baseChangeInvHom hI x ∈
      (CompletedTensorProduct.idealOfDefinition R I S (RestrictedPowerSeries R I n)) ^ m := by
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I S (RestrictedPowerSeries R I n))
      (CompletedTensorProduct R I S (RestrictedPowerSeries R I n)) :=
    (CompletedTensorProduct.isAdicRing R I S (RestrictedPowerSeries R I n) hI).toIsAdicComplete
  rw [baseChangeInvHom_apply]
  exact evalHom_mem_pow
    (CompletedTensorProduct.idealOfDefinition R I S (RestrictedPowerSeries R I n))
    (le_of_eq baseChange_map_algebraMap_eq)
    (fun i => CompletedTensorProduct.inr R I S (RestrictedPowerSeries R I n)
      (AdicCompletion.of _ _ (MvPolynomial.X i))) (hI.map (algebraMap R S)) m hx

/-! #### Action on generators -/

@[simp]
theorem baseChangeHom_inl (hI : I.FG) (s : S) :
    baseChangeHom hI (CompletedTensorProduct.inl R I S (RestrictedPowerSeries R I n) s) =
      algebraMap S (RestrictedPowerSeries S (I.map (algebraMap R S)) n) s := by
  haveI : IsAdicComplete (idealOfDefinition S (I.map (algebraMap R S)) n)
      (RestrictedPowerSeries S (I.map (algebraMap R S)) n) :=
    (isAdicRing S (I.map (algebraMap R S)) n (hI.map _)).toIsAdicComplete
  unfold baseChangeHom
  rw [CompletedTensorProduct.lift_inl]
  rfl

theorem baseChangeHom_inr (hI : I.FG) (y : RestrictedPowerSeries R I n) :
    baseChangeHom hI (CompletedTensorProduct.inr R I S (RestrictedPowerSeries R I n) y) =
      baseChangeCoeff hI y := by
  haveI : IsAdicComplete (idealOfDefinition S (I.map (algebraMap R S)) n)
      (RestrictedPowerSeries S (I.map (algebraMap R S)) n) :=
    (isAdicRing S (I.map (algebraMap R S)) n (hI.map _)).toIsAdicComplete
  unfold baseChangeHom
  rw [CompletedTensorProduct.lift_inr]

@[simp]
theorem baseChangeHom_inr_of_X (hI : I.FG) (i : Fin n) :
    baseChangeHom hI (CompletedTensorProduct.inr R I S (RestrictedPowerSeries R I n)
        (AdicCompletion.of _ _ (MvPolynomial.X i))) =
      AdicCompletion.of _ _ (MvPolynomial.X i) := by
  rw [baseChangeHom_inr, baseChangeCoeff_of_X]

@[simp]
theorem baseChangeInvHom_of_X (hI : I.FG) (i : Fin n) :
    baseChangeInvHom hI (AdicCompletion.of _ _ (MvPolynomial.X i)) =
      CompletedTensorProduct.inr R I S (RestrictedPowerSeries R I n)
        (AdicCompletion.of _ _ (MvPolynomial.X i)) := by
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I S (RestrictedPowerSeries R I n))
      (CompletedTensorProduct R I S (RestrictedPowerSeries R I n)) :=
    (CompletedTensorProduct.isAdicRing R I S (RestrictedPowerSeries R I n) hI).toIsAdicComplete
  rw [baseChangeInvHom_apply, evalHom_of, MvPolynomial.aeval_X]

@[simp]
theorem baseChangeInvHom_algebraMap (hI : I.FG) (s : S) :
    baseChangeInvHom hI (algebraMap S (RestrictedPowerSeries S (I.map (algebraMap R S)) n) s) =
      CompletedTensorProduct.inl R I S (RestrictedPowerSeries R I n) s := by
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I S (RestrictedPowerSeries R I n))
      (CompletedTensorProduct R I S (RestrictedPowerSeries R I n)) :=
    (CompletedTensorProduct.isAdicRing R I S (RestrictedPowerSeries R I n) hI).toIsAdicComplete
  rw [baseChangeInvHom_apply, ← of_C_eq_algebraMap, evalHom_of, MvPolynomial.aeval_C]
  rfl

/-! #### The maps are mutually inverse -/

/-- `baseChangeInvHom` undoes `baseChangeHom` on the image of the second factor `R{X}`. Proved by
the uniqueness principle for `R{X}` (agreement on constants and coordinates). -/
theorem baseChangeInvHom_baseChangeHom_inr (hI : I.FG) (y : RestrictedPowerSeries R I n) :
    baseChangeInvHom hI (baseChangeHom hI
        (CompletedTensorProduct.inr R I S (RestrictedPowerSeries R I n) y)) =
      CompletedTensorProduct.inr R I S (RestrictedPowerSeries R I n) y := by
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I S (RestrictedPowerSeries R I n))
      (CompletedTensorProduct R I S (RestrictedPowerSeries R I n)) :=
    (CompletedTensorProduct.isAdicRing R I S (RestrictedPowerSeries R I n) hI).toIsAdicComplete
  have key :
      ((baseChangeInvHom hI).comp (baseChangeHom hI)).comp
          (CompletedTensorProduct.inr R I S (RestrictedPowerSeries R I n)).toRingHom =
        (CompletedTensorProduct.inr R I S (RestrictedPowerSeries R I n)).toRingHom := by
    refine RestrictedPowerSeries.hom_ext
      (S := CompletedTensorProduct R I S (RestrictedPowerSeries R I n))
      (L := CompletedTensorProduct.idealOfDefinition R I S (RestrictedPowerSeries R I n)) hI
      (fun m x hx => ?_) (fun m x hx => ?_) (fun r => ?_) (fun i => ?_)
    · -- continuity of the composite
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      refine baseChangeInvHom_mem_pow hI m (baseChangeHom_mem_pow hI m
        (CompletedTensorProduct.inr_mem_pow m ?_))
      rwa [← idealOfDefinition_eq_map]
    · -- continuity of inr
      simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      refine CompletedTensorProduct.inr_mem_pow m ?_
      rwa [← idealOfDefinition_eq_map]
    · -- agreement on constants
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [baseChangeHom_inr, (baseChangeCoeff hI).commutes,
        IsScalarTower.algebraMap_apply R S (RestrictedPowerSeries S (I.map (algebraMap R S)) n),
        baseChangeInvHom_algebraMap,
        (CompletedTensorProduct.inl R I S (RestrictedPowerSeries R I n)).commutes,
        (CompletedTensorProduct.inr R I S (RestrictedPowerSeries R I n)).commutes]
    · -- agreement on coordinates
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        baseChangeHom_inr_of_X, baseChangeInvHom_of_X]
  exact DFunLike.congr_fun key y

/-- `baseChangeInvHom` is a left inverse of `baseChangeHom`. -/
theorem baseChangeInvHom_comp_baseChangeHom (hI : I.FG) :
    (baseChangeInvHom hI).comp (baseChangeHom hI) =
      RingHom.id (CompletedTensorProduct R I S (RestrictedPowerSeries R I n)) := by
  haveI : IsAdicComplete
      (CompletedTensorProduct.idealOfDefinition R I S (RestrictedPowerSeries R I n))
      (CompletedTensorProduct R I S (RestrictedPowerSeries R I n)) :=
    (CompletedTensorProduct.isAdicRing R I S (RestrictedPowerSeries R I n) hI).toIsAdicComplete
  refine CompletedTensorProduct.hom_ext
    (CompletedTensorProduct.idealOfDefinition R I S (RestrictedPowerSeries R I n)) hI
    (fun m x hx => ?_) (fun m x hx => hx) (fun s => ?_) (fun y => ?_)
  · simp only [RingHom.coe_comp, Function.comp_apply]
    exact baseChangeInvHom_mem_pow hI m (baseChangeHom_mem_pow hI m hx)
  · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply, baseChangeHom_inl,
      baseChangeInvHom_algebraMap]
  · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply]
    exact baseChangeInvHom_baseChangeHom_inr hI y

/-- `baseChangeInvHom` is a right inverse of `baseChangeHom`. -/
theorem baseChangeHom_comp_baseChangeInvHom (hI : I.FG) :
    (baseChangeHom hI).comp (baseChangeInvHom hI) =
      RingHom.id (RestrictedPowerSeries S (I.map (algebraMap R S)) n) := by
  haveI : IsAdicComplete (idealOfDefinition S (I.map (algebraMap R S)) n)
      (RestrictedPowerSeries S (I.map (algebraMap R S)) n) :=
    (isAdicRing S (I.map (algebraMap R S)) n (hI.map _)).toIsAdicComplete
  refine RestrictedPowerSeries.hom_ext (idealOfDefinition S (I.map (algebraMap R S)) n)
    (hI.map (algebraMap R S))
    (fun m x hx => ?_) (fun m x hx => hx) (fun s => ?_) (fun i => ?_)
  · simp only [RingHom.coe_comp, Function.comp_apply]
    exact baseChangeHom_mem_pow hI m (baseChangeInvHom_mem_pow hI m hx)
  · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply,
      baseChangeInvHom_algebraMap, baseChangeHom_inl]
  · simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply, baseChangeInvHom_of_X,
      baseChangeHom_inr_of_X]

/-- **The finite base-change isomorphism** `S ⊗̂_R R{X₁, …, Xₙ} ≃+* S{X₁, …, Xₙ}` (for `I` finitely
generated): the completed tensor product of `S` with the formal polydisc over `R` is the formal
polydisc over `S`. -/
def baseChangeEquiv (hI : I.FG) :
    CompletedTensorProduct R I S (RestrictedPowerSeries R I n) ≃+*
      RestrictedPowerSeries S (I.map (algebraMap R S)) n :=
  RingEquiv.ofRingHom (baseChangeHom hI) (baseChangeInvHom hI)
    (baseChangeHom_comp_baseChangeInvHom hI) (baseChangeInvHom_comp_baseChangeHom hI)

@[simp]
theorem baseChangeEquiv_inl (hI : I.FG) (s : S) :
    baseChangeEquiv hI (CompletedTensorProduct.inl R I S (RestrictedPowerSeries R I n) s) =
      algebraMap S (RestrictedPowerSeries S (I.map (algebraMap R S)) n) s :=
  baseChangeHom_inl hI s

@[simp]
theorem baseChangeEquiv_inr_of_X (hI : I.FG) (i : Fin n) :
    baseChangeEquiv hI (CompletedTensorProduct.inr R I S (RestrictedPowerSeries R I n)
        (AdicCompletion.of _ _ (MvPolynomial.X i))) =
      AdicCompletion.of _ _ (MvPolynomial.X i) :=
  baseChangeHom_inr_of_X hI i

@[simp]
theorem baseChangeEquiv_symm_of_X (hI : I.FG) (i : Fin n) :
    (baseChangeEquiv hI).symm (AdicCompletion.of _ _ (MvPolynomial.X i)) =
      CompletedTensorProduct.inr R I S (RestrictedPowerSeries R I n)
        (AdicCompletion.of _ _ (MvPolynomial.X i)) :=
  baseChangeInvHom_of_X hI i

@[simp]
theorem baseChangeEquiv_symm_algebraMap (hI : I.FG) (s : S) :
    (baseChangeEquiv hI).symm
        (algebraMap S (RestrictedPowerSeries S (I.map (algebraMap R S)) n) s) =
      CompletedTensorProduct.inl R I S (RestrictedPowerSeries R I n) s :=
  baseChangeInvHom_algebraMap hI s

end BaseChange

end RestrictedPowerSeries
