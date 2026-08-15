import FormalSchemes.TateTransition

set_option linter.style.header false

/-!
# The 𝔾m-inversion overlap transition of the Tate curve

Fix an adic ring `R` with ideal of definition `I` and a Tate parameter `q ∈ R`, and let
`A = R{x, y} / (x·y − q)` be the coordinate ring of the formal Tate annulus. The two completed
overlap charts `A[x⁻¹]^∧` (`annulusOverlap`) and `A[y⁻¹]^∧` (`annulusOverlapY`) are copies of the
formal multiplicative group `Ĝm = R{X, X⁻¹}` (`RestrictedLaurentSeries`) via the crux
identification `overlapEquiv : A[x⁻¹]^∧ ≃+* R{X, X⁻¹}`, sending `x ↦ X`.

The flip transition `annulusOverlapTransition` (`FormalSchemes.TateTransition`) realises the
coordinate *swap* `x ↦ y`, i.e. the identity on the 𝔾m coordinate `X ↦ Y`. This file constructs the
geometrically-correct Tate 2-gon gluing, the **inversion** transition realising `X ↦ Y⁻¹`
(equivalently `x ↦ y⁻¹`), as the composite of the honest 𝔾m-inversion `x ↦ x⁻¹` with the flip.

The single new gadget is the 𝔾m-inversion automorphism `rlsInv : R{X,X⁻¹} ≃+* R{X,X⁻¹}` with
`rlsInv (X n) = X (-n)`, built from the antipode-style evaluation at the unit `X⁻¹`; everything else
is transported through `overlapEquiv` and composed with the merged flip machinery.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open Ideal AlgebraicGeometry LaurentPolynomial

universe u

namespace RestrictedLaurentSeries

variable (R : Type u) [CommRing R] (I : Ideal R)

/-- The variable `X n` of `R{X, X⁻¹}` is the image of the Laurent monomial `T n` under the
canonical algebra map (the `AlgHom` form of the inclusion). -/
theorem X_eq_ofAlgHom (n : ℤ) : X R I n = ofAlgHom R I (T n) :=
  (ofAlgHom_apply R I (T n)).symm

/-- The degree-zero variable is the unit of `R{X, X⁻¹}`. -/
theorem X_zero : X R I 0 = 1 := by
  rw [X_eq_ofAlgHom, T_zero, map_one]

/-- The variables of `R{X, X⁻¹}` multiply additively in the exponent: `X m · X n = X (m + n)`. -/
theorem X_add (m n : ℤ) : X R I m * X R I n = X R I (m + n) := by
  simp only [X_eq_ofAlgHom]
  rw [← map_mul, ← T_add]

/-- The value of the inverse of the unit `X 1` is the variable `X (-1)`. -/
theorem coe_isUnit_X_inv :
    (↑((isUnit_X R I 1).unit⁻¹) : RestrictedLaurentSeries R I) = X R I (-1) := by
  set u := (isUnit_X R I 1).unit with hu
  have hval : (↑u : RestrictedLaurentSeries R I) = X R I 1 := (isUnit_X R I 1).unit_spec
  have hu1 : (↑u : RestrictedLaurentSeries R I) * X R I (-1) = 1 := by
    rw [hval, X_add, show (1 : ℤ) + -1 = 0 from by ring, X_zero]
  calc (↑u⁻¹ : RestrictedLaurentSeries R I)
      = ↑u⁻¹ * (↑u * X R I (-1)) := by rw [hu1, mul_one]
    _ = (↑u⁻¹ * ↑u) * X R I (-1) := by rw [mul_assoc]
    _ = X R I (-1) := by rw [Units.inv_mul, one_mul]

/-- The value of the `n`-th power of the unit `X 1` is the variable `X n`. -/
theorem coe_isUnit_X_zpow (n : ℤ) :
    (↑((isUnit_X R I 1).unit ^ n) : RestrictedLaurentSeries R I) = X R I n := by
  induction n using Int.induction_on with
  | zero => rw [zpow_zero, Units.val_one, X_zero]
  | succ k ih => rw [zpow_add_one, Units.val_mul, ih, IsUnit.unit_spec, X_add]
  | pred k ih =>
      rw [zpow_sub_one, Units.val_mul, ih, coe_isUnit_X_inv, X_add, sub_eq_add_neg]

variable (hI : I.FG)

/-- **The 𝔾m-inversion endomorphism** of `R{X, X⁻¹}`, `X ↦ X⁻¹`, bundled as an `R`-algebra
homomorphism: evaluation at the unit `(X 1)⁻¹`. This is the antipode of the formal multiplicative
group, packaged as an `AlgHom`. -/
def rlsInvAlg : RestrictedLaurentSeries R I →ₐ[R] RestrictedLaurentSeries R I :=
  haveI : IsAdicComplete (idealOfDefinition R I) (RestrictedLaurentSeries R I) :=
    (isAdicRing R I hI).toIsAdicComplete
  unitEvalAlgHom R I (idealOfDefinition R I)
    (le_of_eq (idealOfDefinition_eq_map R I).symm) (isUnit_X R I 1).unit⁻¹

/-- The 𝔾m-inversion endomorphism inverts the exponent of every variable: `X n ↦ X (-n)`. -/
theorem rlsInvAlg_X (n : ℤ) : rlsInvAlg R I hI (X R I n) = X R I (-n) := by
  haveI : IsAdicComplete (idealOfDefinition R I) (RestrictedLaurentSeries R I) :=
    (isAdicRing R I hI).toIsAdicComplete
  have h := unitEvalAlgHom_X R I (idealOfDefinition R I)
    (le_of_eq (idealOfDefinition_eq_map R I).symm) (isUnit_X R I 1).unit⁻¹ n
  rw [inv_zpow, ← zpow_neg, coe_isUnit_X_zpow] at h
  exact h

/-- The 𝔾m-inversion endomorphism is an involution: applying it twice is the identity. -/
theorem rlsInvAlg_comp_rlsInvAlg :
    (rlsInvAlg R I hI).comp (rlsInvAlg R I hI) = AlgHom.id R (RestrictedLaurentSeries R I) := by
  haveI : IsAdicComplete (idealOfDefinition R I) (RestrictedLaurentSeries R I) :=
    (isAdicRing R I hI).toIsAdicComplete
  refine point_ext R I (idealOfDefinition R I) hI ?_ ?_ ?_
  · intro m x hx
    rw [AlgHom.comp_apply]
    have h1 : rlsInvAlg R I hI x ∈ (idealOfDefinition R I) ^ m :=
      isContinuousPoint_unitEvalAlgHom R I (idealOfDefinition R I)
        (le_of_eq (idealOfDefinition_eq_map R I).symm) hI (isUnit_X R I 1).unit⁻¹ m x hx
    exact isContinuousPoint_unitEvalAlgHom R I (idealOfDefinition R I)
      (le_of_eq (idealOfDefinition_eq_map R I).symm) hI (isUnit_X R I 1).unit⁻¹ m _
      ((mem_idealOfDefinition_pow_iff R I m _).mp h1)
  · intro m x hx
    exact (mem_idealOfDefinition_pow_iff R I m x).mpr hx
  · rw [AlgHom.comp_apply, rlsInvAlg_X, rlsInvAlg_X, AlgHom.id_apply, neg_neg]

/-- The 𝔾m-inversion automorphism, as an `R`-algebra equivalence. -/
def rlsInvAlgEquiv : RestrictedLaurentSeries R I ≃ₐ[R] RestrictedLaurentSeries R I :=
  AlgEquiv.ofAlgHom (rlsInvAlg R I hI) (rlsInvAlg R I hI)
    (rlsInvAlg_comp_rlsInvAlg R I hI) (rlsInvAlg_comp_rlsInvAlg R I hI)

/-- **The 𝔾m-inversion automorphism** `rlsInv : R{X, X⁻¹} ≃+* R{X, X⁻¹}`, `X ↦ X⁻¹`, an involution
inverting the exponent of every variable (`rlsInv (X n) = X (-n)`). It fixes the degree-zero part
`R`, so it commutes with the structural map. -/
def rlsInv : RestrictedLaurentSeries R I ≃+* RestrictedLaurentSeries R I :=
  (rlsInvAlgEquiv R I hI).toRingEquiv

@[simp] theorem rlsInv_apply (x : RestrictedLaurentSeries R I) :
    rlsInv R I hI x = rlsInvAlg R I hI x := rfl

/-- **The acceptance identity for 𝔾m-inversion**: `rlsInv (X n) = X (-n)`. -/
theorem rlsInv_X (n : ℤ) : rlsInv R I hI (X R I n) = X R I (-n) := by
  rw [rlsInv_apply, rlsInvAlg_X]

theorem rlsInv_X_one : rlsInv R I hI (X R I 1) = X R I (-1) := by
  rw [rlsInv_X]

theorem rlsInv_X_neg_one : rlsInv R I hI (X R I (-1)) = X R I 1 := by
  rw [rlsInv_X, neg_neg]

/-- `rlsInv` is an involution (function form). -/
theorem rlsInv_rlsInv (x : RestrictedLaurentSeries R I) :
    rlsInv R I hI (rlsInv R I hI x) = x := by
  rw [rlsInv_apply, rlsInv_apply]
  exact AlgHom.congr_fun (rlsInvAlg_comp_rlsInvAlg R I hI) x

theorem rlsInv_symm_apply (y : RestrictedLaurentSeries R I) :
    (rlsInv R I hI).symm y = rlsInv R I hI y := by
  rw [RingEquiv.symm_apply_eq]
  exact (rlsInv_rlsInv R I hI y).symm

/-- `rlsInv` fixes the image of `R`: it commutes with the structural map. -/
theorem rlsInv_algebraMap (r : R) :
    rlsInv R I hI (algebraMap R (RestrictedLaurentSeries R I) r) =
      algebraMap R (RestrictedLaurentSeries R I) r := by
  rw [rlsInv_apply]
  exact (rlsInvAlg R I hI).commutes r

end RestrictedLaurentSeries

open RestrictedLaurentSeries

section Transport

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R) (hI : I.FG)

/-- **The x-side 𝔾m-inversion** `A[x⁻¹]^∧ ≃+* A[x⁻¹]^∧`, `x ↦ x⁻¹`: the 𝔾m-inversion `rlsInv`
transported through the crux identification `overlapEquiv : A[x⁻¹]^∧ ≃+* R{X, X⁻¹}`. -/
def annulusOverlapInvX : annulusOverlap R I q ≃+* annulusOverlap R I q :=
  (overlapEquiv R I q hI).trans ((rlsInv R I hI).trans (overlapEquiv R I q hI).symm)

theorem annulusOverlapInvX_apply (x : annulusOverlap R I q) :
    annulusOverlapInvX R I q hI x =
      (overlapEquiv R I q hI).symm (rlsInv R I hI (overlapEquiv R I q hI x)) := rfl

/-- Reading the x-side inversion through `overlapEquiv` is exactly `rlsInv` in 𝔾m coordinates. -/
theorem overlapEquiv_annulusOverlapInvX (x : annulusOverlap R I q) :
    overlapEquiv R I q hI (annulusOverlapInvX R I q hI x) =
      rlsInv R I hI (overlapEquiv R I q hI x) := by
  rw [annulusOverlapInvX_apply, RingEquiv.apply_symm_apply]

/-- Reading the inverse of the x-side inversion through `overlapEquiv` is also `rlsInv` (it is an
involution). -/
theorem overlapEquiv_annulusOverlapInvX_symm (z : annulusOverlap R I q) :
    overlapEquiv R I q hI ((annulusOverlapInvX R I q hI).symm z) =
      rlsInv R I hI (overlapEquiv R I q hI z) := by
  have h := overlapEquiv_annulusOverlapInvX R I q hI ((annulusOverlapInvX R I q hI).symm z)
  rw [RingEquiv.apply_symm_apply] at h
  rw [h, rlsInv_rlsInv]

/-- **Decisive x-side witness**: the x-side inversion sends the coordinate `x` to the element that
reads as `X (-1)` in 𝔾m coordinates (contrast the flip, which fixes the coordinate as `X 1`). -/
theorem overlapEquiv_annulusOverlapInvX_overlapX :
    overlapEquiv R I q hI (annulusOverlapInvX R I q hI
        (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q) (overlapX R I q))) =
      X R I (-1) := by
  rw [overlapEquiv_annulusOverlapInvX, overlapEquiv_overlapX, rlsInv_X_one]

/-- The x-side inversion fixes the image of `R`: it commutes with the structural map. -/
theorem annulusOverlapInvX_algebraMap (r : R) :
    annulusOverlapInvX R I q hI (algebraMap R (annulusOverlap R I q) r) =
      algebraMap R (annulusOverlap R I q) r := by
  have h1 : overlapEquiv R I q hI (algebraMap R (annulusOverlap R I q) r) =
      algebraMap R (RestrictedLaurentSeries R I) r := by
    rw [overlapEquiv_apply]
    exact (overlapHomAlg R I q hI).commutes r
  rw [annulusOverlapInvX_apply, h1, rlsInv_algebraMap, overlapEquiv_symm_apply]
  exact overlapInv_algebraMap R I q hI r

/-- The flip transition carries the coordinate `x` to the coordinate `y`: it sends the class of
`x` in `A[x⁻¹]^∧` to the class of `y` in `A[y⁻¹]^∧`. -/
theorem annulusOverlapTransition_overlapX :
    annulusOverlapTransition R I q hI
        (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q) (overlapX R I q)) =
      algebraMap (annulusAlgebra R I q) (annulusOverlapY R I q) (overlapY R I q) := by
  rw [annulusOverlapTransition_apply,
    IsScalarTower.algebraMap_apply (annulusAlgebra R I q) (annulusLoc R I q) (annulusOverlap R I q),
    annulusOverlapTransitionHom_algebraMap, annulusLocTransition_algebraMap,
    annulusFlip_overlapX,
    ← IsScalarTower.algebraMap_apply (annulusAlgebra R I q) (annulusLocY R I q)
      (annulusOverlapY R I q)]

/-- The flip transition is `R`-linear on the structural map. -/
theorem annulusOverlapTransition_algebraMap_R (r : R) :
    annulusOverlapTransition R I q hI (algebraMap R (annulusOverlap R I q) r) =
      algebraMap R (annulusOverlapY R I q) r := by
  rw [annulusOverlapTransition_apply,
    IsScalarTower.algebraMap_apply R (annulusLoc R I q) (annulusOverlap R I q),
    annulusOverlapTransitionHom_algebraMap, annulusLocTransition_algebraMap_R,
    ← IsScalarTower.algebraMap_apply R (annulusLocY R I q) (annulusOverlapY R I q)]

/-- **The 𝔾m-inversion overlap transition** `A[x⁻¹]^∧ ≃+* A[y⁻¹]^∧` of the Tate curve: the honest
x-side 𝔾m-inversion `x ↦ x⁻¹` followed by the flip `x ↦ y`. Its coordinate action is `x ↦ y⁻¹`,
i.e. `X ↦ Y⁻¹` — the geometrically-correct Tate 2-gon gluing, contrasting the flip transition
`annulusOverlapTransition` (which realises `X ↦ Y`). -/
def annulusOverlapInversion : annulusOverlap R I q ≃+* annulusOverlapY R I q :=
  (annulusOverlapInvX R I q hI).trans (annulusOverlapTransition R I q hI)

theorem annulusOverlapInversion_apply (x : annulusOverlap R I q) :
    annulusOverlapInversion R I q hI x =
      annulusOverlapTransition R I q hI (annulusOverlapInvX R I q hI x) := rfl

theorem annulusOverlapInversion_symm_apply (y : annulusOverlapY R I q) :
    (annulusOverlapInversion R I q hI).symm y =
      (annulusOverlapInvX R I q hI).symm ((annulusOverlapTransition R I q hI).symm y) := rfl

/-- **The decisive witness that the transition is genuinely inversion, not the flip.**
Transporting chart-1's `y`-coordinate back through `annulusOverlapInversion` and reading via the
crux identification `overlapEquiv` yields `X (-1)` — *not* `X 1`. Since the flip transition would
give `X 1`, this pins down that `annulusOverlapInversion` realises `X ↦ Y⁻¹`. -/
theorem overlapEquiv_annulusOverlapInversion_symm_overlapY :
    overlapEquiv R I q hI ((annulusOverlapInversion R I q hI).symm
        (algebraMap (annulusAlgebra R I q) (annulusOverlapY R I q) (overlapY R I q))) =
      X R I (-1) := by
  have hxy : (annulusOverlapTransition R I q hI).symm
      (algebraMap (annulusAlgebra R I q) (annulusOverlapY R I q) (overlapY R I q)) =
        algebraMap (annulusAlgebra R I q) (annulusOverlap R I q) (overlapX R I q) := by
    rw [RingEquiv.symm_apply_eq]
    exact (annulusOverlapTransition_overlapX R I q hI).symm
  rw [annulusOverlapInversion_symm_apply, hxy, overlapEquiv_annulusOverlapInvX_symm,
    overlapEquiv_overlapX, rlsInv_X_one]

/-- **`R`-linearity of the inversion transition**: it commutes with the structural maps to `Spf R`,
so it is a morphism over the base. -/
theorem annulusOverlapInversion_algebraMap (r : R) :
    annulusOverlapInversion R I q hI (algebraMap R (annulusOverlap R I q) r) =
      algebraMap R (annulusOverlapY R I q) r := by
  rw [annulusOverlapInversion_apply, annulusOverlapInvX_algebraMap,
    annulusOverlapTransition_algebraMap_R]

end Transport

end
