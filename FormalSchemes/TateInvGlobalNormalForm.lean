import FormalSchemes.TateInvGlobalCoeff

set_option linter.style.header false

/-!
# The two `Ĝm` coordinate maps of the Tate annulus, and the constants of `Γ (T_inv/⟨σ⟩)`

`FormalSchemes.TateInvGlobalCoeff` presents `Γ (T_inv/⟨σ⟩)` as the equalizer of two ring maps
`A = R{x, y}/(x·y − q) → R{X, X⁻¹}` and reads the condition coefficientwise:

```
a ∈ Γ ↔ ∀ n, coeff n (φ a) = coeff (-n) (φ (flip⁻¹ a)),   φ := tateInvGlobalCoord.
```

That description says nothing about *which* elements satisfy it, because nothing was known about
the image of `A`. This file supplies the missing comparison and draws the consequences.

## The comparison of the two coordinate maps

`φ` sends `x ↦ X` and `y ↦ q·X⁻¹`; `φ ∘ flip⁻¹` sends `x ↦ q·X⁻¹` and `y ↦ X`. On the monomial
`xⁱyʲ` they take the values `qʲ·X^(i−j)` and `qⁱ·X^(j−i)`, whose coefficients differ by a power
of `q` determined by `i − j` alone. Since `i − j` is the degree, that is a statement with no
reference to `i` and `j`:

* `AlgebraicGeometry.tateInvGlobalCoord_coeff_flip`:
  `q ^ n.toNat * coeff n (φ a) = q ^ (-n).toNat * coeff (-n) (φ (flip⁻¹ a))`.

**No normal form for `A` is used, and none is proved.** Both sides are `R`-linear and continuous
functionals on the polydisc `R{x, y}` and they agree on the polynomials, which are dense; the
presentation `R{x, y} ↠ A` is surjective, so the identity descends to `A`. The *existence* half
of a normal form — that every element of `A` is `Σ aₙxⁿ + Σ bₙyⁿ` — is exactly that surjectivity,
and nothing here needs more of it.

## What follows for the invariants

With the membership criterion, `(1 − q ^ |n|) · coeff n (φ a) = 0` for `a ∈ Γ` and `n ≠ 0`, and
`1 − q ^ |n|` is a unit because `q` lies in the ideal of definition and `R` is complete
(`IsAdicComplete.isUnit_one_sub_pow`). Hence

* `AlgebraicGeometry.coeff_tateInvGlobalCoord_eq_zero_of_mem`: every nonzero-degree coefficient of
  an invariant element vanishes;
* `AlgebraicGeometry.tateInvGlobalCoord_eq_algebraMap_of_mem`: `φ a` is the constant
  `coeff 0 (φ a)`.

## What is *not* proved, and the exact residue

`Γ (T_inv/⟨σ⟩) ≃+* R` is **not** proved unconditionally. It is proved from one hypothesis and
nothing else:

* `AlgebraicGeometry.IsTateInvCoordSeparating`: `φ a = 0` and `φ (flip⁻¹ a) = 0` imply `a = 0`.

This is the *uniqueness* half of a normal form for `A`. From it,
`AlgebraicGeometry.tateInvGlobalSubring_eq_range` gives `Γ = (algebraMap R A).range`,
`AlgebraicGeometry.tateInvGlobalSubringEquivBase` packages the headline as a `RingEquiv`, and
`AlgebraicGeometry.tateInvPeriodQuotientGlobalSectionsEquivBase` transports it along
`AlgebraicGeometry.tateInvGlobalSectionsRingEquiv` to the global sections of the quotient
themselves.

**The hypothesis cannot be weakened to injectivity of `φ`.**
`AlgebraicGeometry.not_injective_tateInvGlobalCoord_zero` shows `φ` is not injective at `q = 0`
over any nontrivial complete base, because there `y ↦ q·X⁻¹ = 0` while `flip⁻¹ y = x ↦ X ≠ 0`;
`AlgebraicGeometry.not_injective_tateInvGlobalCoord_zero_int` instantiates that at `R = ℤ`,
`I = ⊥`, so the kernel is nonzero over an admissible base and not merely in principle. A route to
the headline through injectivity of `φ` is therefore unavailable, not just unproved.

## Placement

`RestrictedLaurentSeries.X_pow`, `RestrictedLaurentSeries.algebraMap_injective_of_isAdicComplete`,
`RestrictedPowerSeries.exists_sub_mem_idealOfDefinition_pow` and the two
`IsAdicComplete.isUnit_one_sub_*` lemmas are general and belong further up the import graph
(`FormalSchemes.FormalGm`, `FormalSchemes.BaseChange`); they are here because those files sit
under the whole tree. **Move them opportunistically.**

## References

* [Deligne–Rapoport, *Les schémas de modules de courbes elliptiques*], II.1 — the Néron `n`-gon.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open AlgebraicGeometry FormalSpectrum RestrictedLaurentSeries LaurentPolynomial

universe u

/-! ### Powers of the variable of `R{X, X⁻¹}` -/

namespace RestrictedLaurentSeries

variable (R : Type u) [CommRing R] (I : Ideal R)

/-- **The variables of `R{X, X⁻¹}` take powers additively in the exponent.** The companion of
`RestrictedLaurentSeries.X_add` (`FormalSchemes.TateOverlapInversion`); the exponent convention
`k * m` is `LaurentPolynomial.T_pow`'s. -/
theorem X_pow (m : ℤ) (k : ℕ) : X R I m ^ k = X R I (k * m) := by
  rw [X_eq_ofAlgHom, ← map_pow, T_pow, X_eq_ofAlgHom]

end RestrictedLaurentSeries

/-! ### Density of the polynomials in the formal polydisc -/

namespace RestrictedPowerSeries

variable {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ)

/-- **The polynomials are dense in the polydisc**: every restricted power series agrees with a
polynomial modulo the `m`-th power of the ideal of definition. -/
theorem exists_sub_mem_idealOfDefinition_pow (hI : I.FG) (m : ℕ)
    (z : RestrictedPowerSeries R I n) :
    ∃ p : MvPolynomial (Fin n) R,
      z - algebraMap (MvPolynomial (Fin n) R) (RestrictedPowerSeries R I n) p ∈
        (idealOfDefinition R I n) ^ m := by
  obtain ⟨p, hp⟩ := Submodule.Quotient.mk_surjective _ (z.val m)
  refine ⟨p, ?_⟩
  rw [mem_idealOfDefinition_pow_iff, AdicCompletion.pow_smul_top_eq_ker_eval (hI.map _),
    LinearMap.mem_ker, map_sub, AdicCompletion.eval_apply, algebraMap_MvPolynomial_apply,
    AdicCompletion.eval_of, Submodule.mkQ_apply, ← hp, sub_self]

end RestrictedPowerSeries

/-! ### `1 − q ^ k` is a unit -/

namespace IsAdicComplete

variable {R : Type u} [CommRing R] {I : Ideal R} [IsAdicComplete I R]

/-- **`1 − a` is a unit for `a` in an ideal of definition of a complete adic ring**: such an
ideal lies in the Jacobson radical. -/
theorem isUnit_one_sub_of_mem {a : R} (ha : a ∈ I) : IsUnit (1 - a) :=
  Ideal.isUnit_of_sub_one_mem_jacobson_bot (1 - a) (by
    have h := IsAdicComplete.le_jacobson_bot I ha
    simpa using Submodule.neg_mem _ h)

/-- **`1 − q ^ k` is a unit** for `q` in an ideal of definition and `k ≠ 0`. -/
theorem isUnit_one_sub_pow {q : R} (hq : q ∈ I) {k : ℕ} (hk : k ≠ 0) : IsUnit (1 - q ^ k) :=
  isUnit_one_sub_of_mem (Ideal.pow_mem_of_mem I hq k (Nat.pos_of_ne_zero hk))

end IsAdicComplete

namespace RestrictedLaurentSeries

variable {R : Type u} [CommRing R] (I : Ideal R) [IsAdicComplete I R]

/-- **`R → R{X, X⁻¹}` is injective for an `I`-adically complete base**, with the degree-zero
coefficient as an explicit retraction. This needs strictly less than
`RestrictedLaurentSeries.algebraMap_injective`, which assumes `[TopologicalSpace R]`
and `[IsAdicRing I]` and goes through evaluation at the unit `1`. -/
theorem algebraMap_injective_of_isAdicComplete :
    Function.Injective (algebraMap R (RestrictedLaurentSeries R I)) := fun r s h => by
  have h0 := congrArg (coeff I 0) h
  rw [coeff_algebraMap, coeff_algebraMap] at h0
  simpa using h0

end RestrictedLaurentSeries

namespace AlgebraicGeometry

/-! ### The two evaluation points of `Ĝm` -/

section Points

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- The evaluation point `(X, q·X⁻¹)` of `Ĝm`: the images of the two annulus coordinates under
`AlgebraicGeometry.tateInvGlobalCoord`. -/
def tateInvCoordPoint : Fin 2 → RestrictedLaurentSeries R I :=
  ![X R I 1, algebraMap R (RestrictedLaurentSeries R I) q * X R I (-1)]

/-- The swapped evaluation point `(q·X⁻¹, X)`, the images of the two coordinates under
`AlgebraicGeometry.tateInvGlobalCoord ∘ (annulusFlip …).symm`. -/
def tateInvCoordPointFlip : Fin 2 → RestrictedLaurentSeries R I :=
  ![algebraMap R (RestrictedLaurentSeries R I) q * X R I (-1), X R I 1]

theorem tateInvCoordPoint_zero : tateInvCoordPoint R I q 0 = X R I 1 := rfl

theorem tateInvCoordPoint_one :
    tateInvCoordPoint R I q 1 = algebraMap R (RestrictedLaurentSeries R I) q * X R I (-1) := rfl

theorem tateInvCoordPointFlip_zero :
    tateInvCoordPointFlip R I q 0 = algebraMap R (RestrictedLaurentSeries R I) q * X R I (-1) :=
  rfl

theorem tateInvCoordPointFlip_one : tateInvCoordPointFlip R I q 1 = X R I 1 := rfl

/-- **On the image of a polynomial the coordinate map is evaluation at `(X, q·X⁻¹)`.** -/
theorem tateInvGlobalCoord_annulusMk_algebraMap (hI : I.FG) (p : MvPolynomial (Fin 2) R) :
    tateInvGlobalCoord R I q hI
        (annulusMk R I q (algebraMap (MvPolynomial (Fin 2) R) (annulusRing R I) p)) =
      MvPolynomial.aeval (tateInvCoordPoint R I q) p := by
  have key : (tateInvGlobalCoord R I q hI).comp
      ((annulusMk R I q).toRingHom.comp
        (algebraMap (MvPolynomial (Fin 2) R) (annulusRing R I))) =
      (MvPolynomial.aeval (tateInvCoordPoint R I q)).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.aeval_C]
      rw [RestrictedPowerSeries.algebraMap_MvPolynomial_apply,
        RestrictedPowerSeries.of_C_eq_algebraMap, AlgHom.commutes,
        tateInvGlobalCoord_algebraMap]
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.aeval_X, tateInvCoordPoint_zero]
      rw [RestrictedPowerSeries.algebraMap_MvPolynomial_apply]
      exact tateInvGlobalCoord_overlapX R I q hI
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.aeval_X, tateInvCoordPoint_one]
      rw [RestrictedPowerSeries.algebraMap_MvPolynomial_apply]
      exact tateInvGlobalCoord_overlapY R I q hI
  exact congrArg (fun F : MvPolynomial (Fin 2) R →+* RestrictedLaurentSeries R I => F p) key

/-- **On the image of a polynomial the flipped coordinate map is evaluation at `(q·X⁻¹, X)`.** -/
theorem tateInvGlobalCoord_annulusFlip_symm_annulusMk_algebraMap (hI : I.FG)
    (p : MvPolynomial (Fin 2) R) :
    tateInvGlobalCoord R I q hI ((annulusFlip R I q hI).symm
        (annulusMk R I q (algebraMap (MvPolynomial (Fin 2) R) (annulusRing R I) p))) =
      MvPolynomial.aeval (tateInvCoordPointFlip R I q) p := by
  have key : (tateInvGlobalCoord R I q hI).comp
      (((annulusFlip R I q hI).symm.toAlgHom.toRingHom).comp
        ((annulusMk R I q).toRingHom.comp
          (algebraMap (MvPolynomial (Fin 2) R) (annulusRing R I)))) =
      (MvPolynomial.aeval (tateInvCoordPointFlip R I q)).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.aeval_C]
      rw [RestrictedPowerSeries.algebraMap_MvPolynomial_apply,
        RestrictedPowerSeries.of_C_eq_algebraMap, AlgHom.commutes, AlgHom.commutes,
        tateInvGlobalCoord_algebraMap]
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.aeval_X, tateInvCoordPointFlip_zero]
      rw [RestrictedPowerSeries.algebraMap_MvPolynomial_apply,
        show annulusMk R I q (annulusX R I) = overlapX R I q from rfl]
      exact congrArg (tateInvGlobalCoord R I q hI) (annulusFlip_symm_overlapX R I q hI) |>.trans
        (tateInvGlobalCoord_overlapY R I q hI)
    · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        MvPolynomial.aeval_X, tateInvCoordPointFlip_one]
      rw [RestrictedPowerSeries.algebraMap_MvPolynomial_apply,
        show annulusMk R I q (annulusY R I) = overlapY R I q from rfl]
      exact congrArg (tateInvGlobalCoord R I q hI) (annulusFlip_symm_overlapY R I q hI) |>.trans
        (tateInvGlobalCoord_overlapX R I q hI)
  exact congrArg (fun F : MvPolynomial (Fin 2) R →+* RestrictedLaurentSeries R I => F p) key

/-- The value of the coordinate map on a monomial: `xⁱyʲ ↦ qʲ·X^(i−j)`. -/
theorem aeval_monomial_tateInvCoordPoint (u : Fin 2 →₀ ℕ) (c : R) :
    MvPolynomial.aeval (tateInvCoordPoint R I q) (MvPolynomial.monomial u c) =
      algebraMap R (RestrictedLaurentSeries R I) (c * q ^ u 1) *
        X R I ((u 0 : ℤ) - (u 1 : ℤ)) := by
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _),
    Fin.prod_univ_two, tateInvCoordPoint_zero, tateInvCoordPoint_one, mul_pow, ← map_pow,
    X_pow, X_pow, map_mul,
    show ((u 0 : ℕ) : ℤ) - ((u 1 : ℕ) : ℤ)
        = ((u 0 : ℕ) : ℤ) * (1 : ℤ) + ((u 1 : ℕ) : ℤ) * (-1 : ℤ) by ring,
    ← X_add]
  ring

/-- The value of the flipped coordinate map on a monomial: `xⁱyʲ ↦ qⁱ·X^(j−i)`. -/
theorem aeval_monomial_tateInvCoordPointFlip (u : Fin 2 →₀ ℕ) (c : R) :
    MvPolynomial.aeval (tateInvCoordPointFlip R I q) (MvPolynomial.monomial u c) =
      algebraMap R (RestrictedLaurentSeries R I) (c * q ^ u 0) *
        X R I ((u 1 : ℤ) - (u 0 : ℤ)) := by
  rw [MvPolynomial.aeval_monomial, Finsupp.prod_fintype _ _ (fun i => pow_zero _),
    Fin.prod_univ_two, tateInvCoordPointFlip_zero, tateInvCoordPointFlip_one, mul_pow, ← map_pow,
    X_pow, X_pow, map_mul,
    show ((u 1 : ℕ) : ℤ) - ((u 0 : ℕ) : ℤ)
        = ((u 0 : ℕ) : ℤ) * (-1 : ℤ) + ((u 1 : ℕ) : ℤ) * (1 : ℤ) by ring,
    ← X_add]
  ring

/-- The composite `R{x, y} → A → R{X, X⁻¹}` is the identity on the base. -/
theorem tateInvGlobalCoord_annulusMk_algebraMap_base (hI : I.FG) (r : R) :
    tateInvGlobalCoord R I q hI (annulusMk R I q (algebraMap R (annulusRing R I) r)) =
      algebraMap R (RestrictedLaurentSeries R I) r := by
  rw [AlgHom.commutes, tateInvGlobalCoord_algebraMap]

/-- The flipped composite is likewise the identity on the base. -/
theorem tateInvGlobalCoord_annulusFlip_symm_annulusMk_algebraMap_base (hI : I.FG) (r : R) :
    tateInvGlobalCoord R I q hI
        ((annulusFlip R I q hI).symm (annulusMk R I q (algebraMap R (annulusRing R I) r))) =
      algebraMap R (RestrictedLaurentSeries R I) r := by
  rw [AlgHom.commutes, (annulusFlip R I q hI).symm.commutes, tateInvGlobalCoord_algebraMap]

/-- **Continuity of the coordinate map on the polydisc**: it carries the powers of the ideal of
definition of `R{x, y}` into those of `R{X, X⁻¹}`. -/
theorem tateInvGlobalCoord_annulusMk_mem_pow (hI : I.FG) (m : ℕ) {w : annulusRing R I}
    (hw : w ∈ (RestrictedPowerSeries.idealOfDefinition R I 2) ^ m) :
    tateInvGlobalCoord R I q hI (annulusMk R I q w) ∈
      (RestrictedLaurentSeries.idealOfDefinition R I) ^ m := by
  rw [RestrictedPowerSeries.idealOfDefinition_eq_map, ← Ideal.map_pow] at hw
  rw [RestrictedLaurentSeries.idealOfDefinition_eq_map, ← Ideal.map_pow]
  have hcomp : ((tateInvGlobalCoord R I q hI).comp (annulusMk R I q).toRingHom).comp
      (algebraMap R (annulusRing R I)) = algebraMap R (RestrictedLaurentSeries R I) :=
    RingHom.ext (tateInvGlobalCoord_annulusMk_algebraMap_base R I q hI)
  have h := Ideal.mem_map_of_mem
    ((tateInvGlobalCoord R I q hI).comp (annulusMk R I q).toRingHom) hw
  rwa [Ideal.map_map, hcomp] at h

/-- **Continuity of the flipped coordinate map on the polydisc.** -/
theorem tateInvGlobalCoord_annulusFlip_symm_annulusMk_mem_pow (hI : I.FG) (m : ℕ)
    {w : annulusRing R I} (hw : w ∈ (RestrictedPowerSeries.idealOfDefinition R I 2) ^ m) :
    tateInvGlobalCoord R I q hI ((annulusFlip R I q hI).symm (annulusMk R I q w)) ∈
      (RestrictedLaurentSeries.idealOfDefinition R I) ^ m := by
  rw [RestrictedPowerSeries.idealOfDefinition_eq_map, ← Ideal.map_pow] at hw
  rw [RestrictedLaurentSeries.idealOfDefinition_eq_map, ← Ideal.map_pow]
  have hcomp : (((tateInvGlobalCoord R I q hI).comp
        (annulusFlip R I q hI).symm.toAlgHom.toRingHom).comp
      (annulusMk R I q).toRingHom).comp (algebraMap R (annulusRing R I)) =
      algebraMap R (RestrictedLaurentSeries R I) :=
    RingHom.ext (tateInvGlobalCoord_annulusFlip_symm_annulusMk_algebraMap_base R I q hI)
  have h := Ideal.mem_map_of_mem
    (((tateInvGlobalCoord R I q hI).comp (annulusFlip R I q hI).symm.toAlgHom.toRingHom).comp
      (annulusMk R I q).toRingHom) hw
  rwa [Ideal.map_map, hcomp] at h

end Points

/-! ### The coefficientwise comparison -/

section Comparison

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R) [IsAdicComplete I R]

/-- **The polynomial case of the comparison.** -/
theorem coeff_aeval_tateInvCoordPoint (p : MvPolynomial (Fin 2) R) (n : ℤ) :
    q ^ n.toNat * coeff I n (MvPolynomial.aeval (tateInvCoordPoint R I q) p) =
      q ^ (-n).toNat * coeff I (-n) (MvPolynomial.aeval (tateInvCoordPointFlip R I q) p) := by
  refine MvPolynomial.induction_on' p ?_ ?_
  · intro u c
    rw [aeval_monomial_tateInvCoordPoint, aeval_monomial_tateInvCoordPointFlip,
      coeff_algebraMap_mul, coeff_algebraMap_mul, coeff_X, coeff_X]
    by_cases h : n = ((u 0 : ℕ) : ℤ) - ((u 1 : ℕ) : ℤ)
    · have h' : -n = ((u 1 : ℕ) : ℤ) - ((u 0 : ℕ) : ℤ) := by omega
      have hexp : n.toNat + u 1 = (-n).toNat + u 0 := by omega
      rw [if_pos h, if_pos h', mul_one, mul_one]
      calc q ^ n.toNat * (c * q ^ u 1) = c * q ^ (n.toNat + u 1) := by rw [pow_add]; ring
        _ = c * q ^ ((-n).toNat + u 0) := by rw [hexp]
        _ = q ^ (-n).toNat * (c * q ^ u 0) := by rw [pow_add]; ring
    · have h' : ¬ (-n = ((u 1 : ℕ) : ℤ) - ((u 0 : ℕ) : ℤ)) := by omega
      rw [if_neg h, if_neg h', mul_zero, mul_zero, mul_zero, mul_zero]
  · intro p₁ p₂ h₁ h₂
    simp only [map_add, mul_add]
    rw [h₁, h₂]

/-- **The two `Ĝm` coordinate maps of the Tate annulus are related coefficientwise by the Tate
parameter.** In degree `n` the flipped map's coefficient in degree `−n` differs from the
coordinate map's coefficient in degree `n` by `q ^ |n|`, stated without division. -/
theorem tateInvGlobalCoord_coeff_flip (hI : I.FG) (a : annulusAlgebra R I q) (n : ℤ) :
    q ^ n.toNat * coeff I n (tateInvGlobalCoord R I q hI a) =
      q ^ (-n).toNat *
        coeff I (-n) (tateInvGlobalCoord R I q hI ((annulusFlip R I q hI).symm a)) := by
  obtain ⟨w, rfl⟩ := annulusMk_surjective R I q a
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := I) (M := R) inferInstance _ fun m => ?_
  rw [SModEq.zero]
  obtain ⟨p, hp⟩ := RestrictedPowerSeries.exists_sub_mem_idealOfDefinition_pow I 2 hI m w
  have hA : coeff I n (tateInvGlobalCoord R I q hI (annulusMk R I q w)) -
      coeff I n (MvPolynomial.aeval (tateInvCoordPoint R I q) p) ∈ I ^ m := by
    have h := coeff_mem_pow I hI n m
      ((RestrictedLaurentSeries.mem_idealOfDefinition_pow_iff R I m _).mp
        (tateInvGlobalCoord_annulusMk_mem_pow R I q hI m hp))
    simp only [map_sub] at h
    rwa [tateInvGlobalCoord_annulusMk_algebraMap] at h
  have hB : coeff I (-n)
        (tateInvGlobalCoord R I q hI ((annulusFlip R I q hI).symm (annulusMk R I q w))) -
      coeff I (-n) (MvPolynomial.aeval (tateInvCoordPointFlip R I q) p) ∈ I ^ m := by
    have h := coeff_mem_pow I hI (-n) m
      ((RestrictedLaurentSeries.mem_idealOfDefinition_pow_iff R I m _).mp
        (tateInvGlobalCoord_annulusFlip_symm_annulusMk_mem_pow R I q hI m hp))
    simp only [map_sub] at h
    rwa [tateInvGlobalCoord_annulusFlip_symm_annulusMk_algebraMap] at h
  have hpoly := coeff_aeval_tateInvCoordPoint R I q p n
  rw [Ideal.mem_smul_top_self_iff]
  have hsplit : q ^ n.toNat * coeff I n (tateInvGlobalCoord R I q hI (annulusMk R I q w)) -
      q ^ (-n).toNat * coeff I (-n)
        (tateInvGlobalCoord R I q hI ((annulusFlip R I q hI).symm (annulusMk R I q w))) =
      q ^ n.toNat * (coeff I n (tateInvGlobalCoord R I q hI (annulusMk R I q w)) -
          coeff I n (MvPolynomial.aeval (tateInvCoordPoint R I q) p)) -
        q ^ (-n).toNat * (coeff I (-n)
            (tateInvGlobalCoord R I q hI
              ((annulusFlip R I q hI).symm (annulusMk R I q w))) -
          coeff I (-n) (MvPolynomial.aeval (tateInvCoordPointFlip R I q) p)) := by
    rw [mul_sub, mul_sub, hpoly]; ring
  rw [hsplit]
  exact (I ^ m).sub_mem ((I ^ m).mul_mem_left _ hA) ((I ^ m).mul_mem_left _ hB)

end Comparison

/-! ### The invariants are constants -/

section Invariants

variable {R : Type u} [CommRing R] {I : Ideal R} {q : R} [IsAdicComplete I R]

/-- **Every nonzero-degree coefficient of an invariant element vanishes.** The overlap condition
says `coeff n (φ a) = coeff (-n) (φ (flip⁻¹ a))` and
`AlgebraicGeometry.tateInvGlobalCoord_coeff_flip` says the two sides differ by `q ^ |n|`; so
`(1 − q ^ |n|) · coeff n (φ a) = 0`, and `1 − q ^ |n|` is a unit. -/
theorem coeff_tateInvGlobalCoord_eq_zero_of_mem (hq : q ∈ I) (hI : I.FG)
    {a : annulusAlgebra R I q} (ha : a ∈ tateInvGlobalSubring (R := R) (I := I) (q := q) hI)
    {n : ℤ} (hn : n ≠ 0) : coeff I n (tateInvGlobalCoord R I q hI a) = 0 := by
  have hcond := (mem_tateInvGlobalSubring_iff_coeff hI a).mp ha n
  have hrel := tateInvGlobalCoord_coeff_flip R I q hI a n
  rw [← hcond] at hrel
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · have h1 : n.toNat = 0 := by omega
    have h2 : (-n).toNat ≠ 0 := by omega
    rw [h1, pow_zero, one_mul] at hrel
    have hz : (1 - q ^ (-n).toNat) * coeff I n (tateInvGlobalCoord R I q hI a) = 0 := by
      rw [sub_mul, one_mul, ← hrel, sub_self]
    exact (IsAdicComplete.isUnit_one_sub_pow hq h2).mul_right_eq_zero.mp hz
  · have h1 : (-n).toNat = 0 := by omega
    have h2 : n.toNat ≠ 0 := by omega
    rw [h1, pow_zero, one_mul] at hrel
    have hz : (1 - q ^ n.toNat) * coeff I n (tateInvGlobalCoord R I q hI a) = 0 := by
      rw [sub_mul, one_mul, hrel, sub_self]
    exact (IsAdicComplete.isUnit_one_sub_pow hq h2).mul_right_eq_zero.mp hz

/-- **An invariant element has constant image in `Ĝm` coordinates.** -/
theorem tateInvGlobalCoord_eq_algebraMap_of_mem (hq : q ∈ I) (hI : I.FG)
    {a : annulusAlgebra R I q} (ha : a ∈ tateInvGlobalSubring (R := R) (I := I) (q := q) hI) :
    tateInvGlobalCoord R I q hI a =
      algebraMap R (RestrictedLaurentSeries R I)
        (coeff I 0 (tateInvGlobalCoord R I q hI a)) := by
  refine ext_coeff I fun n => ?_
  rw [coeff_algebraMap]
  by_cases h : n = 0
  · rw [if_pos h, h]
  · rw [if_neg h, coeff_tateInvGlobalCoord_eq_zero_of_mem hq hI ha h]

end Invariants

/-! ### The headline, conditional on one separation property -/

section Headline

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- **The separation property that is all that stands between the tree and
`Γ (T_inv/⟨σ⟩) ≃+* R`**: the coordinate map and its flip have zero common kernel, i.e.
`a ↦ (φ a, φ (flip⁻¹ a))` is injective. This is the *uniqueness* half of a normal form for
`A = R{x, y}/(x·y − q)`; the existence half is not needed. -/
def IsTateInvCoordSeparating (hI : I.FG) : Prop :=
  ∀ a : annulusAlgebra R I q, tateInvGlobalCoord R I q hI a = 0 →
    tateInvGlobalCoord R I q hI ((annulusFlip R I q hI).symm a) = 0 → a = 0

variable {R I q}
variable [IsAdicComplete I R]

/-- **`Γ (T_inv/⟨σ⟩)` is exactly the image of the base**, given the separation property. -/
theorem tateInvGlobalSubring_eq_range (hq : q ∈ I) (hI : I.FG)
    (hsep : IsTateInvCoordSeparating R I q hI) :
    tateInvGlobalSubring (R := R) (I := I) (q := q) hI =
      (algebraMap R (annulusAlgebra R I q)).range := by
  refine le_antisymm (fun a ha => ?_) ?_
  · refine ⟨coeff I 0 (tateInvGlobalCoord R I q hI a), ?_⟩
    have hb : a - algebraMap R (annulusAlgebra R I q)
        (coeff I 0 (tateInvGlobalCoord R I q hI a)) ∈
        tateInvGlobalSubring (R := R) (I := I) (q := q) hI :=
      Subring.sub_mem _ ha (algebraMap_mem_tateInvGlobalSubring hI _)
    have h1 : tateInvGlobalCoord R I q hI
        (a - algebraMap R (annulusAlgebra R I q)
          (coeff I 0 (tateInvGlobalCoord R I q hI a))) = 0 := by
      rw [map_sub, tateInvGlobalCoord_algebraMap,
        ← tateInvGlobalCoord_eq_algebraMap_of_mem hq hI ha, sub_self]
    have h2 : tateInvGlobalCoord R I q hI ((annulusFlip R I q hI).symm
        (a - algebraMap R (annulusAlgebra R I q)
          (coeff I 0 (tateInvGlobalCoord R I q hI a)))) = 0 := by
      refine eq_zero_of_coeff_eq_zero I fun n => ?_
      have hn := (mem_tateInvGlobalSubring_iff_coeff hI _).mp hb (-n)
      rw [neg_neg] at hn
      rw [← hn, h1, map_zero]
    have h3 := hsep _ h1 h2
    rw [sub_eq_zero] at h3
    exact h3.symm
  · rintro x ⟨r, rfl⟩
    exact algebraMap_mem_tateInvGlobalSubring hI r

/-- The structural map `R → Γ (T_inv/⟨σ⟩)`. -/
def tateInvGlobalAlgebraMap (hI : I.FG) :
    R →+* tateInvGlobalSubring (R := R) (I := I) (q := q) hI :=
  (algebraMap R (annulusAlgebra R I q)).codRestrict _
    (algebraMap_mem_tateInvGlobalSubring hI)

omit [IsAdicComplete I R] in
theorem tateInvGlobalAlgebraMap_coe (hI : I.FG) (r : R) :
    (tateInvGlobalAlgebraMap (R := R) (I := I) (q := q) hI r : annulusAlgebra R I q) =
      algebraMap R (annulusAlgebra R I q) r := rfl

theorem tateInvGlobalAlgebraMap_injective (hI : I.FG) :
    Function.Injective (tateInvGlobalAlgebraMap (R := R) (I := I) (q := q) hI) := by
  intro r s h
  have h1 : algebraMap R (annulusAlgebra R I q) r = algebraMap R (annulusAlgebra R I q) s :=
    congrArg Subtype.val h
  have h2 := congrArg (tateInvGlobalCoord R I q hI) h1
  rw [tateInvGlobalCoord_algebraMap, tateInvGlobalCoord_algebraMap] at h2
  exact RestrictedLaurentSeries.algebraMap_injective_of_isAdicComplete I h2

/-- **`Γ (T_inv/⟨σ⟩) ≃+* R`** — the formal-geometry shadow of properness of the Néron 1-gon —
given the separation property. -/
def tateInvGlobalSubringEquivBase (hq : q ∈ I) (hI : I.FG)
    (hsep : IsTateInvCoordSeparating R I q hI) :
    tateInvGlobalSubring (R := R) (I := I) (q := q) hI ≃+* R :=
  (RingEquiv.ofBijective (tateInvGlobalAlgebraMap (R := R) (I := I) (q := q) hI)
    ⟨tateInvGlobalAlgebraMap_injective hI, by
      rintro ⟨a, ha⟩
      rw [tateInvGlobalSubring_eq_range hq hI hsep] at ha
      obtain ⟨r, hr⟩ := ha
      exact ⟨r, Subtype.ext hr⟩⟩).symm

end Headline

/-! ### The headline at the level of global sections -/

section Sections

open CategoryTheory TopologicalSpace

variable {R : Type u} [CommRing R] {I : Ideal R} {q : R}
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R]

/-- **`Γ (T_inv/⟨σ⟩, ⊤) ≃+* R`** — the formal-geometry shadow of properness of the Néron 1-gon
(Deligne–Rapoport II.1) — given `AlgebraicGeometry.IsTateInvCoordSeparating`. This is
`AlgebraicGeometry.tateInvGlobalSectionsRingEquiv` composed with
`AlgebraicGeometry.tateInvGlobalSubringEquivBase`; the completeness needed by the second is
`IsAdicRing.toIsAdicComplete`. -/
def tateInvPeriodQuotientGlobalSectionsEquivBase (hq : q ∈ I) (hI : I.FG)
    (hsep : IsTateInvCoordSeparating R I q hI) :
    ((actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj
      (Opposite.op (⊤ : Opens (actionQuotient
        (tateInvPeriodAction R I q hq hI)).toTopCat))) ≃+* R :=
  haveI _hc : IsAdicComplete I R := ‹IsAdicRing I›.toIsAdicComplete
  (tateInvGlobalSectionsRingEquiv hq hI).trans (tateInvGlobalSubringEquivBase hq hI hsep)

end Sections

/-! ### The coordinate map alone is not injective -/

section NotInjective

variable (R : Type u) [CommRing R] [Nontrivial R] (I : Ideal R) [IsAdicComplete I R]

/-- **The coordinate map alone is not injective**, so the separating hypothesis cannot be
weakened to injectivity of `AlgebraicGeometry.tateInvGlobalCoord`. At `q = 0` the map kills the
second coordinate outright (`AlgebraicGeometry.tateInvGlobalCoord_overlapY` reads `y ↦ q·X⁻¹`),
while the flipped map sends it to `X ≠ 0`; so `y ≠ 0` and `y` is in the kernel. -/
theorem not_injective_tateInvGlobalCoord_zero (hI : I.FG) :
    ¬ Function.Injective (tateInvGlobalCoord R I 0 hI) := by
  intro hinj
  have h1 : tateInvGlobalCoord R I 0 hI (overlapY R I 0) = 0 := by
    rw [tateInvGlobalCoord_overlapY, map_zero, zero_mul]
  have h0 : overlapY R I 0 = 0 := hinj (h1.trans (map_zero _).symm)
  have h2 : tateInvGlobalCoord R I 0 hI ((annulusFlip R I 0 hI).symm (overlapY R I 0)) =
      X R I 1 := by
    rw [annulusFlip_symm_overlapY, tateInvGlobalCoord_overlapX]
  rw [h0, map_zero, map_zero] at h2
  have h3 := congrArg (coeff I 1) h2
  rw [map_zero, coeff_X, if_pos rfl] at h3
  exact zero_ne_one h3


/-- **The refutation is not vacuous.** `R = ℤ`, `I = ⊥`, `q = 0` satisfies every hypothesis of
`AlgebraicGeometry.not_injective_tateInvGlobalCoord_zero`: `ℤ` is nontrivial, `⊥` is finitely
generated, and `IsAdicComplete (⊥ : Ideal ℤ) ℤ` is found by instance search. So the coordinate map
really does have a nonzero kernel over an admissible base, and not merely in principle. -/
theorem not_injective_tateInvGlobalCoord_zero_int :
    ¬ Function.Injective (tateInvGlobalCoord ℤ ⊥ 0 Submodule.fg_bot) :=
  not_injective_tateInvGlobalCoord_zero ℤ ⊥ Submodule.fg_bot

end NotInjective

end AlgebraicGeometry
