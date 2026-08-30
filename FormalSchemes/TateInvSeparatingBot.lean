import FormalSchemes.TateInvGlobalNormalForm

set_option linter.style.header false

/-!
# The separation hypothesis holds over a discrete base

`FormalSchemes.TateInvGlobalNormalForm` proves `Γ (T_inv/⟨σ⟩) ≃+* R` from one hypothesis,
`AlgebraicGeometry.IsTateInvCoordSeparating`, and proves that hypothesis for no `(R, I, q)`;
`FormalSchemes.TateInvSeparatingKerClosed` measures what the hypothesis costs but does not
discharge it. **Every conditional statement of that cluster was therefore unverified for
non-vacuity.** This file removes that doubt, for the whole family `I = ⊥`, `q = 0`.

## The statement

`AlgebraicGeometry.isTateInvCoordSeparating_bot`: for **every** commutative ring `R`,

```
IsTateInvCoordSeparating R ⊥ 0 Submodule.fg_bot
```

with no further hypothesis — `IsAdicComplete (⊥ : Ideal R) R` is automatic, `(⊥ : Ideal R).FG`
is `Submodule.fg_bot`, and `q = 0` is forced by `q ∈ ⊥`, so this is the *only* shape a discrete
base can take and the whole of it is covered. `AlgebraicGeometry.isTateInvCoordSeparating_int` is
the instance at `R = ℤ`, the tree's standing non-vacuity witness.

## Why the discrete case is a genuine computation and not a degeneracy

At `I = ⊥` the polydisc `R{x, y}` is the polynomial ring `R[x, y]` — `AdicCompletion.of` is
bijective because `R[x, y]` is already `⊥`-adically complete — so `A = R[x, y]/(x·y)`, and the
two coordinate maps are the two evaluations

```
φ       :  x ↦ X,  y ↦ q·X⁻¹ = 0
φ ∘ flip⁻¹ :  x ↦ 0,  y ↦ X
```

into `R{X, X⁻¹}`. Separation is then exactly the statement that a polynomial killed by both
`y ↦ 0` and `x ↦ 0` lies in `(x·y)` — which is **false for the individual maps** and is the
reason the hypothesis is stated jointly. `AlgebraicGeometry.not_injective_tateInvGlobalCoord_zero`
already records that `φ` alone is not injective at `q = 0`, so this file is proving something
that map cannot give.

The proof reads a coefficient of the image off a coefficient of the polynomial
(`AlgebraicGeometry.coeff_tateInvBotCoordX`, `AlgebraicGeometry.coeff_tateInvBotCoordY`), which
forces every monomial in the support of a jointly-killed polynomial to be divisible by both
variables, and closes with `MvPolynomial.mem_ideal_span_monomial_image`.

## What this does *not* prove

**Nothing about a base with `I ≠ ⊥`.** The general case is untouched, and so is every route to
it: no coefficient API for the two-variable polydisc is built here, and the argument below uses
`I = ⊥` twice essentially — once to identify the polydisc with a polynomial ring, and once
through `q = 0` to make the two evaluations kill a variable each. Whether
`IsTateInvCoordSeparating` holds for, say, `R = ℤ_p`, `I = (p)`, `q = p` is exactly as open as it
was before.

In particular this file does **not** make `AlgebraicGeometry.tateInvGlobalSubringEquivBase` or
`AlgebraicGeometry.tateInvPeriodQuotientGlobalSectionsEquivBase` unconditional. It makes them
non-vacuous.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7, §9.
-/

noncomputable section

open RestrictedLaurentSeries MvPolynomial

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R]

/-! ### The polydisc over a discrete base is the polynomial ring -/

/-- The structural map `R[x, y] → R{x, y}` at `I = ⊥`. It is a ring isomorphism
(`AlgebraicGeometry.bijective_polydiscOfBot`), which is what makes the whole file a computation
with polynomials. -/
def polydiscOfBot : MvPolynomial (Fin 2) R →+* annulusRing R ⊥ :=
  algebraMap (MvPolynomial (Fin 2) R) (annulusRing R ⊥)

/-- **The polydisc over a discrete base is the polynomial ring**: `R[x, y]` is already
`⊥`-adically complete, so `AdicCompletion.of` is bijective. -/
theorem bijective_polydiscOfBot : Function.Bijective (polydiscOfBot R) := by
  haveI : IsAdicComplete (Ideal.map (algebraMap R (MvPolynomial (Fin 2) R)) ⊥)
      (MvPolynomial (Fin 2) R) := by rw [Ideal.map_bot]; infer_instance
  exact AdicCompletion.of_bijective _ _

theorem polydiscOfBot_X_zero : polydiscOfBot R (X 0) = annulusX R ⊥ := rfl

theorem polydiscOfBot_X_one : polydiscOfBot R (X 1) = annulusY R ⊥ := rfl

/-! ### The two coordinate maps, read on polynomials -/

/-- The `x`-chart coordinate map, precomposed with `R[x, y] ↠ A`. It sends `x ↦ X` and `y ↦ 0`,
because `y ↦ q·X⁻¹` and `q = 0`. -/
def tateInvBotCoordX : MvPolynomial (Fin 2) R →+* RestrictedLaurentSeries R ⊥ :=
  (tateInvGlobalCoord R ⊥ 0 Submodule.fg_bot).comp
    ((annulusMk R ⊥ 0).toRingHom.comp (polydiscOfBot R))

/-- The flipped coordinate map, precomposed with `R[x, y] ↠ A`. It sends `x ↦ 0` and `y ↦ X`. -/
def tateInvBotCoordY : MvPolynomial (Fin 2) R →+* RestrictedLaurentSeries R ⊥ :=
  ((tateInvGlobalCoord R ⊥ 0 Submodule.fg_bot).comp
    (annulusFlip R ⊥ 0 Submodule.fg_bot).symm.toAlgHom.toRingHom).comp
      ((annulusMk R ⊥ 0).toRingHom.comp (polydiscOfBot R))

variable {R}

theorem tateInvBotCoordX_X_zero :
    tateInvBotCoordX R (X 0) = RestrictedLaurentSeries.X R ⊥ 1 :=
  tateInvGlobalCoord_overlapX R ⊥ 0 _

theorem tateInvBotCoordX_X_one : tateInvBotCoordX R (X 1) = 0 := by
  change tateInvGlobalCoord R ⊥ 0 Submodule.fg_bot (overlapY R ⊥ 0) = 0
  rw [tateInvGlobalCoord_overlapY, map_zero, zero_mul]

theorem tateInvBotCoordY_X_zero : tateInvBotCoordY R (X 0) = 0 := by
  change tateInvGlobalCoord R ⊥ 0 Submodule.fg_bot
    ((annulusFlip R ⊥ 0 Submodule.fg_bot).symm (overlapX R ⊥ 0)) = 0
  rw [annulusFlip_symm_overlapX, tateInvGlobalCoord_overlapY, map_zero, zero_mul]

theorem tateInvBotCoordY_X_one :
    tateInvBotCoordY R (X 1) = RestrictedLaurentSeries.X R ⊥ 1 := by
  change tateInvGlobalCoord R ⊥ 0 Submodule.fg_bot
    ((annulusFlip R ⊥ 0 Submodule.fg_bot).symm (overlapY R ⊥ 0)) = _
  rw [annulusFlip_symm_overlapY]
  exact tateInvGlobalCoord_overlapX R ⊥ 0 _

theorem tateInvBotCoordX_C (r : R) :
    tateInvBotCoordX R (C r) = algebraMap R (RestrictedLaurentSeries R ⊥) r := by
  change tateInvGlobalCoord R ⊥ 0 Submodule.fg_bot (algebraMap R (annulusAlgebra R ⊥ 0) r) = _
  rw [tateInvGlobalCoord_algebraMap]

theorem tateInvBotCoordY_C (r : R) :
    tateInvBotCoordY R (C r) = algebraMap R (RestrictedLaurentSeries R ⊥) r := by
  change tateInvGlobalCoord R ⊥ 0 Submodule.fg_bot
    ((annulusFlip R ⊥ 0 Submodule.fg_bot).symm (algebraMap R (annulusAlgebra R ⊥ 0) r)) = _
  rw [AlgEquiv.commutes, tateInvGlobalCoord_algebraMap]

/-! ### Reading a coefficient of the image off a coefficient of the polynomial -/

/-- A monomial of `R[x, y]` in the two variables explicitly. -/
theorem monomial_finTwo_eq (d : Fin 2 →₀ ℕ) (c : R) :
    (monomial d c : MvPolynomial (Fin 2) R) = C c * (X 0 ^ d 0 * X 1 ^ d 1) := by
  rw [MvPolynomial.monomial_eq]
  congr 1
  rw [Finsupp.prod_fintype _ _ fun i => pow_zero (X i)]
  exact Fin.prod_univ_two fun i => X i ^ d i

/-- A two-variable exponent is `Finsupp.single 0 k` exactly when it has `x`-degree `k` and
no `y`. -/
theorem finTwo_eq_single_zero_iff {d : Fin 2 →₀ ℕ} {k : ℕ} :
    d = Finsupp.single (0 : Fin 2) k ↔ d 0 = k ∧ d 1 = 0 := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ?_⟩
  · simpa using congrArg (fun f => f (0 : Fin 2)) h
  · simpa using congrArg (fun f => f (1 : Fin 2)) h
  · refine Finsupp.ext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩) <;> simp [h.1, h.2]

/-- A two-variable exponent is `Finsupp.single 1 k` exactly when it has `y`-degree `k` and
no `x`. -/
theorem finTwo_eq_single_one_iff {d : Fin 2 →₀ ℕ} {k : ℕ} :
    d = Finsupp.single (1 : Fin 2) k ↔ d 1 = k ∧ d 0 = 0 := by
  refine ⟨fun h => ⟨?_, ?_⟩, fun h => ?_⟩
  · simpa using congrArg (fun f => f (1 : Fin 2)) h
  · simpa using congrArg (fun f => f (0 : Fin 2)) h
  · refine Finsupp.ext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩) <;> simp [h.1, h.2]

/-- **The `k`-th coefficient of the `x`-chart image is the coefficient of `xᵏ`.** The map kills
every monomial involving `y`, and carries `xᵏ` to the variable `X ^ k`. -/
theorem coeff_tateInvBotCoordX (p : MvPolynomial (Fin 2) R) (k : ℕ) :
    RestrictedLaurentSeries.coeff (⊥ : Ideal R) (k : ℤ) (tateInvBotCoordX R p) =
      MvPolynomial.coeff (Finsupp.single 0 k) p := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    have himg : tateInvBotCoordX R (monomial d c) =
        algebraMap R (RestrictedLaurentSeries R ⊥) c *
          (RestrictedLaurentSeries.X R ⊥ 1 ^ d 0 *
            (0 : RestrictedLaurentSeries R ⊥) ^ d 1) := by
      rw [monomial_finTwo_eq, map_mul, map_mul, map_pow, map_pow, tateInvBotCoordX_C,
        tateInvBotCoordX_X_zero, tateInvBotCoordX_X_one]
    rw [himg, MvPolynomial.coeff_monomial]
    by_cases hd : d 1 = 0
    · rw [hd, pow_zero, mul_one, RestrictedLaurentSeries.X_pow, mul_one,
        RestrictedLaurentSeries.coeff_algebraMap_mul, RestrictedLaurentSeries.coeff_X]
      by_cases hk : k = d 0
      · rw [if_pos (finTwo_eq_single_zero_iff.mpr ⟨hk.symm, hd⟩), if_pos (by exact_mod_cast hk),
          mul_one]
      · rw [if_neg fun h => hk (finTwo_eq_single_zero_iff.mp h).1.symm,
          if_neg (by exact_mod_cast hk), mul_zero]
    · rw [zero_pow hd, mul_zero, mul_zero, map_zero,
        if_neg fun h => hd (finTwo_eq_single_zero_iff.mp h).2]
  | add p q hp hq => rw [map_add, map_add, MvPolynomial.coeff_add, hp, hq]

/-- **The `k`-th coefficient of the flipped image is the coefficient of `yᵏ`.** -/
theorem coeff_tateInvBotCoordY (p : MvPolynomial (Fin 2) R) (k : ℕ) :
    RestrictedLaurentSeries.coeff (⊥ : Ideal R) (k : ℤ) (tateInvBotCoordY R p) =
      MvPolynomial.coeff (Finsupp.single 1 k) p := by
  induction p using MvPolynomial.induction_on' with
  | monomial d c =>
    have himg : tateInvBotCoordY R (monomial d c) =
        algebraMap R (RestrictedLaurentSeries R ⊥) c *
          ((0 : RestrictedLaurentSeries R ⊥) ^ d 0 *
            RestrictedLaurentSeries.X R ⊥ 1 ^ d 1) := by
      rw [monomial_finTwo_eq, map_mul, map_mul, map_pow, map_pow, tateInvBotCoordY_C,
        tateInvBotCoordY_X_zero, tateInvBotCoordY_X_one]
    rw [himg, MvPolynomial.coeff_monomial]
    by_cases hd : d 0 = 0
    · rw [hd, pow_zero, one_mul, RestrictedLaurentSeries.X_pow, mul_one,
        RestrictedLaurentSeries.coeff_algebraMap_mul, RestrictedLaurentSeries.coeff_X]
      by_cases hk : k = d 1
      · rw [if_pos (finTwo_eq_single_one_iff.mpr ⟨hk.symm, hd⟩), if_pos (by exact_mod_cast hk),
          mul_one]
      · rw [if_neg fun h => hk (finTwo_eq_single_one_iff.mp h).1.symm,
          if_neg (by exact_mod_cast hk), mul_zero]
    · rw [zero_pow hd, zero_mul, mul_zero, map_zero,
        if_neg fun h => hd (finTwo_eq_single_one_iff.mp h).2]
  | add p q hp hq => rw [map_add, map_add, MvPolynomial.coeff_add, hp, hq]

/-! ### The separation property over a discrete base -/

/-- `x·y` as a monomial, so that `MvPolynomial.mem_ideal_span_monomial_image` applies to the
ideal it spans. -/
theorem X_zero_mul_X_one_eq_monomial :
    (X 0 * X 1 : MvPolynomial (Fin 2) R) =
      monomial (Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1) 1 := by
  rw [show (X 0 : MvPolynomial (Fin 2) R) = X 0 ^ 1 from (pow_one _).symm,
    show (X 1 : MvPolynomial (Fin 2) R) = X 1 ^ 1 from (pow_one _).symm,
    MvPolynomial.X_pow_eq_monomial, MvPolynomial.X_pow_eq_monomial, monomial_mul, mul_one]

/-- **A polynomial killed by both evaluations is divisible by `x·y`.** Every exponent in its
support has positive degree in each variable — otherwise it is a `Finsupp.single` and the
corresponding coefficient is one of the vanishing ones — so
`MvPolynomial.mem_ideal_span_monomial_image` applies. -/
theorem mem_span_X_mul_X_of_coord_eq_zero {p : MvPolynomial (Fin 2) R}
    (hx : tateInvBotCoordX R p = 0) (hy : tateInvBotCoordY R p = 0) :
    p ∈ Ideal.span {(X 0 * X 1 : MvPolynomial (Fin 2) R)} := by
  have hsingle : ∀ d ∈ p.support,
      Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1 ≤ d := by
    intro d hd
    have hne : MvPolynomial.coeff d p ≠ 0 := MvPolynomial.mem_support_iff.mp hd
    have h0 : d 0 ≠ 0 := by
      intro h
      refine hne ?_
      rw [finTwo_eq_single_one_iff.mpr ⟨rfl, h⟩, ← coeff_tateInvBotCoordY p (d 1), hy, map_zero]
    have h1 : d 1 ≠ 0 := by
      intro h
      refine hne ?_
      rw [finTwo_eq_single_zero_iff.mpr ⟨rfl, h⟩, ← coeff_tateInvBotCoordX p (d 0), hx, map_zero]
    refine Finsupp.le_def.mpr (Fin.forall_fin_two.mpr ⟨?_, ?_⟩) <;> simp <;> omega
  have himg : ({(X 0 * X 1 : MvPolynomial (Fin 2) R)} : Set (MvPolynomial (Fin 2) R)) =
      (fun s => monomial s (1 : R)) ''
        {Finsupp.single (0 : Fin 2) 1 + Finsupp.single (1 : Fin 2) 1} := by
    rw [Set.image_singleton, X_zero_mul_X_one_eq_monomial]
  rw [himg]
  exact MvPolynomial.mem_ideal_span_monomial_image.mpr fun d hd =>
    ⟨_, rfl, hsingle d hd⟩

/-- **The separation property holds over every discrete base.** At `I = ⊥` the Tate parameter is
forced to be `0`, the polydisc is the polynomial ring `R[x, y]`, and the two coordinate maps are
the evaluations `y ↦ 0` and `x ↦ 0`; a polynomial killed by both has every monomial divisible by
`x·y`, which is exactly the presentation ideal.

This is the **non-vacuity witness** for the whole conditional cluster of
`FormalSchemes.TateInvGlobalNormalForm`: `AlgebraicGeometry.tateInvGlobalSubringEquivBase` and
`AlgebraicGeometry.tateInvPeriodQuotientGlobalSectionsEquivBase` are statements about a
hypothesis that some `(R, I, q)` satisfies. It does **not** make them unconditional. -/
theorem isTateInvCoordSeparating_bot (R : Type u) [CommRing R] :
    IsTateInvCoordSeparating R ⊥ 0 Submodule.fg_bot := by
  intro a hx hy
  obtain ⟨w, rfl⟩ := annulusMk_surjective R ⊥ 0 a
  obtain ⟨p, rfl⟩ := (bijective_polydiscOfBot R).surjective w
  have hmem := mem_span_X_mul_X_of_coord_eq_zero (R := R) (p := p) hx hy
  obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton'.mp hmem
  rw [map_mul, map_mul]
  refine mul_eq_zero_of_right _ ?_
  refine (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.subset_span ?_)
  rw [Set.mem_singleton_iff, annulusRel, map_zero, sub_zero]
  rfl

/-- **Non-vacuity at the tree's standing witness** `R = ℤ`, `I = ⊥`, `q = 0`. -/
theorem isTateInvCoordSeparating_int :
    IsTateInvCoordSeparating ℤ ⊥ 0 Submodule.fg_bot :=
  isTateInvCoordSeparating_bot ℤ

end AlgebraicGeometry
