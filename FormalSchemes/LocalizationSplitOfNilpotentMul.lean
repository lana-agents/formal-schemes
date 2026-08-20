import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.RingTheory.Localization.Away.Basic

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000

/-!
# A ring splits as a product of two localizations when `f + g` is a unit and `f · g` is nilpotent

Let `T` be a commutative ring and `f g : T` with `IsUnit (f + g)` and `IsNilpotent (f · g)`.
Geometrically `D(f)` and `D(g)` then cover `Spec T` (because `f + g` is a unit) and are disjoint
(because `f · g` is nilpotent), so `Spec T = D(f) ⊔ D(g)` as a topological space — and a disjoint
open cover of an affine scheme by two pieces is a product decomposition of the ring:

```
T ≃ₐ[R] T_f × T_g .
```

This file proves that.

## The construction

Write `u = f + g` (a unit) and `x = f · u⁻¹`, so that `1 - x = g · u⁻¹` and
`x · (1 - x) = f · g · u⁻²` is nilpotent, say `(f·g)ⁿ = 0`. Then `x` is idempotent *modulo
nilpotents*, and

```
ε = 1 - (1 - xⁿ)ⁿ
```

is the genuine idempotent lifting it (`isIdempotentElem_one_sub_one_sub_pow_pow`). The two corners
`T ⧸ (1 - ε)` and `T ⧸ (ε)` are then the two localizations, which is the content of
`RingSplit.isLocalization_away_left` / `_right`: in `T ⧸ (1 - ε)` the element `f` is a unit and
`fⁿ · (1 - ε) = 0` kills exactly the kernel, so the quotient map satisfies the universal property
of `T_f` (and symmetrically for `g`). Assembling with `AlgEquiv.prodQuotientOfIsIdempotentElem`
gives the splitting.

Both annihilation identities come from the same source, the geometric-series factorisation
`1 - xⁿ = (1 - x) · Σ xⁱ`: it gives `xⁿ · (1 - xⁿ)ⁿ = (x(1-x))ⁿ · (Σ xⁱ)ⁿ = 0`, and dually
`ε = xⁿ · Σ (1 - xⁿ)ⁱ`, whence `(1-x)ⁿ · ε = 0`.

## Main results

* `RingSplit.isLocalization_away_left`, `RingSplit.isLocalization_away_right`: the two corners are
  the localizations away from `f` and from `g`. These are the reusable content — a consumer that
  wants an explicit model of `T_f` can take the quotient rather than `Localization.Away f`.
* `RingSplit.awaySplitEquiv`, `RingSplit.awaySplitEquivOfIsNilpotent`:
  `T ≃ₐ[R] Localization.Away f × Localization.Away g`, for any base ring `R` over which `T` is an
  algebra.

The intended application (issues 601/603) is the two-chart overlap of the Tate curve model, where
`f = x`, `g = y` and `f · g = q`. Note that `q` is only *topologically* nilpotent in the Tate
annulus, so this lemma does **not** apply to that ring directly: it applies level by level, to
`(A_{x+y}) ⧸ (I·A)ᵐ`, where `q` is genuinely nilpotent. Assembling the levels is a separate step.

## References

* [The Stacks Project, Tag 00EE](https://stacks.math.columbia.edu/tag/00EE) (idempotents and
  disconnections of `Spec`), Tag 00J9 (lifting idempotents along a nil ideal).
* Mathlib `Mathlib/RingTheory/Idempotents.lean`.
-/

noncomputable section

universe u

namespace RingSplit

variable {T : Type u} [CommRing T] {f g : T}

/-- The element `x = f · (f + g)⁻¹`, idempotent modulo nilpotents: it is `1` on `D(f)` and `0` on
`D(g)`. -/
def splitElem (hu : IsUnit (f + g)) : T := f * ↑hu.unit⁻¹

/-- `(f + g) · (f + g)⁻¹ = 1`, in the spelling `hu.unit⁻¹` used throughout. -/
theorem mul_unit_inv (hu : IsUnit (f + g)) : (f + g) * ↑hu.unit⁻¹ = 1 := by
  have h := hu.unit.mul_inv
  rwa [hu.unit_spec] at h

/-- The complementary element: `1 - x = g · u⁻¹`. -/
theorem one_sub_splitElem (hu : IsUnit (f + g)) : 1 - splitElem hu = g * ↑hu.unit⁻¹ := by
  refine (eq_sub_of_add_eq ?_).symm
  rw [splitElem, ← add_mul, add_comm g f]
  exact mul_unit_inv hu

/-- `x · (1 - x) = f · g · u⁻²` — the product `f · g` is what obstructs idempotency. -/
theorem splitElem_mul_one_sub (hu : IsUnit (f + g)) :
    splitElem hu * (1 - splitElem hu) = f * g * (↑hu.unit⁻¹ * ↑hu.unit⁻¹) := by
  rw [one_sub_splitElem, splitElem]
  ring

/-- `x · u = f`. -/
theorem mul_splitElem (hu : IsUnit (f + g)) : splitElem hu * ↑hu.unit = f := by
  rw [splitElem, mul_assoc, hu.unit.inv_mul, mul_one]

/-- `(1 - x) · u = g`. -/
theorem mul_one_sub_splitElem (hu : IsUnit (f + g)) : (1 - splitElem hu) * ↑hu.unit = g := by
  rw [one_sub_splitElem, mul_assoc, hu.unit.inv_mul, mul_one]

/-- `x` is idempotent modulo nilpotents: `(x - x²)ⁿ = 0` whenever `(f · g)ⁿ = 0`. This is the
hypothesis of `isIdempotentElem_one_sub_one_sub_pow_pow`. -/
theorem splitElem_sub_sq_pow (hu : IsUnit (f + g)) {n : ℕ} (hfg : (f * g) ^ n = 0) :
    (splitElem hu - splitElem hu ^ 2) ^ n = 0 := by
  have h : splitElem hu - splitElem hu ^ 2 = f * g * (↑hu.unit⁻¹ * ↑hu.unit⁻¹) := by
    rw [← splitElem_mul_one_sub hu]
    ring
  rw [h, mul_pow, hfg, zero_mul]

/-- The same in the factored form `(x · (1 - x))ⁿ = 0`. -/
theorem splitElem_mul_one_sub_pow (hu : IsUnit (f + g)) {n : ℕ} (hfg : (f * g) ^ n = 0) :
    (splitElem hu * (1 - splitElem hu)) ^ n = 0 := by
  have h : splitElem hu * (1 - splitElem hu) = splitElem hu - splitElem hu ^ 2 := by ring
  rw [h]
  exact splitElem_sub_sq_pow hu hfg

/-- The geometric-series factorisation `1 - xⁿ = (1 - x) · Σ_{i<n} xⁱ`, the source of both
annihilation identities below. -/
theorem one_sub_pow_eq (x : T) (n : ℕ) :
    1 - x ^ n = (1 - x) * ∑ i ∈ Finset.range n, x ^ i := by
  have h : (∑ i ∈ Finset.range n, x ^ i) * (x - 1) = x ^ n - 1 := geom_sum_mul x n
  have h2 : (1 - x) * (∑ i ∈ Finset.range n, x ^ i) =
      -((∑ i ∈ Finset.range n, x ^ i) * (x - 1)) := by ring
  rw [h2, h]
  ring

/-- **The idempotent cutting `Spec T` into `D(f)` and `D(g)`**: the canonical lift of `splitElem`
along the nilpotents, `ε = 1 - (1 - xⁿ)ⁿ`. -/
def splitIdem (hu : IsUnit (f + g)) (n : ℕ) : T := 1 - (1 - splitElem hu ^ n) ^ n

/-- The complementary idempotent is `(1 - xⁿ)ⁿ`. -/
theorem one_sub_splitIdem (hu : IsUnit (f + g)) (n : ℕ) :
    1 - splitIdem hu n = (1 - splitElem hu ^ n) ^ n := by
  rw [splitIdem]
  ring

/-- `ε` is idempotent. -/
theorem splitIdem_isIdempotentElem (hu : IsUnit (f + g)) {n : ℕ} (hfg : (f * g) ^ n = 0) :
    IsIdempotentElem (splitIdem hu n) :=
  isIdempotentElem_one_sub_one_sub_pow_pow _ n (splitElem_sub_sq_pow hu hfg)

/-- **`fⁿ` annihilates `1 - ε`.** This is what makes the corner `T ⧸ (1 - ε)` the localization at
`f`: the kernel of `T → T ⧸ (1 - ε)` is exactly what inverting `f` kills. -/
theorem pow_mul_one_sub_splitIdem (hu : IsUnit (f + g)) {n : ℕ} (hfg : (f * g) ^ n = 0) :
    f ^ n * (1 - splitIdem hu n) = 0 := by
  have h1 : (splitElem hu * ↑hu.unit) ^ n = f ^ n := by rw [mul_splitElem]
  have h2 : f ^ n * (1 - splitIdem hu n) =
      (splitElem hu * (1 - splitElem hu)) ^ n *
        (↑hu.unit ^ n * (∑ i ∈ Finset.range n, splitElem hu ^ i) ^ n) := by
    rw [← h1, one_sub_splitIdem, one_sub_pow_eq (splitElem hu) n, mul_pow, mul_pow, mul_pow]
    ring
  rw [h2, splitElem_mul_one_sub_pow hu hfg, zero_mul]

/-- The idempotent is divisible by `xⁿ`, the factorisation dual to `one_sub_splitIdem`. -/
theorem splitIdem_eq_mul (hu : IsUnit (f + g)) (n : ℕ) :
    splitIdem hu n = splitElem hu ^ n *
      ∑ i ∈ Finset.range n, (1 - splitElem hu ^ n) ^ i := by
  have h := one_sub_pow_eq (1 - splitElem hu ^ n) n
  rw [sub_sub_cancel] at h
  rw [splitIdem, h]

/-- **`gⁿ` annihilates `ε`**, the mirror of `pow_mul_one_sub_splitIdem`. -/
theorem pow_mul_splitIdem (hu : IsUnit (f + g)) {n : ℕ} (hfg : (f * g) ^ n = 0) :
    g ^ n * splitIdem hu n = 0 := by
  have h1 : ((1 - splitElem hu) * ↑hu.unit) ^ n = g ^ n := by rw [mul_one_sub_splitElem]
  have h2 : g ^ n * splitIdem hu n =
      (splitElem hu * (1 - splitElem hu)) ^ n *
        (↑hu.unit ^ n * ∑ i ∈ Finset.range n, (1 - splitElem hu ^ n) ^ i) := by
    rw [← h1, splitIdem_eq_mul, mul_pow, mul_pow]
    ring
  rw [h2, splitElem_mul_one_sub_pow hu hfg, zero_mul]

/-! ### The two corners -/

/-- **`f` is a unit in the corner `T ⧸ (1 - ε)`.** There `(1 - xⁿ)ⁿ = 0`, so `1 - xⁿ` is nilpotent,
so `xⁿ` is a unit, so `x` is (using `n ≠ 0`), so `f = x · u` is. -/
theorem isUnit_mk_left (hu : IsUnit (f + g)) {n : ℕ} (hn : n ≠ 0) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {1 - splitIdem hu n}) f) := by
  have hz : (Ideal.Quotient.mk (Ideal.span {1 - splitIdem hu n}))
      ((1 - splitElem hu ^ n) ^ n) = 0 := by
    rw [← one_sub_splitIdem]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hnil : IsNilpotent (Ideal.Quotient.mk (Ideal.span {1 - splitIdem hu n})
      (1 - splitElem hu ^ n)) := ⟨n, by rw [← map_pow]; exact hz⟩
  have hxu : IsUnit (Ideal.Quotient.mk (Ideal.span {1 - splitIdem hu n})
      (splitElem hu ^ n)) := by
    have := IsNilpotent.isUnit_one_sub hnil
    rwa [map_sub, map_one, sub_sub_cancel] at this
  rw [map_pow] at hxu
  have hx := (isUnit_pow_iff hn).mp hxu
  have hfeq : (Ideal.Quotient.mk (Ideal.span {1 - splitIdem hu n})) f =
      Ideal.Quotient.mk (Ideal.span {1 - splitIdem hu n}) (splitElem hu) *
        Ideal.Quotient.mk (Ideal.span {1 - splitIdem hu n}) (↑hu.unit) := by
    rw [← map_mul, mul_splitElem]
  rw [hfeq]
  exact hx.mul (hu.unit.isUnit.map _)

/-- **`g` is a unit in the corner `T ⧸ (ε)`.** There `(1 - xⁿ)ⁿ = 1`, so `1 - xⁿ` is a unit, so its
factor `1 - x` is, so `g = (1 - x) · u` is. -/
theorem isUnit_mk_right (hu : IsUnit (f + g)) {n : ℕ} (hn : n ≠ 0) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {splitIdem hu n}) g) := by
  have hz : (Ideal.Quotient.mk (Ideal.span {splitIdem hu n})) (splitIdem hu n) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hone : (Ideal.Quotient.mk (Ideal.span {splitIdem hu n}))
      ((1 - splitElem hu ^ n) ^ n) = 1 := by
    have h := congrArg (Ideal.Quotient.mk (Ideal.span {splitIdem hu n})) (one_sub_splitIdem hu n)
    rw [map_sub, map_one, hz, sub_zero] at h
    exact h.symm
  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {splitIdem hu n})
      (1 - splitElem hu ^ n)) := by
    rw [← isUnit_pow_iff hn, ← map_pow]
    exact hone ▸ isUnit_one
  have hfac : IsUnit (Ideal.Quotient.mk (Ideal.span {splitIdem hu n}) (1 - splitElem hu)) := by
    have h := one_sub_pow_eq (splitElem hu) n
    rw [h, map_mul] at hunit
    exact isUnit_of_mul_isUnit_left hunit
  have hgeq : (Ideal.Quotient.mk (Ideal.span {splitIdem hu n})) g =
      Ideal.Quotient.mk (Ideal.span {splitIdem hu n}) (1 - splitElem hu) *
        Ideal.Quotient.mk (Ideal.span {splitIdem hu n}) (↑hu.unit) := by
    rw [← map_mul, mul_one_sub_splitElem]
  rw [hgeq]
  exact hfac.mul (hu.unit.isUnit.map _)

/-! ### The two corners are the two localizations -/

/-- **The corner `T ⧸ (1 - ε)` is the localization `T_f`.** The three localization axioms: `f` is a
unit there (`isUnit_mk_left`); the quotient map is surjective, which gives the `surj` axiom with
denominator `1`; and if `a` and `b` agree in the quotient then `a - b ∈ (1 - ε)`, so `fⁿ` kills the
difference by `pow_mul_one_sub_splitIdem`. -/
theorem isLocalization_away_left (hu : IsUnit (f + g)) {n : ℕ} (hn : n ≠ 0)
    (hfg : (f * g) ^ n = 0) :
    IsLocalization.Away f (T ⧸ Ideal.span {1 - splitIdem hu n}) := by
  rw [IsLocalization.Away, isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, k, rfl⟩
    rw [Ideal.Quotient.algebraMap_eq, map_pow]
    exact (isUnit_mk_left hu hn).pow k
  · intro z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨⟨a, 1⟩, by simp⟩
  · intro a b h
    refine ⟨⟨f ^ n, n, rfl⟩, ?_⟩
    rw [Ideal.Quotient.algebraMap_eq] at h
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp h)
    have hab : a - b = c * (1 - splitIdem hu n) := hc.symm
    have hz : f ^ n * a - f ^ n * b = c * (f ^ n * (1 - splitIdem hu n)) := by
      calc f ^ n * a - f ^ n * b = f ^ n * (a - b) := by ring
        _ = f ^ n * (c * (1 - splitIdem hu n)) := by rw [hab]
        _ = c * (f ^ n * (1 - splitIdem hu n)) := by ring
    rw [pow_mul_one_sub_splitIdem hu hfg, mul_zero, sub_eq_zero] at hz
    exact hz

/-- **The corner `T ⧸ (ε)` is the localization `T_g`**, the mirror of
`isLocalization_away_left`. -/
theorem isLocalization_away_right (hu : IsUnit (f + g)) {n : ℕ} (hn : n ≠ 0)
    (hfg : (f * g) ^ n = 0) :
    IsLocalization.Away g (T ⧸ Ideal.span {splitIdem hu n}) := by
  rw [IsLocalization.Away, isLocalization_iff]
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, k, rfl⟩
    rw [Ideal.Quotient.algebraMap_eq, map_pow]
    exact (isUnit_mk_right hu hn).pow k
  · intro z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨⟨a, 1⟩, by simp⟩
  · intro a b h
    refine ⟨⟨g ^ n, n, rfl⟩, ?_⟩
    rw [Ideal.Quotient.algebraMap_eq] at h
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp h)
    have hab : a - b = c * splitIdem hu n := hc.symm
    have hz : g ^ n * a - g ^ n * b = c * (g ^ n * splitIdem hu n) := by
      calc g ^ n * a - g ^ n * b = g ^ n * (a - b) := by ring
        _ = g ^ n * (c * splitIdem hu n) := by rw [hab]
        _ = c * (g ^ n * splitIdem hu n) := by ring
    rw [pow_mul_splitIdem hu hfg, mul_zero, sub_eq_zero] at hz
    exact hz

/-! ### The splitting -/

variable (R : Type u) [CommRing R] [Algebra R T]

/-- The idempotent decomposition `T ≃ₐ[R] T ⧸ (1 - ε) × T ⧸ (ε)`. -/
noncomputable def splitQuotEquiv (hu : IsUnit (f + g)) {n : ℕ} (hfg : (f * g) ^ n = 0) :
    T ≃ₐ[R] (T ⧸ Ideal.span {1 - splitIdem hu n}) × (T ⧸ Ideal.span {splitIdem hu n}) :=
  AlgEquiv.prodQuotientOfIsIdempotentElem R (splitIdem_isIdempotentElem hu hfg).one_sub
    (splitIdem_isIdempotentElem hu hfg) (by ring)
    (by rw [sub_mul, one_mul, (splitIdem_isIdempotentElem hu hfg).eq, sub_self])

/-- **The splitting** `T ≃ₐ[R] T_f × T_g`, for `f + g` a unit and `(f · g)ⁿ = 0` with `n ≠ 0`:
compose the idempotent decomposition with the identification of each corner with a localization. -/
noncomputable def awaySplitEquiv (hu : IsUnit (f + g)) {n : ℕ} (hn : n ≠ 0)
    (hfg : (f * g) ^ n = 0) :
    T ≃ₐ[R] Localization.Away f × Localization.Away g :=
  letI := isLocalization_away_left hu hn hfg
  letI := isLocalization_away_right hu hn hfg
  (splitQuotEquiv R hu hfg).trans
    (AlgEquiv.prodCongr
      ((IsLocalization.algEquiv (Submonoid.powers f) (T ⧸ Ideal.span {1 - splitIdem hu n})
        (Localization.Away f)).restrictScalars R)
      ((IsLocalization.algEquiv (Submonoid.powers g) (T ⧸ Ideal.span {splitIdem hu n})
        (Localization.Away g)).restrictScalars R))

/-- **The splitting**, stated with `IsNilpotent (f · g)` instead of an explicit exponent. The
exponent is taken to be `k + 1` for a witness `k`, so that the `n ≠ 0` hypothesis is automatic. -/
noncomputable def awaySplitEquivOfIsNilpotent (hu : IsUnit (f + g))
    (hfg : IsNilpotent (f * g)) :
    T ≃ₐ[R] Localization.Away f × Localization.Away g :=
  awaySplitEquiv R hu (Nat.succ_ne_zero hfg.choose)
    (by rw [pow_succ, hfg.choose_spec, zero_mul])

end RingSplit

end
