import FormalSchemes.TateInvSeparatingBot
import FormalSchemes.TateInvSeparatingKerClosed
import Mathlib.RingTheory.PowerSeries.Ideal

set_option linter.style.header false

/-!
# Division by `x·y − q`, and the separation property over a Noetherian base

`FormalSchemes.TateInvGlobalNormalForm` proves `Γ (T_inv/⟨σ⟩) ≃+* R` from one hypothesis,
`AlgebraicGeometry.IsTateInvCoordSeparating`. `FormalSchemes.TateInvSeparatingKerClosed` shows
that hypothesis *implies* adic closedness of the presentation kernel of `A = R{x, y}/(x·y − q)`,
and `FormalSchemes.TateInvSeparatingBot` discharges it for the discrete family `I = ⊥`, `q = 0`.
**This file proves the converse of the first and, with it, the hypothesis itself over every
Noetherian base.**

## Main results

* `AlgebraicGeometry.isTateInvCoordSeparating_of_adicKerClosed`: **adic closedness of the
  presentation kernel implies separation.** Together with
  `AlgebraicGeometry.adicKerClosed_of_isTateInvCoordSeparating` this is
  `AlgebraicGeometry.isTateInvCoordSeparating_iff_adicKerClosed`, an equivalence: the separation
  property *is* adic closedness of `(x·y − q)`, no more and no less.
* `AlgebraicGeometry.isTateInvCoordSeparating_of_noetherian`: **the separation property holds
  over every Noetherian base**, with no further hypothesis — not `q ∈ I`, not a topology on `R`.
  Over a Noetherian `R` the polydisc `R{x, y}` is Noetherian
  (`RestrictedPowerSeries.instIsNoetherianRing`), so `RingHom.adicKerClosed_of_noetherian` applies.
* `AlgebraicGeometry.tateInvGlobalSubring_eq_range_of_noetherian`,
  `AlgebraicGeometry.tateInvGlobalSubringEquivBaseOfNoetherian` and
  **`AlgebraicGeometry.tateInvPeriodQuotientGlobalSectionsEquivBaseOfNoetherian`**: the three
  consumers of the hypothesis, restated without it. The last is
  `Γ (T_inv/⟨σ⟩, ⊤) ≃+* R`, and it carries no hypothesis its conditional form did not already
  carry: `[TopologicalSpace R]`, `[IsAdicRing I]`, `[IsNoetherianRing R]`, `q ∈ I`, `I.FG`.
* `AlgebraicGeometry.exists_algebraMap_eq_of_mem_tateInvChartAnnulusSubring_univ`: **issue 1223's
  goal 3, in the negative.** Every element of the chart ring at `S = Set.univ` comes from the
  base, so there is no element of it outside the image of `Γ (Spf R, ·)`. This is distinct from
  properness, the opposite inclusion, which `FormalSchemes.TateInvGlobalProperness` settles.
* `AlgebraicGeometry.isTateInvCoordSeparating_powerSeriesInt` and
  `AlgebraicGeometry.tateInvPeriodQuotientGlobalSectionsEquivPowerSeriesInt`: **non-vacuity at a
  base with `q ≠ 0`** — `R = ℤ⟦X⟧`, `I = (X)`, `q = X`, the universal Tate base. The witness of
  `FormalSchemes.TateInvSeparatingBot` has `I = ⊥` and `q = 0`; this one does not.

## The route, and how it differs from the one that was planned

The plan recorded on issue 1274 was a coefficient API for the two-variable polydisc plus a
division of `R{x, y}` by `x·y − q` inside the completion. The first half exists
(`FormalSchemes.RestrictedPowerSeriesCoeff`, `FormalSchemes.TateAnnulusCoeff`). **This file uses
neither**, and imports neither: no declaration below mentions
`RestrictedPowerSeries.coeff` or `AlgebraicGeometry.coeff_annulusRel_mul`. The division that is
actually needed is on the **polynomial** ring, and it is elementary there.

Write `M d = min (d 0) (d 1)` (`AlgebraicGeometry.tateExpDiag`) and let
`AlgebraicGeometry.tateExpRed d` be `d` with `(M d, M d)` subtracted — a `Finsupp.single` on one
of the two axes. Then

```
xᵃyᵇ − qᴹ · x^(a−M) y^(b−M) = x^(a−M) y^(b−M) · ((x·y)ᴹ − qᴹ)
```

is divisible by `x·y − q` (`sub_dvd_pow_sub_pow`). Summing over the support of a polynomial `p`
gives `AlgebraicGeometry.tateRem`, the **remainder**, supported on the two axes, with

```
p − tateRem q p ∈ (x·y − q)
```

(`AlgebraicGeometry.sub_tateRem_mem`). The remainder's coefficient on the `x`-axis in degree `n`
is the diagonal sum `Σⱼ coeff (n+j, j) p · qʲ`, which is exactly the `n`-th Laurent coefficient of
the image of `p` under `(x, y) ↦ (X, q·X⁻¹)`; the `y`-axis is the same statement for
`(x, y) ↦ (q·X⁻¹, X)`. That is
`AlgebraicGeometry.coeff_tateRem_single_zero` and `AlgebraicGeometry.coeff_tateRem_single_one`,
and both are proved termwise on the support, with no induction and no infinite sum.

The passage to the completion is then the standard one and does **not** need a division there.
Given `w ∈ R{x, y}` killed by both coordinate maps, approximate it by a polynomial `p` modulo the
`m`-th step of the filtration; both images of `p` are then small, so by the two lemmas above every
coefficient of `tateRem q p` lies in `I ^ m`, so `tateRem q p ∈ I ^ m · R[x, y]`, so

```
w  ≡  (an element of (x·y − q))   mod  (I·R{x, y}) ^ m
```

for every `m` (`AlgebraicGeometry.exists_ker_sub_mem_pow`). Adic closedness of the kernel converts
that into `w ∈ (x·y − q)`. **The infinite sum `Σⱼ c_{n+j,j} qʲ` that issue 1274 warns about never
appears**: at each level `m` the polynomial `p` makes it finite, and the levels are only ever
compared through the closedness hypothesis.

## What is *not* proved

**Nothing about a non-Noetherian base.**
`AlgebraicGeometry.isTateInvCoordSeparating_iff_adicKerClosed` says exactly how much is missing:
the separation property over a base where `Ideal.span {x·y − q}` is not adically closed in
`R{x, y}` is **false**, and over one where it is closed it is true. No
such base is constructed here, so it is not known whether the headline is false anywhere; the
equivalence merely shows that the question is entirely about closedness.

**No division inside the completion.** `AlgebraicGeometry.tateRem` is a polynomial construction.
Nothing below writes an element of `R{x, y}` in the joint kernel as `(x·y − q) · v` for an
explicit `v`; that element is produced by the closedness hypothesis, not exhibited.

**No converse to `AlgebraicGeometry.coeff_annulusRel_mul`.** `FormalSchemes.TateAnnulusCoeff`
records that converse as the open question its recursion poses. It is still open; this file
reaches the same conclusion by a different route rather than by answering it.

**Nothing at a general `S`.**
`AlgebraicGeometry.exists_algebraMap_eq_of_mem_tateInvChartAnnulusSubring_univ`
is stated at `S = Set.univ` only; `tateInvChartAnnulusSubring_empty_eq_top` shows there is no
`S`-free answer.

## References

* [Deligne–Rapoport, *Les schémas de modules de courbes elliptiques*], II.1 — the Néron `n`-gon.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.3, §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. 0, §7.5.
-/

noncomputable section

open MvPolynomial

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R]

/-! ### Reducing a two-variable exponent modulo the diagonal -/

/-- The number of times the diagonal exponent `(1, 1)` divides `d`. -/
def tateExpDiag (d : Fin 2 →₀ ℕ) : ℕ := min (d 0) (d 1)

/-- The reduction of `d` modulo the diagonal. -/
def tateExpRed (d : Fin 2 →₀ ℕ) : Fin 2 →₀ ℕ :=
  if d 1 ≤ d 0 then Finsupp.single 0 (d 0 - d 1) else Finsupp.single 1 (d 1 - d 0)

theorem tateExpRed_apply_zero (d : Fin 2 →₀ ℕ) : tateExpRed d 0 = d 0 - tateExpDiag d := by
  unfold tateExpRed tateExpDiag
  split <;> simp <;> omega

theorem tateExpRed_apply_one (d : Fin 2 →₀ ℕ) : tateExpRed d 1 = d 1 - tateExpDiag d := by
  unfold tateExpRed tateExpDiag
  split <;> simp <;> omega

theorem tateExpRed_eq_single_zero_iff {d : Fin 2 →₀ ℕ} {n : ℕ} :
    tateExpRed d = Finsupp.single 0 n ↔ (n : ℤ) = (d 0 : ℤ) - (d 1 : ℤ) := by
  rw [finTwo_eq_single_zero_iff, tateExpRed_apply_zero, tateExpRed_apply_one]
  unfold tateExpDiag
  omega

theorem tateExpRed_eq_single_one_iff {d : Fin 2 →₀ ℕ} {n : ℕ} :
    tateExpRed d = Finsupp.single 1 n ↔ (n : ℤ) = (d 1 : ℤ) - (d 0 : ℤ) := by
  rw [finTwo_eq_single_one_iff, tateExpRed_apply_zero, tateExpRed_apply_one]
  unfold tateExpDiag
  omega

theorem tateExpRed_apply_eq_zero_or (d : Fin 2 →₀ ℕ) :
    tateExpRed d 0 = 0 ∨ tateExpRed d 1 = 0 := by
  rw [tateExpRed_apply_zero, tateExpRed_apply_one]
  unfold tateExpDiag
  omega

/-! ### The remainder of division by `x·y − q` -/

section Division

variable (q : R)

/-- **A monomial differs from its reduction by a multiple of `x·y − q`.** -/
theorem monomial_sub_monomial_tateExpRed_mem (d : Fin 2 →₀ ℕ) (c : R) :
    (monomial d c : MvPolynomial (Fin 2) R) -
        monomial (tateExpRed d) (c * q ^ tateExpDiag d) ∈
      Ideal.span {(X 0 * X 1 - C q : MvPolynomial (Fin 2) R)} := by
  have e0 : (X 0 : MvPolynomial (Fin 2) R) ^ d 0 =
      X 0 ^ (d 0 - tateExpDiag d) * X 0 ^ tateExpDiag d := by
    rw [← pow_add]; congr 1; unfold tateExpDiag; omega
  have e1 : (X 1 : MvPolynomial (Fin 2) R) ^ d 1 =
      X 1 ^ (d 1 - tateExpDiag d) * X 1 ^ tateExpDiag d := by
    rw [← pow_add]; congr 1; unfold tateExpDiag; omega
  have hd : (monomial d c : MvPolynomial (Fin 2) R) =
      C c * (X 0 ^ (d 0 - tateExpDiag d) * X 1 ^ (d 1 - tateExpDiag d)) *
        (X 0 * X 1) ^ tateExpDiag d := by
    rw [monomial_finTwo_eq, e0, e1, mul_pow]; ring
  have hred : (monomial (tateExpRed d) (c * q ^ tateExpDiag d) : MvPolynomial (Fin 2) R) =
      C c * (X 0 ^ (d 0 - tateExpDiag d) * X 1 ^ (d 1 - tateExpDiag d)) *
        C q ^ tateExpDiag d := by
    rw [monomial_finTwo_eq, tateExpRed_apply_zero, tateExpRed_apply_one, map_mul, map_pow]
    ring
  rw [hd, hred, ← mul_sub]
  exact Ideal.mem_span_singleton.mpr ((sub_dvd_pow_sub_pow _ _ _).mul_left _)

/-- **The remainder of `p` on division by `x·y − q`.** -/
def tateRem (p : MvPolynomial (Fin 2) R) : MvPolynomial (Fin 2) R :=
  ∑ d ∈ p.support, monomial (tateExpRed d) (MvPolynomial.coeff d p * q ^ tateExpDiag d)

/-- The remainder may be summed over any superset of the support. -/
theorem tateRem_eq_sum (p : MvPolynomial (Fin 2) R) {s : Finset (Fin 2 →₀ ℕ)}
    (hs : p.support ⊆ s) :
    tateRem q p =
      ∑ d ∈ s, monomial (tateExpRed d) (MvPolynomial.coeff d p * q ^ tateExpDiag d) :=
  Finset.sum_subset hs fun d _ hd => by
    rw [MvPolynomial.notMem_support_iff.mp hd, zero_mul, map_zero]

/-- **The remainder is additive.** -/
theorem tateRem_add (p₁ p₂ : MvPolynomial (Fin 2) R) :
    tateRem q (p₁ + p₂) = tateRem q p₁ + tateRem q p₂ := by
  classical
  rw [tateRem_eq_sum q (p₁ + p₂) (MvPolynomial.support_add.trans (le_refl _)),
    tateRem_eq_sum q p₁ Finset.subset_union_left,
    tateRem_eq_sum q p₂ Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.coeff_add, add_mul, ← map_add]

/-- **The remainder of a monomial** is the monomial at the reduced exponent, with the missing
diagonal factors replaced by powers of `q`. -/
theorem tateRem_monomial (d : Fin 2 →₀ ℕ) (c : R) :
    tateRem q (monomial d c) = monomial (tateExpRed d) (c * q ^ tateExpDiag d) := by
  classical
  rw [tateRem, MvPolynomial.support_monomial]
  by_cases hc : c = 0
  · rw [if_pos hc, Finset.sum_empty, hc, zero_mul, map_zero]
  · rw [if_neg hc, Finset.sum_singleton, MvPolynomial.coeff_monomial, if_pos rfl]

/-- **The remainder really is a remainder.** -/
theorem sub_tateRem_mem (p : MvPolynomial (Fin 2) R) :
    p - tateRem q p ∈ Ideal.span {(X 0 * X 1 - C q : MvPolynomial (Fin 2) R)} := by
  have h : p - tateRem q p =
      ∑ d ∈ p.support, ((monomial d (MvPolynomial.coeff d p) : MvPolynomial (Fin 2) R) -
        monomial (tateExpRed d) (MvPolynomial.coeff d p * q ^ tateExpDiag d)) := by
    rw [Finset.sum_sub_distrib, ← MvPolynomial.as_sum]
    rfl
  rw [h]
  exact Ideal.sum_mem _ fun d _ => monomial_sub_monomial_tateExpRed_mem q d _

/-- Only the two axes carry a coefficient of the remainder. -/
theorem coeff_tateRem_eq_zero (p : MvPolynomial (Fin 2) R) {e : Fin 2 →₀ ℕ}
    (h0 : e 0 ≠ 0) (h1 : e 1 ≠ 0) : MvPolynomial.coeff e (tateRem q p) = 0 := by
  rw [tateRem, MvPolynomial.coeff_sum]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [MvPolynomial.coeff_monomial, if_neg]
  rintro rfl
  rcases tateExpRed_apply_eq_zero_or d with h | h
  · exact h0 h
  · exact h1 h

/-! ### The remainder's coefficients are the coefficients of the two `Ĝm` images -/

section Complete

variable {I : Ideal R} [IsAdicComplete I R]

/-- **The `xⁿ`-coefficient of the remainder is the `n`-th coefficient of the image under
`(x, y) ↦ (X, q·X⁻¹)`.** -/
theorem coeff_tateRem_single_zero (p : MvPolynomial (Fin 2) R) (n : ℕ) :
    MvPolynomial.coeff (Finsupp.single 0 n) (tateRem q p) =
      RestrictedLaurentSeries.coeff I (n : ℤ) (aeval (tateInvCoordPoint R I q) p) := by
  have hp : (aeval (tateInvCoordPoint R I q) p : RestrictedLaurentSeries R I) =
      ∑ d ∈ p.support,
        aeval (tateInvCoordPoint R I q) (monomial d (MvPolynomial.coeff d p)) := by
    rw [← map_sum, ← MvPolynomial.as_sum]
  rw [tateRem, MvPolynomial.coeff_sum, hp, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.coeff_monomial, aeval_monomial_tateInvCoordPoint,
    RestrictedLaurentSeries.coeff_algebraMap_mul, RestrictedLaurentSeries.coeff_X]
  by_cases h : (n : ℤ) = (d 0 : ℤ) - (d 1 : ℤ)
  · rw [if_pos (tateExpRed_eq_single_zero_iff.mpr h), if_pos h, mul_one,
      show tateExpDiag d = d 1 from by unfold tateExpDiag; omega]
  · rw [if_neg fun hh => h (tateExpRed_eq_single_zero_iff.mp hh), if_neg h, mul_zero]

/-- **The `yⁿ`-coefficient of the remainder is the `n`-th coefficient of the image under
`(x, y) ↦ (q·X⁻¹, X)`.** -/
theorem coeff_tateRem_single_one (p : MvPolynomial (Fin 2) R) (n : ℕ) :
    MvPolynomial.coeff (Finsupp.single 1 n) (tateRem q p) =
      RestrictedLaurentSeries.coeff I (n : ℤ) (aeval (tateInvCoordPointFlip R I q) p) := by
  have hp : (aeval (tateInvCoordPointFlip R I q) p : RestrictedLaurentSeries R I) =
      ∑ d ∈ p.support,
        aeval (tateInvCoordPointFlip R I q) (monomial d (MvPolynomial.coeff d p)) := by
    rw [← map_sum, ← MvPolynomial.as_sum]
  rw [tateRem, MvPolynomial.coeff_sum, hp, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.coeff_monomial, aeval_monomial_tateInvCoordPointFlip,
    RestrictedLaurentSeries.coeff_algebraMap_mul, RestrictedLaurentSeries.coeff_X]
  by_cases h : (n : ℤ) = (d 1 : ℤ) - (d 0 : ℤ)
  · rw [if_pos (tateExpRed_eq_single_one_iff.mpr h), if_pos h, mul_one,
      show tateExpDiag d = d 0 from by unfold tateExpDiag; omega]
  · rw [if_neg fun hh => h (tateExpRed_eq_single_one_iff.mp hh), if_neg h, mul_zero]

/-! ### Division modulo an ideal of the base -/

/-- **If every coefficient of the remainder lies in `K`, the remainder does.** -/
theorem tateRem_mem_map_C (K : Ideal R) (p : MvPolynomial (Fin 2) R)
    (h0 : ∀ n : ℕ, MvPolynomial.coeff (Finsupp.single 0 n) (tateRem q p) ∈ K)
    (h1 : ∀ n : ℕ, MvPolynomial.coeff (Finsupp.single 1 n) (tateRem q p) ∈ K) :
    tateRem q p ∈ Ideal.map (C : R →+* MvPolynomial (Fin 2) R) K := by
  refine MvPolynomial.mem_map_C_iff.mpr fun e => ?_
  by_cases he0 : e 0 = 0
  · have h := h1 (e 1)
    rwa [← (finTwo_eq_single_one_iff.mpr ⟨rfl, he0⟩ : e = Finsupp.single 1 (e 1))] at h
  by_cases he1 : e 1 = 0
  · have h := h0 (e 0)
    rwa [← (finTwo_eq_single_zero_iff.mpr ⟨rfl, he1⟩ : e = Finsupp.single 0 (e 0))] at h
  rw [coeff_tateRem_eq_zero q p he0 he1]
  exact K.zero_mem

/-! ### The separation property -/

omit [IsAdicComplete I R] in
/-- The image of the polynomial Tate relation in the polydisc is `annulusRel`. -/
theorem algebraMap_X_mul_X_sub_C :
    algebraMap (MvPolynomial (Fin 2) R) (annulusRing R I) (X 0 * X 1 - C q) =
      annulusRel R I q := by
  rw [map_sub, map_mul, RestrictedPowerSeries.algebraMap_MvPolynomial_apply,
    RestrictedPowerSeries.algebraMap_MvPolynomial_apply,
    RestrictedPowerSeries.algebraMap_MvPolynomial_apply,
    RestrictedPowerSeries.of_C_eq_algebraMap]

/-- **The division step.** -/
theorem exists_ker_sub_mem_pow (hI : I.FG) {w : annulusRing R I}
    (hφ : tateInvGlobalCoord R I q hI (annulusMk R I q w) = 0)
    (hψ : tateInvGlobalCoord R I q hI ((annulusFlip R I q hI).symm (annulusMk R I q w)) = 0)
    (m : ℕ) :
    ∃ k ∈ RingHom.ker (annulusMk R I q).toRingHom,
      w - k ∈ (RestrictedPowerSeries.idealOfDefinition R I 2) ^ m := by
  obtain ⟨p, hp⟩ := RestrictedPowerSeries.exists_sub_mem_idealOfDefinition_pow I 2 hI m w
  have hφp : ∀ n : ℤ,
      RestrictedLaurentSeries.coeff I n (aeval (tateInvCoordPoint R I q) p) ∈ I ^ m := by
    intro n
    have himg : tateInvGlobalCoord R I q hI (annulusMk R I q
          (w - algebraMap (MvPolynomial (Fin 2) R) (annulusRing R I) p)) =
        - aeval (tateInvCoordPoint R I q) p := by
      rw [map_sub, map_sub, hφ, tateInvGlobalCoord_annulusMk_algebraMap, zero_sub]
    have hmem := RestrictedLaurentSeries.coeff_mem_pow I hI n m
      ((RestrictedLaurentSeries.mem_idealOfDefinition_pow_iff R I m _).mp
        (tateInvGlobalCoord_annulusMk_mem_pow R I q hI m hp))
    rw [himg, map_neg] at hmem
    exact neg_mem_iff.mp hmem
  have hψp : ∀ n : ℤ,
      RestrictedLaurentSeries.coeff I n (aeval (tateInvCoordPointFlip R I q) p) ∈ I ^ m := by
    intro n
    have himg : tateInvGlobalCoord R I q hI ((annulusFlip R I q hI).symm (annulusMk R I q
          (w - algebraMap (MvPolynomial (Fin 2) R) (annulusRing R I) p))) =
        - aeval (tateInvCoordPointFlip R I q) p := by
      rw [map_sub, map_sub, map_sub, hψ,
        tateInvGlobalCoord_annulusFlip_symm_annulusMk_algebraMap, zero_sub]
    have hmem := RestrictedLaurentSeries.coeff_mem_pow I hI n m
      ((RestrictedLaurentSeries.mem_idealOfDefinition_pow_iff R I m _).mp
        (tateInvGlobalCoord_annulusFlip_symm_annulusMk_mem_pow R I q hI m hp))
    rw [himg, map_neg] at hmem
    exact neg_mem_iff.mp hmem
  have hrem : tateRem q p ∈ Ideal.map (C : R →+* MvPolynomial (Fin 2) R) (I ^ m) :=
    tateRem_mem_map_C q (I ^ m) p
      (fun n => by rw [coeff_tateRem_single_zero (I := I)]; exact hφp n)
      (fun n => by rw [coeff_tateRem_single_one (I := I)]; exact hψp n)
  refine ⟨algebraMap (MvPolynomial (Fin 2) R) (annulusRing R I) (p - tateRem q p), ?_, ?_⟩
  · obtain ⟨g, hg⟩ := Ideal.mem_span_singleton.mp (sub_tateRem_mem q p)
    have hrel : annulusMk R I q (annulusRel R I q) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    rw [RingHom.mem_ker, hg, map_mul, algebraMap_X_mul_X_sub_C]
    change annulusMk R I q _ = 0
    rw [map_mul, hrel, zero_mul]
  · have hcomp : (algebraMap (MvPolynomial (Fin 2) R) (RestrictedPowerSeries R I 2)).comp
        (C : R →+* MvPolynomial (Fin 2) R) = algebraMap R (RestrictedPowerSeries R I 2) :=
      RingHom.ext fun r => by
        rw [RingHom.comp_apply, RestrictedPowerSeries.algebraMap_MvPolynomial_apply,
          RestrictedPowerSeries.of_C_eq_algebraMap]
    have hmap := Ideal.mem_map_of_mem
      (algebraMap (MvPolynomial (Fin 2) R) (RestrictedPowerSeries R I 2)) hrem
    rw [Ideal.map_map, hcomp, Ideal.map_pow,
      ← RestrictedPowerSeries.idealOfDefinition_eq_map] at hmap
    have heq : w - algebraMap (MvPolynomial (Fin 2) R) (annulusRing R I) (p - tateRem q p) =
        (w - algebraMap (MvPolynomial (Fin 2) R) (annulusRing R I) p) +
          algebraMap (MvPolynomial (Fin 2) R) (annulusRing R I) (tateRem q p) := by
      rw [map_sub]; ring
    rw [heq]
    exact Ideal.add_mem _ hp hmap

/-- **The separation property holds whenever the presentation kernel is adically closed.** -/
theorem isTateInvCoordSeparating_of_adicKerClosed (hI : I.FG)
    (hker : (annulusMk R I q).toRingHom.AdicKerClosed
      (RestrictedPowerSeries.idealOfDefinition R I 2)) :
    IsTateInvCoordSeparating R I q hI := by
  intro a hφ hψ
  obtain ⟨w, rfl⟩ := annulusMk_surjective R I q a
  exact RingHom.mem_ker.mp (hker w (exists_ker_sub_mem_pow q hI hφ hψ))

/-! ### The Noetherian case, and the equivalence with adic closedness -/

omit [IsAdicComplete I R] in
/-- **Over a Noetherian base the presentation kernel is adically closed.** -/
theorem adicKerClosed_annulusMk_of_noetherian [IsNoetherianRing R] (hI : I.FG) :
    (annulusMk R I q).toRingHom.AdicKerClosed
      (RestrictedPowerSeries.idealOfDefinition R I 2) := by
  letI : Algebra (annulusRing R I) (annulusAlgebra R I q) := (annulusMk R I q).toRingHom.toAlgebra
  haveI : IsAdicComplete (RestrictedPowerSeries.idealOfDefinition R I 2) (annulusRing R I) :=
    (RestrictedPowerSeries.isAdicRing R I 2 hI).toIsAdicComplete
  exact RingHom.adicKerClosed_of_noetherian
    (RestrictedPowerSeries.idealOfDefinition R I 2) (annulusMk_surjective R I q)

/-- **The separation property holds over every Noetherian base.** -/
theorem isTateInvCoordSeparating_of_noetherian [IsNoetherianRing R] (hI : I.FG) :
    IsTateInvCoordSeparating R I q hI :=
  isTateInvCoordSeparating_of_adicKerClosed q hI (adicKerClosed_annulusMk_of_noetherian q hI)

/-- **Separation is exactly adic closedness of the presentation kernel.** -/
theorem isTateInvCoordSeparating_iff_adicKerClosed (hI : I.FG) :
    IsTateInvCoordSeparating R I q hI ↔
      (annulusMk R I q).toRingHom.AdicKerClosed
        (RestrictedPowerSeries.idealOfDefinition R I 2) :=
  ⟨adicKerClosed_of_isTateInvCoordSeparating hI, isTateInvCoordSeparating_of_adicKerClosed q hI⟩

end Complete

end Division

/-! ### The consumers, with the hypothesis discharged -/

section Consumers

variable {I : Ideal R} {q : R} [IsAdicComplete I R] [IsNoetherianRing R]

/-- **`Γ (T_inv/⟨σ⟩)` is exactly the image of the base**, over a Noetherian base. -/
theorem tateInvGlobalSubring_eq_range_of_noetherian (hq : q ∈ I) (hI : I.FG) :
    tateInvGlobalSubring (R := R) (I := I) (q := q) hI =
      (algebraMap R (annulusAlgebra R I q)).range :=
  tateInvGlobalSubring_eq_range hq hI (isTateInvCoordSeparating_of_noetherian q hI)

/-- **`Γ (T_inv/⟨σ⟩) ≃+* R`**, over a Noetherian base. -/
def tateInvGlobalSubringEquivBaseOfNoetherian (hq : q ∈ I) (hI : I.FG) :
    tateInvGlobalSubring (R := R) (I := I) (q := q) hI ≃+* R :=
  tateInvGlobalSubringEquivBase hq hI (isTateInvCoordSeparating_of_noetherian q hI)

end Consumers

section SectionsConsumer

open CategoryTheory TopologicalSpace

variable {I : Ideal R} {q : R}
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R]

/-- **`Γ (T_inv/⟨σ⟩, ⊤) ≃+* R`, with no hypothesis left.** -/
def tateInvPeriodQuotientGlobalSectionsEquivBaseOfNoetherian (hq : q ∈ I) (hI : I.FG) :
    ((actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj
      (Opposite.op (⊤ : Opens (actionQuotient
        (tateInvPeriodAction R I q hq hI)).toTopCat))) ≃+* R :=
  haveI _hc : IsAdicComplete I R := ‹IsAdicRing I›.toIsAdicComplete
  tateInvPeriodQuotientGlobalSectionsEquivBase hq hI (isTateInvCoordSeparating_of_noetherian q hI)

end SectionsConsumer

/-! ### The chart ring at `S = Set.univ` is exactly the base -/

section Chart

open CategoryTheory TopologicalSpace Opposite

variable {I : Ideal R} {q : R}
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R]
variable [IsAdicRing (annulusIdealOfDefinition R I q)]
variable [IsAdicRing (FormalSpectrum.awayCompletionIdeal (annulusIdealOfDefinition R I q)
  (overlapX R I q))]
variable [IsAdicRing (FormalSpectrum.awayCompletionIdeal (annulusIdealOfDefinition R I q)
  (overlapY R I q))]

/-- **Every element of the chart ring at `S = Set.univ` comes from the base.** -/
theorem exists_algebraMap_eq_of_mem_tateInvChartAnnulusSubring_univ (hq : q ∈ I) (hI : I.FG)
    {s : (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
      (op (tateInvPatchSaturateOpens (R := R) (I := I) (q := q) (S := Set.univ) hq hI
        isOpen_univ))}
    (hs : s ∈ tateInvChartAnnulusSubring (hq := hq) (hI := hI) (S := Set.univ) isOpen_univ) :
    ∃ r : R, (tateInvGlobalPatchEquiv hq hI).symm (algebraMap R (annulusAlgebra R I q) r) = s := by
  haveI _hc : IsAdicComplete I R := ‹IsAdicRing I›.toIsAdicComplete
  have h := (mem_tateInvChartAnnulusSubring_iff_mem_tateInvGlobalSubring hq hI s).mp hs
  rw [tateInvGlobalSubring_eq_range_of_noetherian hq hI] at h
  obtain ⟨r, hr⟩ := h
  exact ⟨r, by rw [hr, RingEquiv.symm_apply_apply]⟩

end Chart

/-! ### Non-vacuity at a base with `q ≠ 0` -/

section NonVacuous

open CategoryTheory TopologicalSpace

/-- **The separation property at the universal Tate base** `R = ℤ⟦X⟧`, `I = (X)`, `q = X`. Here
`q ≠ 0` and `I ≠ ⊥`, so this is not the discrete family of
`AlgebraicGeometry.isTateInvCoordSeparating_bot`. -/
theorem isTateInvCoordSeparating_powerSeriesInt :
    IsTateInvCoordSeparating (PowerSeries ℤ) (Ideal.span {(PowerSeries.X : PowerSeries ℤ)})
      PowerSeries.X (Submodule.fg_span_singleton _) :=
  isTateInvCoordSeparating_of_noetherian _ (Submodule.fg_span_singleton _)

/-- **`Γ (T_inv/⟨σ⟩, ⊤) ≃+* ℤ⟦X⟧` at the universal Tate base**, with the `X`-adic topology on
`ℤ⟦X⟧` supplied by the `letI`. This is the headline at a base with `q ≠ 0`. -/
noncomputable def tateInvPeriodQuotientGlobalSectionsEquivPowerSeriesInt :
    letI : TopologicalSpace (PowerSeries ℤ) :=
      (Ideal.span {(PowerSeries.X : PowerSeries ℤ)}).adicTopology
    haveI : IsAdicRing (Ideal.span {(PowerSeries.X : PowerSeries ℤ)}) := ⟨rfl⟩
    ((actionQuotient (tateInvPeriodAction (PowerSeries ℤ)
        (Ideal.span {(PowerSeries.X : PowerSeries ℤ)}) PowerSeries.X
        (Ideal.mem_span_singleton_self _) (Submodule.fg_span_singleton _))).presheaf.obj
      (Opposite.op (⊤ : Opens (actionQuotient (tateInvPeriodAction (PowerSeries ℤ)
        (Ideal.span {(PowerSeries.X : PowerSeries ℤ)}) PowerSeries.X
        (Ideal.mem_span_singleton_self _)
        (Submodule.fg_span_singleton _))).toTopCat))) ≃+* PowerSeries ℤ :=
  letI : TopologicalSpace (PowerSeries ℤ) :=
    (Ideal.span {(PowerSeries.X : PowerSeries ℤ)}).adicTopology
  haveI : IsAdicRing (Ideal.span {(PowerSeries.X : PowerSeries ℤ)}) := ⟨rfl⟩
  tateInvPeriodQuotientGlobalSectionsEquivBaseOfNoetherian
    (Ideal.mem_span_singleton_self _) (Submodule.fg_span_singleton _)

end NonVacuous

end AlgebraicGeometry
