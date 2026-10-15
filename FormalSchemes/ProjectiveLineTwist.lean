/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.TwoCech
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.Polynomial.Basic

/-!
# Čech cohomology of the twisting sheaves on the projective line

The projective line `ℙ¹_A` over a commutative ring `A` is covered by the two affine lines
`D₊(x₀) = Spec A[X]` and `D₊(x₁) = Spec A[Y]`, with intersection `Spec A[T, T⁻¹]`, where
`X ↦ T` and `Y ↦ T⁻¹`. The twisting sheaf `𝒪(d)` is free of rank one on each chart, glued on the
overlap by multiplication by `T^d`. Its ordered Čech complex for this covering is therefore
`A[X] × A[Y] → A[T, T⁻¹]`, `(p, q) ↦ p(T) - T^d q(T⁻¹)`
(`ProjectiveLine.res0`, `ProjectiveLine.resInf`, and `TwoCech.d`).

This file computes its cohomology: this is Serre's computation of the cohomology of `𝒪(d)` on
`ℙ¹_A` (Stacks, Lemma 30.8.1, Tag 01XT, for `n = 1`):

* `ProjectiveLine.H0_eq_bot`: `H⁰(𝒪(d)) = 0` for `d < 0`;
* `ProjectiveLine.H0EquivDegreeLT`: `H⁰(𝒪(e)) ≃ A[X]_{≤ e}`, free of rank `e + 1`, for `e ≥ 0`;
* `ProjectiveLine.mem_range_d_iff`: a Laurent polynomial is a Čech coboundary iff its
  coefficients in degrees strictly between `d` and `0` vanish;
* `ProjectiveLine.H1_subsingleton`: `H¹(𝒪(d)) = 0` for `d ≥ -1`;
* `ProjectiveLine.H1Equiv`: `H¹(𝒪(-e-2)) ≃ A^(e+1)`, via the coefficients of `T⁻¹, …, T^(-e-1)`.

These are the inputs of Serre's finiteness and vanishing theorems on `ℙ¹_A`, on which the
projective case of the Grothendieck existence theorem rests (Stacks, Lemma 30.24.3, Tag 0885).
-/

universe u

open Polynomial LaurentPolynomial

namespace ProjectiveLine

variable (A : Type u) [CommRing A]

lemma coeff_toLaurent (p : A[X]) (n : ℤ) :
    (toLaurent p).coeff n = if 0 ≤ n then p.coeff n.toNat else 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hp, hq, coeff_add]
    split_ifs <;> simp
  | monomial k a =>
    rw [← C_mul_X_pow_eq_monomial, toLaurent_C_mul_X_pow, ← single_eq_C_mul_T,
      AddMonoidAlgebra.coeff_single, Finsupp.single_apply, coeff_C_mul_X_pow]
    by_cases hn : 0 ≤ n
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      simp [Int.toNat_natCast, eq_comm]
    · have : (k : ℤ) ≠ n := by omega
      simp [this, hn]

/-- The restriction from the chart `Spec A[X]` to the overlap: `p ↦ p(T)`. -/
noncomputable def res0 : A[X] →ₗ[A] A[T;T⁻¹] := (toLaurentAlg (R := A)).toLinearMap

/-- The restriction from the chart `Spec A[Y]` to the overlap, twisted by the transition function
`T^d` of `𝒪(d)`: `q ↦ T^d q(T⁻¹)`. -/
noncomputable def resInf (d : ℤ) : A[X] →ₗ[A] A[T;T⁻¹] :=
  LinearMap.mulLeft A (T d) ∘ₗ (invert.toLinearMap ∘ₗ (toLaurentAlg (R := A)).toLinearMap)

lemma coeff_res0 (p : A[X]) (n : ℤ) :
    (res0 A p).coeff n = if 0 ≤ n then p.coeff n.toNat else 0 :=
  coeff_toLaurent A p n

lemma coeff_resInf (d : ℤ) (q : A[X]) (n : ℤ) :
    (resInf A d q).coeff n = if n ≤ d then q.coeff (d - n).toNat else 0 := by
  simp only [resInf, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply,
    AlgEquiv.toLinearMap_apply, AlgHom.toLinearMap_apply, coe_toLaurentAlg, T]
  rw [AddMonoidAlgebra.coeff_single_mul_apply, one_mul, invert_apply, coeff_toLaurent]
  congr 1
  · exact propext (by omega)
  · congr 2; omega

/-- `H⁰(ℙ¹_A, 𝒪(d))`, as the Čech `H⁰` of the standard covering. -/
noncomputable abbrev H0 (d : ℤ) : Submodule A (A[X] × A[X]) := TwoCech.H0 (res0 A) (resInf A d)

/-- `H¹(ℙ¹_A, 𝒪(d))`, as the Čech `H¹` of the standard covering. -/
noncomputable abbrev H1 (d : ℤ) : Type u := TwoCech.H1 (res0 A) (resInf A d)

variable {A}

lemma mem_H0_iff {d : ℤ} {p q : A[X]} :
    (p, q) ∈ H0 A d ↔ ∀ n : ℤ, (if 0 ≤ n then p.coeff n.toNat else 0) =
      if n ≤ d then q.coeff (d - n).toNat else 0 := by
  rw [TwoCech.mem_H0, LaurentPolynomial.ext_iff]
  simp only [coeff_res0, coeff_resInf]

/-- `H⁰(𝒪(d)) = 0` for `d < 0`. -/
theorem H0_eq_bot {d : ℤ} (hd : d < 0) : H0 A d = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨p, q⟩ h
  rw [mem_H0_iff] at h
  rw [Submodule.mem_bot, Prod.mk_eq_zero]
  constructor
  · ext k
    have := h k
    simp only [Nat.cast_nonneg, if_true, Int.toNat_natCast] at this
    rw [this, if_neg (by omega), coeff_zero]
  · ext k
    have := h (d - k)
    rw [if_neg (by omega), if_pos (by omega)] at this
    simpa using this.symm

/-! ### `H⁰(𝒪(e))` for `e ≥ 0` -/

lemma fst_mem_degreeLT {e : ℕ} {x : A[X] × A[X]} (hx : x ∈ H0 A e) :
    x.1 ∈ degreeLT A (e + 1) := by
  obtain ⟨p, q⟩ := x
  rw [mem_H0_iff] at hx
  rw [mem_degreeLT, degree_lt_iff_coeff_zero]
  intro m hm
  have := hx m
  rw [if_pos (by omega), if_neg (by omega), Int.toNat_natCast] at this
  exact this

lemma snd_eq_reflect {e : ℕ} {x : A[X] × A[X]} (hx : x ∈ H0 A e) : x.2 = reflect e x.1 := by
  have hdeg := fst_mem_degreeLT hx
  obtain ⟨p, q⟩ := x
  rw [mem_H0_iff] at hx
  rw [mem_degreeLT, degree_lt_iff_coeff_zero] at hdeg
  ext k
  rw [coeff_reflect]
  by_cases hk : k ≤ e
  · rw [revAt_le hk]
    have := hx ((e : ℤ) - k)
    rw [if_pos (by omega), if_pos (by omega)] at this
    convert this.symm using 2 <;> omega
  · rw [revAt, Function.Embedding.coeFn_mk, if_neg hk]
    have := hx ((e : ℤ) - k)
    rw [if_neg (by omega), if_pos (by omega)] at this
    rw [hdeg k (by omega)]
    convert this.symm using 2
    omega

lemma reflect_mem_H0 {e : ℕ} {p : A[X]} (hp : p ∈ degreeLT A (e + 1)) :
    (p, reflect e p) ∈ H0 A e := by
  rw [mem_degreeLT, degree_lt_iff_coeff_zero] at hp
  rw [mem_H0_iff]
  intro n
  by_cases h0 : 0 ≤ n
  · rw [if_pos h0]
    by_cases he : n ≤ e
    · rw [if_pos he, coeff_reflect, revAt_le (by omega)]
      congr 1
      omega
    · rw [if_neg he]
      exact hp _ (by omega)
  · rw [if_neg h0, if_pos (by omega), coeff_reflect, revAt, Function.Embedding.coeFn_mk,
      if_neg (by omega)]
    exact (hp _ (by omega)).symm

/-- `H⁰(ℙ¹_A, 𝒪(e)) ≃ A[X]_{< e + 1}` for `e ≥ 0`: a global section is a polynomial of degree at
most `e` on the first chart, and its reflection on the second. -/
noncomputable def H0EquivDegreeLT (e : ℕ) : H0 A e ≃ₗ[A] degreeLT A (e + 1) where
  toFun x := ⟨x.1.1, fst_mem_degreeLT x.2⟩
  invFun p := ⟨(p.1, reflect e p.1), reflect_mem_H0 p.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := Subtype.ext (Prod.ext rfl (snd_eq_reflect x.2).symm)
  right_inv _ := rfl

/-- `H⁰(ℙ¹_A, 𝒪(e))` is free of rank `e + 1` for `e ≥ 0` (Stacks, Lemma 30.8.1, Tag 01XT). -/
noncomputable def H0Equiv (e : ℕ) : H0 A e ≃ₗ[A] (Fin (e + 1) → A) :=
  (H0EquivDegreeLT e).trans (degreeLTEquiv A (e + 1))

/-! ### `H¹(𝒪(d))` -/

variable (A) in
lemma coeff_trunc (f : A[T;T⁻¹]) (k : ℕ) : (trunc f).coeff k = f.coeff k := by
  induction f using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    rw [map_add, coeff_add, hp, hq, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
  | C_mul_T n a =>
    rw [trunc_C_mul_T, ← single_eq_C_mul_T, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    split_ifs with h1 h2 h2
    · rw [coeff_monomial, if_pos (by omega)]
    · rw [coeff_monomial, if_neg (by omega)]
    · rw [coeff_zero]; omega
    · rw [coeff_zero]

/-- A Laurent polynomial is a Čech coboundary for `𝒪(d)` iff its coefficients in the degrees
strictly between `d` and `0` vanish. -/
theorem mem_range_d_iff {d : ℤ} {r : A[T;T⁻¹]} :
    r ∈ LinearMap.range (TwoCech.d (res0 A) (resInf A d)) ↔
      ∀ n : ℤ, d < n → n < 0 → r.coeff n = 0 := by
  constructor
  · rintro ⟨⟨p, q⟩, rfl⟩ n h1 h2
    rw [TwoCech.d_apply, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, coeff_res0, coeff_resInf,
      if_neg (by omega), if_neg (by omega), sub_zero]
  · intro h
    let rneg := r - toLaurent (trunc r)
    refine ⟨(trunc r, -trunc (invert (T (-d) * rneg))), ?_⟩
    ext n
    have hneg (m : ℤ) : rneg.coeff m = r.coeff m - if 0 ≤ m then r.coeff m else 0 := by
      simp only [rneg, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, coeff_toLaurent]
      split_ifs with hm
      · rw [coeff_trunc, Int.toNat_of_nonneg hm]
      · rfl
    rw [TwoCech.d_apply, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, coeff_res0, coeff_resInf]
    simp only [coeff_neg]
    split_ifs with h0 hd
    · rw [coeff_trunc, Int.toNat_of_nonneg h0, coeff_trunc, invert_apply, T,
        AddMonoidAlgebra.coeff_single_mul_apply, one_mul, hneg, if_pos (by omega)]
      simp only [Int.toNat_of_nonneg (by omega : 0 ≤ d - n)]
      rw [show -(-d) + -(d - n) = n by omega]
      simp
    · rw [coeff_trunc, Int.toNat_of_nonneg h0]
      simp
    · rw [coeff_trunc, invert_apply, T, AddMonoidAlgebra.coeff_single_mul_apply, one_mul, hneg]
      simp only [Int.toNat_of_nonneg (by omega : 0 ≤ d - n)]
      rw [show -(-d) + -(d - n) = n by omega, if_neg h0]
      simp
    · rw [h n (by omega) (by omega)]
      simp

/-- `H¹(ℙ¹_A, 𝒪(d)) = 0` for `d ≥ -1` (Stacks, Lemma 30.8.1, Tag 01XT). -/
theorem H1_subsingleton {d : ℤ} (hd : -1 ≤ d) : Subsingleton (H1 A d) := by
  rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
  intro r _
  exact mem_range_d_iff.mpr fun n h1 h2 ↦ absurd h1 (by omega)

variable (A) in
/-- The coefficients of `T⁻¹, …, T^(-e-1)`: the gap between the two charts' contributions. -/
noncomputable def gapCoeff (e : ℕ) : A[T;T⁻¹] →ₗ[A] (Fin (e + 1) → A) where
  toFun r i := r.coeff (-((i : ℤ) + 1))
  map_add' _ _ := by ext; simp [AddMonoidAlgebra.coeff_add]
  map_smul' _ _ := by ext; simp [AddMonoidAlgebra.coeff_smul]

lemma ker_gapCoeff (e : ℕ) :
    LinearMap.ker (gapCoeff A e) = LinearMap.range (TwoCech.d (res0 A) (resInf A (-(e + 2)))) := by
  ext r
  rw [mem_range_d_iff, LinearMap.mem_ker]
  constructor
  · intro h n h1 h2
    have := congrFun h ⟨(-n - 1).toNat, by omega⟩
    change r.coeff (-((((-n - 1).toNat : ℕ) : ℤ) + 1)) = 0 at this
    rwa [show -((((-n - 1).toNat : ℕ) : ℤ) + 1) = n by omega] at this
  · intro h
    ext i
    exact h _ (by omega) (by omega)

lemma gapCoeff_surjective (e : ℕ) : Function.Surjective (gapCoeff A e) := by
  intro v
  refine ⟨∑ i : Fin (e + 1), AddMonoidAlgebra.single (-((i : ℤ) + 1)) (v i), ?_⟩
  ext j
  change (∑ i : Fin (e + 1), AddMonoidAlgebra.single (-((i : ℤ) + 1)) (v i)).coeff _ = _
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single j]
  · rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_pos rfl]
  · intro i _ hij
    rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, if_neg]
    intro h
    exact hij (Fin.ext (by omega))
  · simp

/-- `H¹(ℙ¹_A, 𝒪(-e-2)) ≃ A^(e+1)` (Stacks, Lemma 30.8.1, Tag 01XT): the class of a Laurent
polynomial is determined by its coefficients of `T⁻¹, …, T^(-e-1)`. -/
noncomputable def H1Equiv (e : ℕ) : H1 A (-(e + 2)) ≃ₗ[A] (Fin (e + 1) → A) :=
  (Submodule.quotEquivOfEq _ _ (ker_gapCoeff e).symm).trans
    ((gapCoeff A e).quotKerEquivOfSurjective (gapCoeff_surjective e))

end ProjectiveLine
