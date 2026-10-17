/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Nakayama

/-!
# Every point of `ℙ¹_A` specializes into the special fibre

Let `I ⊆ A` be an ideal contained in the Jacobson radical (e.g. `A` is `I`-adically complete).
`ℙ¹_A` is covered by `U₀ = Spec A[X]` and `U₁ = Spec A[Y]`, glued along
`Spec A[T, T⁻¹]` via `X ↦ T` (`Polynomial.toLaurent`) and `Y ↦ T⁻¹`
(`ProjectiveLine.toLaurentInv`). Since `ℙ¹_A → Spec A` is closed, every point of `ℙ¹_A`
specializes to a point of the special fibre `V(I)`. On the chart `U₀` this says: a prime `p` of
`A[X]` with `p + I·A[X] = A[X]` (no specialization inside `U₀` meets `V(I)`) does not contain `X`,
and the corresponding prime of `A[Y]` is contained in a prime containing `I·A[Y]`
(`ProjectiveLine.exists_prime_le_comap_toLaurentInv`).

The proof is elementary (no properness machinery): from `1 - g ∈ p` with `g ∈ I[X]`, the
reversed polynomial of `1 - g` has unit leading coefficient `1 - g(0)` and lies in the prime of
`A[Y]`; hence `A[Y]` modulo that prime is a finite `A`-module, and Nakayama's lemma
(Stacks, Lemma 10.20.1, Tag 00DV) shows that `I` generates a proper ideal in it.
-/

universe u

open Polynomial
open scoped LaurentPolynomial
open LaurentPolynomial (T invert)

namespace ProjectiveLine

variable {A : Type u} [CommRing A]

/-- The coordinate ring map of the second chart, `A[Y] → A[T, T⁻¹]`, `Y ↦ T⁻¹`. -/
noncomputable def toLaurentInv : A[X] →+* A[T;T⁻¹] :=
  (invert : A[T;T⁻¹] ≃ₐ[A] A[T;T⁻¹]).toRingEquiv.toRingHom.comp toLaurent

lemma toLaurentInv_apply (q : A[X]) : toLaurentInv q = invert (toLaurent q) := rfl

lemma toLaurentInv_reverse (q : A[X]) :
    toLaurentInv q.reverse = toLaurent q * T (-(q.natDegree : ℤ)) := by
  rw [toLaurentInv_apply, LaurentPolynomial.toLaurent_reverse, map_mul,
    LaurentPolynomial.invert_T]
  congr 1
  exact (invert (R := A)).apply_symm_apply _

variable (I : Ideal A)

lemma exists_mem_one_sub_mem (p : Ideal A[X]) (h : I.map C ⊔ p = ⊤) :
    ∃ g ∈ I.map C, 1 - g ∈ p := by
  have : (1 : A[X]) ∈ I.map C ⊔ p := h ▸ Submodule.mem_top
  obtain ⟨g, hg, q, hq, hgq⟩ := Submodule.mem_sup.1 this
  exact ⟨g, hg, by rw [← hgq, add_sub_cancel_left]; exact hq⟩

variable {I}

lemma isUnit_one_sub_coeff_zero (hI : I ≤ Ideal.jacobson ⊥) {g : A[X]} (hg : g ∈ I.map C) :
    IsUnit (1 - g.coeff 0) := by
  have h := Ideal.mem_jacobson_bot.1 (hI (Ideal.mem_map_C_iff.1 hg 0)) (-1)
  rwa [mul_neg_one, neg_add_eq_sub] at h

/-- A prime of `A[X]` not specializing into `V(I)` inside `U₀` does not contain `X`. -/
theorem X_notMem_of_sup_eq_top (hI : I ≤ Ideal.jacobson ⊥) (p : Ideal A[X]) [hp : p.IsPrime]
    (h : I.map C ⊔ p = ⊤) : (X : A[X]) ∉ p := by
  intro hX
  obtain ⟨g, hg, hgp⟩ := exists_mem_one_sub_mem I p h
  obtain ⟨q, hq⟩ := X_dvd_sub_C (p := g)
  have h1 : C (1 - g.coeff 0) ∈ p := by
    have : C (1 - g.coeff 0) = (1 - g) + X * q := by rw [← hq, map_sub, map_one]; ring
    rw [this]
    exact p.add_mem hgp (p.mul_mem_right q hX)
  exact hp.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 ((isUnit_one_sub_coeff_zero hI hg).map C))

/-- **Every point of `U₀` specializes into the special fibre of `ℙ¹_A`**: if a prime `p` of
`A[X]` satisfies `p + I·A[X] = A[X]`, then `X ∉ p`, and the prime of `A[Y]` corresponding to `p`
(the preimage of `p·A[T, T⁻¹]` under `Y ↦ T⁻¹`) lies in a prime containing `I·A[Y]`. -/
theorem exists_prime_le_comap_toLaurentInv (hI : I ≤ Ideal.jacobson ⊥) (p : Ideal A[X])
    [hp : p.IsPrime] (h : I.map C ⊔ p = ⊤) :
    ∃ q : Ideal A[X], q.IsPrime ∧
      (p.map (algebraMap A[X] A[T;T⁻¹])).comap toLaurentInv ≤ q ∧ I.map C ≤ q := by
  have hX := X_notMem_of_sup_eq_top hI p h
  have hdisj : Disjoint (Submonoid.powers (X : A[X]) : Set A[X]) p := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hX (hp.mem_of_pow_mem n hn)
  set P := p.map (algebraMap A[X] A[T;T⁻¹])
  haveI hP : P.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (X : A[X])) _ p hp hdisj
  set p₁ := P.comap (toLaurentInv (A := A))
  haveI : p₁.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨g, hg, hgp⟩ := exists_mem_one_sub_mem I p h
  have hu := isUnit_one_sub_coeff_zero hI hg
  haveI : Nontrivial A := by
    have : Nontrivial A[X] := ⟨⟨0, 1, fun h01 ↦ hp.ne_top (by
      rw [Ideal.eq_top_iff_one, ← h01]; exact p.zero_mem)⟩⟩
    exact Polynomial.nontrivial_iff.1 this
  set f := 1 - g
  have hf0 : f.coeff 0 = 1 - g.coeff 0 := by simp [f]
  -- the reversed polynomial lies in `p₁` and has unit leading coefficient
  have hrev : f.reverse ∈ p₁ := by
    change toLaurentInv f.reverse ∈ P
    rw [toLaurentInv_reverse]
    exact P.mul_mem_right _ (Ideal.mem_map_of_mem _ hgp)
  have hlead : f.reverse.leadingCoeff = 1 - g.coeff 0 := by
    rw [reverse_leadingCoeff, trailingCoeff, ← hf0]
    congr
    rw [natTrailingDegree_eq_zero]
    exact Or.inr (hf0 ▸ hu.ne_zero)
  set m := C (↑hu.unit⁻¹ : A) * f.reverse
  have hm : m.Monic := monic_C_mul_of_mul_leadingCoeff_eq_one (by
    rw [hlead]; exact hu.unit.inv_mul)
  have hmp : Ideal.span {m} ≤ p₁ := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact p₁.mul_mem_left _ hrev
  -- `A[Y] / p₁` is a finite `A`-module
  haveI := hm.finite_quotient
  haveI : Module.Finite A (A[X] ⧸ p₁) :=
    Module.Finite.of_surjective (Ideal.Quotient.factorₐ A hmp).toLinearMap
      (Ideal.Quotient.factor_surjective hmp)
  have hne : I.map C ⊔ p₁ ≠ ⊤ := by
    intro htop
    have hmap : I.map (algebraMap A (A[X] ⧸ p₁)) = ⊤ := by
      have e : algebraMap A (A[X] ⧸ p₁) = (Ideal.Quotient.mk p₁).comp C := rfl
      rw [e, ← Ideal.map_map]
      have := congrArg (Ideal.map (Ideal.Quotient.mk p₁)) htop
      rwa [Ideal.map_sup, Ideal.map_quotient_self, sup_bot_eq, Ideal.map_top] at this
    have htop' : (⊤ : Submodule A (A[X] ⧸ p₁)) ≤ I • ⊤ := by
      rw [Ideal.smul_top_eq_map, hmap]
      exact le_refl _
    have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot I ⊤
      (Module.Finite.fg_top) htop' hI
    have h1 : (1 : A[X] ⧸ p₁) = 0 := by
      have : (1 : A[X] ⧸ p₁) ∈ (⊤ : Submodule A (A[X] ⧸ p₁)) := Submodule.mem_top
      rw [hbot] at this
      exact this
    rw [← map_one (Ideal.Quotient.mk p₁), Ideal.Quotient.eq_zero_iff_mem] at h1
    exact Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one _).2 h1)
  obtain ⟨q, hqmax, hq⟩ := Ideal.exists_le_maximal _ hne
  exact ⟨q, hqmax.isPrime, le_sup_right.trans hq, le_sup_left.trans hq⟩

/-- The prime `p·A[T, T⁻¹]` lies over `p` (for `X ∉ p`). -/
lemma comap_map_toLaurent (p : Ideal A[X]) [hp : p.IsPrime] (hX : (X : A[X]) ∉ p) :
    (p.map (algebraMap A[X] A[T;T⁻¹])).comap (algebraMap A[X] A[T;T⁻¹]) = p := by
  have hdisj : Disjoint (Submonoid.powers (X : A[X]) : Set A[X]) p := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hX (hp.mem_of_pow_mem n hn)
  exact IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers (X : A[X])) _ hp hdisj

lemma isPrime_map_toLaurent (p : Ideal A[X]) [hp : p.IsPrime] (hX : (X : A[X]) ∉ p) :
    (p.map (algebraMap A[X] A[T;T⁻¹])).IsPrime := by
  have hdisj : Disjoint (Submonoid.powers (X : A[X]) : Set A[X]) p := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, rfl⟩ hn
    exact hX (hp.mem_of_pow_mem n hn)
  exact IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers (X : A[X])) _ p hp hdisj

end ProjectiveLine
