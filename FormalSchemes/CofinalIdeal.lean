import FormalSchemes.IdealsOfDefinition
import FormalSchemes.LargestIdealOfDefinition
import Mathlib.RingTheory.Finiteness.Ideal

set_option linter.style.header false

/-!
# Cofinal ideals: the equivalence relation behind "same adic topology"

Two ideals `I`, `J` of a commutative ring `R` are **cofinal** when some power of each is contained
in the other. This is the exact sense in which an ideal of definition of an adic ring is
non-unique: `IsAdic.exists_pow_le` (`FormalSchemes.IdealsOfDefinition`) says any two ideals of
definition of one topological ring are cofinal, and `Ideal.IsCofinal.isAdic` below is the converse.

This file gives that relation a name, proves it is an equivalence relation, and records the two
bridges the rest of the tree needs — to the adic topology, and to the radical.

## Why a named relation rather than the two containments

The relation was already in use, unnamed, in at least four places: `AdicCompletion.cofinalHom`
(`FormalSchemes.CofinalCompletion`), `FormalSpectrum.generalCofinalSpfIso`
(`FormalSchemes.CofinalSheafComparisonGeneral`), `IsAdic.of_le_of_pow_le`
(`FormalSchemes.LargestIdealOfDefinition`) and `IsAdic.radical_eq`. Each carried the two exponents
as separate hypotheses, which is fine for a single lemma and unworkable for a *transport*: the
consumer of this file, `FormalSchemes.CofinalTopFiniteType`, composes the relation with itself and
with `Ideal.map`, and the exponents are different at every step.

The two directions are deliberately kept as bare existentials rather than as a chosen pair of
exponents. Nothing downstream needs the exponents to be canonical, and `AdicCompletion.cofinalHom`
already shows that the map they induce does not depend on them up to the resulting isomorphism.

## Main definitions and results

* `Ideal.IsCofinal`: some power of each ideal is contained in the other.
* `Ideal.IsCofinal.refl`, `Ideal.IsCofinal.symm`, `Ideal.IsCofinal.trans`: it is an equivalence
  relation, packaged as `Ideal.isCofinal_equivalence`.
* `Ideal.IsCofinal.pow`: `I` is cofinal with `I ^ n` for `n ≠ 0` — the standard example, and the
  one that makes the relation non-trivial.
* `Ideal.IsCofinal.map`: cofinality is preserved by extension along a ring homomorphism.
* `Ideal.IsCofinal.isAdic` and `IsAdic.isCofinal`: **the topological bridge.** For ideals of one
  topological ring, cofinality is exactly the statement that both are ideals of definition.
* `Ideal.IsCofinal.radical_eq` and `Ideal.IsCofinal.of_radical_eq`: **the geometric bridge.**
  Cofinal ideals have the same radical, and for finitely generated ideals the converse holds. This
  is what turns a statement about the underlying space of a formal spectrum back into a statement
  about ideals.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.5.
* [The Stacks Project, Tag 0AHZ](https://stacks.math.columbia.edu/tag/0AHZ).
-/

namespace Ideal

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] {I J K : Ideal R}

/-- Two ideals are **cofinal** if some power of each is contained in the other. Equivalently — see
`Ideal.IsCofinal.isAdic` and `IsAdic.isCofinal` — they induce the same adic topology.

The name follows the tree's existing usage (`AdicCompletion.cofinalHom`,
`FormalSpectrum.generalCofinalSpfIso`): the two filtrations `I ^ n` and `J ^ n` are cofinal in one
another as descending families of ideals. -/
def IsCofinal (I J : Ideal R) : Prop :=
  (∃ m : ℕ, I ^ m ≤ J) ∧ ∃ n : ℕ, J ^ n ≤ I

namespace IsCofinal

theorem exists_pow_le (h : IsCofinal I J) : ∃ m : ℕ, I ^ m ≤ J := h.1

theorem exists_pow_le' (h : IsCofinal I J) : ∃ n : ℕ, J ^ n ≤ I := h.2

/-- A cofinality witness can always be taken with a *positive* exponent, since the powers of an
ideal are decreasing. Several proofs need this: `Ideal.radical_pow` and `is_ideal_adic_pow` both
refuse the exponent `0`, where `I ^ 0 = ⊤`. -/
theorem exists_pow_succ_le (h : IsCofinal I J) : ∃ m : ℕ, I ^ (m + 1) ≤ J := by
  obtain ⟨m, hm⟩ := h.1
  exact ⟨m, (Ideal.pow_le_pow_right (Nat.le_succ m)).trans hm⟩

@[refl]
theorem refl (I : Ideal R) : IsCofinal I I :=
  ⟨⟨1, (pow_one I).le⟩, ⟨1, (pow_one I).le⟩⟩

theorem rfl : IsCofinal I I := .refl I

@[symm]
theorem symm (h : IsCofinal I J) : IsCofinal J I := ⟨h.2, h.1⟩

theorem comm : IsCofinal I J ↔ IsCofinal J I := ⟨.symm, .symm⟩

/-- Transitivity, by multiplying the exponents: `I ^ (m * p) = (I ^ m) ^ p ≤ J ^ p ≤ K`. -/
@[trans]
theorem trans (h₁ : IsCofinal I J) (h₂ : IsCofinal J K) : IsCofinal I K := by
  obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ := h₁
  obtain ⟨⟨p, hp⟩, ⟨q, hq⟩⟩ := h₂
  refine ⟨⟨m * p, ?_⟩, ⟨q * n, ?_⟩⟩
  · rw [pow_mul]
    exact (Ideal.pow_right_mono hm p).trans hp
  · rw [pow_mul]
    exact (Ideal.pow_right_mono hq n).trans hn

/-- Two nested ideals with a power of the larger inside the smaller are cofinal. -/
theorem of_le_of_pow_le (hle : I ≤ J) {n : ℕ} (hn : J ^ n ≤ I) : IsCofinal I J :=
  ⟨⟨1, by rwa [pow_one]⟩, ⟨n, hn⟩⟩

/-- **The standard example**: `I` is cofinal with each of its positive powers. This is the reason
the relation is not equality, and the counterexample that makes the naive "an isomorphism of formal
spectra identifies the ideals of definition" false — see `FormalSchemes.TopFiniteTypeHomComp`. -/
theorem pow (I : Ideal R) {n : ℕ} (hn : n ≠ 0) : IsCofinal I (I ^ n) :=
  ⟨⟨n, le_rfl⟩, ⟨1, by rw [pow_one]; exact Ideal.pow_le_self hn⟩⟩

/-- Cofinality is preserved by extension along a ring homomorphism, because `Ideal.map` commutes
with powers and is monotone. -/
theorem map (f : R →+* S) (h : IsCofinal I J) : IsCofinal (I.map f) (J.map f) := by
  obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ := h
  refine ⟨⟨m, ?_⟩, ⟨n, ?_⟩⟩
  · rw [← Ideal.map_pow]
    exact Ideal.map_mono hm
  · rw [← Ideal.map_pow]
    exact Ideal.map_mono hn

end IsCofinal

theorem isCofinal_equivalence : Equivalence (IsCofinal (R := R)) :=
  ⟨IsCofinal.refl, IsCofinal.symm, IsCofinal.trans⟩

/-! ### The topological bridge -/

/-- **Cofinal ideals define the same adic topology.** If the topology of `R` is the `I`-adic one
and `J` is cofinal with `I`, then it is also the `J`-adic one.

Neither `I ≤ J` nor `J ≤ I` is assumed, so `IsAdic.of_le_of_pow_le`
(`FormalSchemes.LargestIdealOfDefinition`) does not apply directly. The proof interpolates through
the product `I * J`, which lies below both — the same device as
`FormalSpectrum.generalCofinalSpfIso` (`FormalSchemes.CofinalSheafComparisonGeneral`). -/
theorem IsCofinal.isAdic [TopologicalSpace R] (h : IsCofinal I J) (hI : IsAdic I) : IsAdic J := by
  haveI : IsTopologicalRing R := hI.isTopologicalRing
  obtain ⟨m, hm⟩ := h.exists_pow_succ_le
  obtain ⟨n, hn⟩ := h.symm.exists_pow_succ_le
  -- `I * J` sits below both `I` and `J`, and a power of `I` sits inside it.
  have hKI : (I * J : Ideal R) ≤ I := Ideal.mul_le_right
  have hKJ : (I * J : Ideal R) ≤ J := Ideal.mul_le_left
  have hIK : I ^ (m + 2) ≤ I * J := by
    rw [pow_succ']
    exact Ideal.mul_mono le_rfl hm
  -- so `I * J` is an ideal of definition …
  have hK : IsAdic (I * J) :=
    IsAdic.of_le_of_pow_le (is_ideal_adic_pow hI (Nat.succ_pos (m + 1))) hIK
      (Ideal.pow_right_mono hKI (m + 2))
  -- … and then so is `J`, since a power of `J` sits inside `I * J` too.
  refine IsAdic.of_le_of_pow_le hK hKJ (n := n + 2) ?_
  rw [pow_succ]
  exact Ideal.mul_mono hn le_rfl

/-- **Any two ideals of definition of a topological ring are cofinal.** The converse of
`Ideal.IsCofinal.isAdic`, and a repackaging of `IsAdic.exists_pow_le`. -/
theorem _root_.IsAdic.isCofinal [TopologicalSpace R] (hI : IsAdic I) (hJ : IsAdic J) :
    IsCofinal I J :=
  ⟨hJ.exists_pow_le hI, hI.exists_pow_le hJ⟩

/-! ### The geometric bridge -/

/-- **Cofinal ideals have the same radical**, so they cut out the same closed subset of
`Spec R`. -/
theorem IsCofinal.radical_eq (h : IsCofinal I J) : I.radical = J.radical := by
  have key : ∀ {A B : Ideal R}, IsCofinal A B → A.radical ≤ B.radical := by
    intro A B hAB
    obtain ⟨m, hm⟩ := hAB.exists_pow_succ_le
    calc A.radical = (A ^ (m + 1)).radical := (Ideal.radical_pow A (Nat.succ_ne_zero m)).symm
      _ ≤ B.radical := Ideal.radical_mono hm
  exact le_antisymm (key h) (key (IsCofinal.symm h))

/-- **The converse, for finitely generated ideals**: two finitely generated ideals with the same
radical are cofinal. `Ideal.exists_pow_le_of_le_radical_of_fg` is what upgrades the containment
`I ≤ J.radical` to a containment of a *power* of `I` in `J`, and it is exactly where finite
generation is used.

This is the direction a geometric input produces: an isomorphism of formal spectra sees only the
closed subsets `V (I)` and `V (J)`, hence only the radicals. -/
theorem IsCofinal.of_radical_eq (hI : I.FG) (hJ : J.FG) (h : I.radical = J.radical) :
    IsCofinal I J :=
  ⟨Ideal.exists_pow_le_of_le_radical_of_fg (h ▸ Ideal.le_radical) hI,
    Ideal.exists_pow_le_of_le_radical_of_fg (h ▸ Ideal.le_radical) hJ⟩

end Ideal
