import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Spectrum.Prime.Basic

set_option linter.style.header false

/-!
# The standing two-patch witness: `𝔸¹_ℚ` doubled along `D(X)`, completed at `1`

Every witness section in the two-patch completion cluster — `CompletionTwoPatchRange.lean`,
`CompletionTwoPatchSupport.lean`, `CompletionTwoPatchClosed.lean` — exhibits the *same* geometry:
`𝔸¹_ℚ` glued to itself along `D(X)`, completed along the point `1` on each chart. This file holds
the scaffolding those sections share, so that a reader can see at a glance that the three
statements are about one and the same example.

The ideal completed along is `(X − 1)`, the two points that come up are the origin `(X)` and the
centre `(X − 1)` of the completion, and the one fact that needs proving is that the origin does
**not** lie on `V(X − 1)`. Note `X ∉ (X − 1)`, so the overlap `D(X) ∩ V(X − 1)` is nonempty: this
is the nondegenerate case, in which the two charts genuinely contribute to each other.

Nothing here mentions formal schemes, and this module deliberately imports nothing from the
project, so that it can sit below the whole two-patch cluster.

## Main definitions

* `AlgebraicGeometry.twoPatchWitnessIdeal`: the ideal `(X − 1) ⊆ ℚ[X]`.
* `AlgebraicGeometry.twoPatchWitnessOrigin`, `AlgebraicGeometry.twoPatchWitnessOne`: the origin
  and the point `1` of `𝔸¹_ℚ`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
-/

noncomputable section

open Polynomial

namespace AlgebraicGeometry

/-- The ideal `(X − 1) ⊆ ℚ[X]`: the standing two-patch witness completes `𝔸¹_ℚ` along it.

A `def` rather than an `abbrev` on purpose — an `abbrev` naming an object under study makes `rw`
fail on goals mentioning it, since keyed matching will not rewrite underneath one in a
type-correct way. -/
def twoPatchWitnessIdeal : Ideal ℚ[X] := Ideal.span {(X - C (1 : ℚ))}

theorem twoPatchWitnessIdeal_fg : twoPatchWitnessIdeal.FG :=
  Submodule.fg_span (Set.finite_singleton _)

/-- The origin of `𝔸¹_ℚ`, as a point of `Spec ℚ[X]`. -/
def twoPatchWitnessOrigin : PrimeSpectrum ℚ[X] :=
  ⟨Ideal.span {(X : ℚ[X])}, (Ideal.span_singleton_prime X_ne_zero).mpr prime_X⟩

/-- The point `1` of `𝔸¹_ℚ`: the centre of the completion. -/
def twoPatchWitnessOne : PrimeSpectrum ℚ[X] :=
  ⟨twoPatchWitnessIdeal,
    (Ideal.span_singleton_prime (prime_X_sub_C (1 : ℚ)).ne_zero).mpr (prime_X_sub_C (1 : ℚ))⟩

/-- **The origin does not lie on `V(X − 1)`**: evaluating a putative factorisation at `0` would
give `-1 = 0` in `ℚ`. This is what makes the witness nondegenerate — the completion at `1` really
does miss a point of the chart. -/
theorem twoPatchWitnessOrigin_notMem_zeroLocus :
    twoPatchWitnessOrigin ∉
      PrimeSpectrum.zeroLocus (twoPatchWitnessIdeal : Set ℚ[X]) := by
  intro hmem
  obtain ⟨q, hq⟩ : (X : ℚ[X]) ∣ X - C (1 : ℚ) :=
    Ideal.mem_span_singleton.mp
      ((PrimeSpectrum.mem_zeroLocus _ _).mp hmem (Ideal.mem_span_singleton_self _))
  have := congrArg (Polynomial.eval (0 : ℚ)) hq
  simp at this

/-- **The centre of the completion lies on `V(X − 1)`.** -/
theorem twoPatchWitnessOne_mem_zeroLocus :
    twoPatchWitnessOne ∈ PrimeSpectrum.zeroLocus (twoPatchWitnessIdeal : Set ℚ[X]) :=
  (PrimeSpectrum.mem_zeroLocus _ _).mpr Set.Subset.rfl

/-- `X` lies in the origin's prime ideal, which is the hypothesis every consumer feeds to
`notMem_range_completionTwoPatchToScheme_base`. -/
theorem X_mem_twoPatchWitnessOrigin : (X : ℚ[X]) ∈ twoPatchWitnessOrigin.asIdeal :=
  Ideal.mem_span_singleton_self _

end AlgebraicGeometry

end
