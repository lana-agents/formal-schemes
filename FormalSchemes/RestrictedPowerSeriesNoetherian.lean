import FormalSchemes.CompleteNoetherian
import FormalSchemes.AssociatedGradedCompletion
import FormalSchemes.RestrictedPowerSeries
import Mathlib.RingTheory.Polynomial.Basic

set_option linter.style.header false

/-!
# Restricted power series over a Noetherian adic ring are Noetherian

This file is **Part 3 of 3** of issue 98 — the assembly that closes it. It combines the two
completion-analogue-of-Hilbert-basis ingredients already in the repository:

* Part 2 (`FormalSchemes/CompleteNoetherian.lean`, Atiyah–Macdonald 10.25):
  a `J`-adically complete and separated ring whose associated graded ring is Noetherian is itself
  Noetherian.
* the transport lemma (`FormalSchemes/AssociatedGradedCompletion.lean`, issue 149): for `B`
  Noetherian and `K` finitely generated, `gr_{K̂}(B̂)` is Noetherian (obtained *by transport* from
  `gr_K(B)`, which is Noetherian by Part 1, dodging the circularity of trying to use `B̂`
  Noetherian directly).

## Main results

* `AdicCompletion.isNoetherianRing`: **Atiyah–Macdonald 10.26.** The `K`-adic completion of a
  Noetherian ring `B` along a finitely generated ideal `K` is Noetherian.
* `RestrictedPowerSeries.isNoetherianRing_of_fg` /
  `RestrictedPowerSeries.instIsNoetherianRing`: the original issue-98 target — the restricted power
  series ring `R{X₁, …, Xₙ}` over a Noetherian ring `R` is Noetherian. As an `instance` this
  discharges the residual `[IsNoetherianRing (RestrictedPowerSeries R I n)]` hypotheses carried by
  `IsTopologicallyFiniteType.isAdicRing_of_noetherian` (issue 66) and `annulus` (issue 68,
  `FormalSchemes/TateAnnulus.lean`).

## References

* [Atiyah–Macdonald, *Introduction to Commutative Algebra*], Prop. 10.26.
* [Bosch, *Lectures on Formal and Rigid Geometry* (LNM 2105)], §7.3.
* Stacks Tag 05GH.
-/

noncomputable section

universe u

namespace AdicCompletion

variable {B : Type u} [CommRing B] (K : Ideal B)

/-- **Atiyah–Macdonald, Prop. 10.26.** The `K`-adic completion of a Noetherian ring `B` along a
finitely generated ideal `K` is Noetherian.

The completion `B̂ := AdicCompletion K B` is complete and separated for its ideal of definition
`K̂ = idealOfDefinition K` (`isAdicComplete_map`), and its associated graded ring `gr_{K̂}(B̂)` is
Noetherian by transport from `gr_K(B)` (`isNoetherianRing_completion`); AM 10.25
(`isNoetherianRing_of_isAdicComplete_of_isNoetherianRing_associatedGraded`) then yields the
result. -/
theorem isNoetherianRing [IsNoetherianRing B] (hK : K.FG) :
    IsNoetherianRing (AdicCompletion K B) := by
  haveI : IsAdicComplete (idealOfDefinition K) (AdicCompletion K B) := isAdicComplete_map K hK
  exact AssociatedGraded.isNoetherianRing_of_isAdicComplete_of_isNoetherianRing_associatedGraded
    (idealOfDefinition K) (AssociatedGraded.isNoetherianRing_completion K hK)

end AdicCompletion

namespace RestrictedPowerSeries

variable {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ)

/-- **The original issue-98 target.** The restricted power series ring `R{X₁, …, Xₙ}` over a
Noetherian ring `R`, along a finitely generated ideal `I`, is Noetherian.

By definition `R{X₁, …, Xₙ} = AdicCompletion (I·R[X]) (MvPolynomial (Fin n) R)`. The base
`MvPolynomial (Fin n) R` is Noetherian by the Hilbert basis theorem and the extended ideal
`I·R[X]` is finitely generated (`I.FG.map`), so this is `AdicCompletion.isNoetherianRing`. -/
theorem isNoetherianRing_of_fg [IsNoetherianRing R] (hI : I.FG) :
    IsNoetherianRing (RestrictedPowerSeries R I n) :=
  AdicCompletion.isNoetherianRing _ (hI.map _)

/-- Over a Noetherian ring every ideal is finitely generated, so `R{X₁, …, Xₙ}` is Noetherian with
no separate finiteness hypothesis. This `instance` discharges the residual
`[IsNoetherianRing (RestrictedPowerSeries R I n)]` hypotheses of issues 66 and 68. -/
instance instIsNoetherianRing [IsNoetherianRing R] :
    IsNoetherianRing (RestrictedPowerSeries R I n) :=
  isNoetherianRing_of_fg I n (IsNoetherian.noetherian I)

end RestrictedPowerSeries
