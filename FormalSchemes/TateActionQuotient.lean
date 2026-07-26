import FormalSchemes.ActionQuotient
import FormalSchemes.TateAction

set_option linter.style.header false

/-!
# Action-invariance of the Tate-chain structural morphism

The general categorical quotient interface `CategoryTheory.IsActionQuotient` (issue 224) is
instantiated here against the merged `q^ℤ`-period action on the Tate chain (issue 135). The one
concrete input it needs from the eventual quotient construction is recorded now: the structural
morphism `T ⟶ Spf R` is invariant under the action, hence descends to any quotient `T / q^ℤ`.

## Main result

* `AlgebraicGeometry.tateChainStructMap_isActionInvariant`: the structural morphism
  `tateChainStructMap : T ⟶ Spf R` is `IsActionInvariant` under `tatePeriodAction`.

This is exactly `tateShiftAut_zpow_comp_structMap` (every power of the shift automorphism commutes
with the structural morphism) repackaged through the general-purpose `IsActionInvariant` predicate,
confirming the interface is non-vacuous and matches the merged Tate infrastructure. When the
quotient `𝔈_q = T / q^ℤ` is constructed (issue 223 for the concrete two-chart model, or the general
construction here) as an `IsActionQuotient`, its `desc` applied to this invariant morphism produces
the structural morphism `𝔈_q ⟶ Spf R`.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)

/-- **The Tate-chain structural morphism is action-invariant.** The morphism
`tateChainStructMap : T ⟶ Spf R` is invariant under the `q^ℤ`-period action
`tatePeriodAction : ℤ → Aut T`: every power `σⁿ` of the shift automorphism commutes with it
(`tateShiftAut_zpow_comp_structMap`). Consequently it descends through any quotient `T / q^ℤ`. -/
theorem tateChainStructMap_isActionInvariant :
    IsActionInvariant (tatePeriodAction R I q hq hI) (tateChainStructMap R I q hq hI) := by
  intro g
  rw [tatePeriodAction_apply]
  exact tateShiftAut_zpow_comp_structMap R I q hq hI g.toAdd

end AlgebraicGeometry
