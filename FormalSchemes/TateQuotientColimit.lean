import FormalSchemes.ActionQuotientColimit
import FormalSchemes.TateQuotientMap
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace.HasColimits

set_option linter.style.header false

/-!
# The generic quotient exists for locally ringed spaces, and it is `𝔈_q`

`FormalSchemes.ActionQuotientColimit` builds the quotient `X / G` as a coequalizer in any category
with the two colimits involved. This file supplies the ambient category this project needs and
checks the construction against the one quotient it already had by hand.

## The ambient category

`LocallyRingedSpace` has **all** small colimits — `AlgebraicGeometry.LocallyRingedSpace`'s
`HasColimits` instance in `Mathlib/Geometry/RingedSpace/LocallyRingedSpace/HasColimits.lean`,
assembled from small coproducts and coequalizers. So the coequalizer construction applies to *every*
action of a small monoid on a locally ringed space, with no freeness, proper discontinuity or
finiteness hypothesis: `AlgebraicGeometry.LocallyRingedSpace.exists_isActionQuotient`.

That is worth stating explicitly because both `FormalSchemes.ActionQuotient` and
`FormalSchemes.TateQuotientMap` are written as though no such construction were available. The
first says colimits "of this shape are not available off the shelf in the target categories
(`LocallyRingedSpace`, `FormalScheme`)"; for `LocallyRingedSpace` that is false. The second
observes that `CategoryTheory.GlueData'` has `V : ∀ i j, i ≠ j → C`, so `T_inv / ⟨σ⟩` — whose
fundamental domain is a single patch — "has no model in this framework". That remains true of the
*glue-datum* framework, and it is why `𝔈_q` is the quotient by `σ²`; but it is a statement about
presentations, not about existence. The quotient locally ringed space `T_inv / ⟨σ⟩` exists, by the
theorem below. What is open is whether it is a formal scheme.

## The check against the hand-built quotient

`AlgebraicGeometry.tateQuotientIsActionQuotient` exhibits `𝔈_q` as `T_inv / ⟨σ²⟩`. Uniqueness of
quotients (`CategoryTheory.IsActionQuotient.isoActionQuotient`) therefore identifies `𝔈_q` with the
coequalizer, compatibly with the two projections. Two consequences, in opposite directions:

* the generic construction reproduces the object that was built patch by patch — the two agree, so
  the coequalizer is not some larger sheaf-theoretic artefact; and
* conversely, this is the one case on the tree where the generic quotient of a formal scheme's
  underlying locally ringed space **is** a formal scheme
  (`AlgebraicGeometry.exists_formalScheme_iso_tateActionQuotient`). The general statement — a free,
  properly discontinuous action has a formal-scheme quotient — is still open, and this is its
  first instance.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.exists_isActionQuotient`: every action of a small monoid on
  a locally ringed space has a quotient.
* `AlgebraicGeometry.tateCurveModelIsoActionQuotient`: `𝔈_q ≅ T_inv / ⟨σ²⟩` as locally ringed
  spaces, the hand-built model against the generic coequalizer.
* `AlgebraicGeometry.exists_formalScheme_iso_tateActionQuotient`: that coequalizer is (isomorphic
  to) a formal scheme.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Every action on a locally ringed space has a quotient -/

/-- **The quotient of a locally ringed space by a group action always exists.** `LocallyRingedSpace`
has all small colimits, so the coequalizer of `FormalSchemes.ActionQuotientColimit` is available for
any action of any monoid in the same universe — no freeness or proper discontinuity is used.

This is the existence half of the first goal of issue 224, at the locally-ringed-space level. It
says nothing about the quotient being a formal scheme. -/
theorem LocallyRingedSpace.exists_isActionQuotient (G : Type u) [Monoid G]
    (X : LocallyRingedSpace.{u}) (a : G →* Aut X) :
    ∃ (Q : LocallyRingedSpace.{u}) (π : X ⟶ Q), Nonempty (IsActionQuotient a π) :=
  ⟨actionQuotient a, actionQuotientπ a, ⟨isActionQuotient_actionQuotientπ a⟩⟩

/-! ### The Tate-curve model is the coequalizer -/

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)

/-- **The hand-built Tate-curve model agrees with the generic quotient.** `𝔈_q` was glued patch by
patch from the parity map (`FormalSchemes.TateQuotientMap`); the right-hand side is the coequalizer
of the two legs `∐_{n : ℤ} T_inv ⇉ T_inv`. Both satisfy the universal property of `T_inv / ⟨σ²⟩`,
so they are canonically isomorphic. -/
def tateCurveModelIsoActionQuotient :
    (tateCurveModel R I q hq hI).toLocallyRingedSpace ≅
      actionQuotient (tateInvPeriodSqAction R I q hq hI) :=
  (tateQuotientIsActionQuotient R I q hq hI).isoActionQuotient

/-- The isomorphism carries the glued quotient map `π : T_inv ⟶ 𝔈_q` to the coequalizer
projection. -/
theorem tateQuotientPi_comp_tateCurveModelIsoActionQuotient_hom :
    tateQuotientPi R I q hq hI ≫ (tateCurveModelIsoActionQuotient R I q hq hI).hom =
      actionQuotientπ (tateInvPeriodSqAction R I q hq hI) :=
  (tateQuotientIsActionQuotient R I q hq hI).comp_isoActionQuotient_hom

/-- **The generic quotient of `T_inv` by `q^{2ℤ}` is a formal scheme.** The first — and, on this
tree, only — case in which the coequalizer quotient of a formal scheme's underlying locally ringed
space is known to be a formal scheme again. The witness is `𝔈_q` itself. -/
theorem exists_formalScheme_iso_tateActionQuotient :
    ∃ Y : FormalScheme.{u}, Nonempty (Y.toLocallyRingedSpace ≅
      actionQuotient (tateInvPeriodSqAction R I q hq hI)) :=
  ⟨tateCurveModel R I q hq hI, ⟨tateCurveModelIsoActionQuotient R I q hq hI⟩⟩

end AlgebraicGeometry
