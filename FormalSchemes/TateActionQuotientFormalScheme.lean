import FormalSchemes.ActionQuotientFormalScheme
import FormalSchemes.TateChainInvLocallyFG
import FormalSchemes.TateQuotientColimit

set_option linter.style.header false

/-!
# The Tate curve as the quotient produced by the general criterion, modulo the stalk lemma

`AlgebraicGeometry.exists_formalScheme_iso_tateActionQuotient`
(`FormalSchemes/TateQuotientColimit.lean`) says the coequalizer quotient `T_inv / ⟨σ²⟩` is a formal
scheme, and proves it by exhibiting the hand-glued `𝔈_q = tateCurveModel`. That is a fact about one
object, obtained by a route the general theory does not travel. The question it leaves — *does the
general criterion, run on this action, land on the same object?* — is the check that the general
theory has the right hypotheses.

This file answers it, **conditionally on one hypothesis and on nothing else**.

## What is assumed here, and where it is discharged

`TateStalkIsoHypothesis` below is the statement that over a separating open `U` of `T_inv` the
stalk maps of `T_inv|_U ⟶ T_inv / ⟨σ²⟩` are isomorphisms. It is a hypothesis **of this file** —
every result below carries it as an explicit argument — and it is not proved here, because nothing
Mathlib says about the stalk maps of a locally ringed space coequalizer gives it: those statements
say the maps are *local homomorphisms*, which is what makes the coequalizer a locally ringed space
at all, and none says they are isomorphisms;
`AlgebraicGeometry.LocallyRingedSpace.HasCoequalizer.coequalizer_π_stalk_isLocalHom` is the
representative one.

It is a **theorem** one module further on: `AlgebraicGeometry.tateStalkIsoHypothesis`
(`FormalSchemes.TateActionQuotientStalk`), an instance of the general stalk lemma
`AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_ofRestrict_comp`. So the unconditional forms
of everything below exist — `AlgebraicGeometry.tateQuotientFormalScheme` and
`AlgebraicGeometry.tateQuotientIsoTateCurveModel` — and a caller should reach for those rather
than for the hypothesis-carrying versions here.

## What is proved

That the hypothesis is the *only* thing missing. The general criterion
`AlgebraicGeometry.LocallyRingedSpace.formalSchemeOfStalkIso` needs three further inputs, and all
three are now theorems:

* `(tateChainInv …).LocallyFG`, by `AlgebraicGeometry.tateChainInv_locallyFG`;
* the universal property of the coequalizer projection, by
  `CategoryTheory.isActionQuotient_actionQuotientπ`;
* freeness and proper discontinuity of the action, by
  `AlgebraicGeometry.tateInvPeriodSq_isFreeProperlyDiscontinuous`.

Feeding them in gives a formal scheme whose underlying locally ringed space **is** the coequalizer,
definitionally (`tateActionQuotientFormalScheme_toLocallyRingedSpace`), so
`exists_formalScheme_iso_tateActionQuotient` is re-derived rather than restated
(`exists_formalScheme_iso_tateActionQuotient_of_stalkIso`, whose witness isomorphism is
`Iso.refl`), and the object it produces is isomorphic to the hand-glued model
(`tateActionQuotientIsoTateCurveModel`).

## Why the hypothesis is not vacuous

A hypothesis quantified over separating opens would be uninteresting if no separating open existed,
or if the space were empty. Neither happens: `tateInvPeriodSq_isFreeProperlyDiscontinuous` produces
a separating neighbourhood of *every* point — the patch `U_n` of the chain containing it —
restated as an `Opens` in `tateInvPeriodSq_exists_separating_opens`, and `tateChainInv_nonempty`
says there are points to produce them at, whenever `q` lies in a proper ideal of definition. So the
hypothesis is applied at genuinely occurring opens.

## Main results

* `AlgebraicGeometry.TateStalkIsoHypothesis`: the assumption, named.
* `AlgebraicGeometry.tateInvPeriodSq_exists_separating_opens`: the opens it quantifies over exist.
* `AlgebraicGeometry.tateActionQuotientFormalScheme`: the formal scheme the general criterion
  produces, and `…_toLocallyRingedSpace`, that it is the coequalizer.
* `AlgebraicGeometry.exists_formalScheme_iso_tateActionQuotient_of_stalkIso`: 1144's goal 4,
  conditional on the hypothesis.
* `AlgebraicGeometry.tateActionQuotientIsoTateCurveModel`: it is the hand-glued `𝔈_q`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)

/-- **Every point of the chain has a separating open neighbourhood, packaged as an `Opens`.** This
is `tateInvPeriodSq_isFreeProperlyDiscontinuous` in the form the hypothesis below quantifies over,
and together with `tateChainInv_nonempty` it is what makes that hypothesis a statement about opens
that genuinely occur rather than a vacuous one. -/
theorem tateInvPeriodSq_exists_separating_opens (x : tateChainInv R I q hq hI) :
    ∃ U : Opens (tateChainInv R I q hq hI), x ∈ U ∧
      LocallyRingedSpace.IsProperlyDiscontinuousOn (tateInvPeriodSqAction R I q hq hI)
        (U : Set (tateChainInv R I q hq hI)) := by
  obtain ⟨U, hUopen, hxU, hU⟩ := tateInvPeriodSq_isFreeProperlyDiscontinuous R I q hq hI x
  exact ⟨⟨U, hUopen⟩, hxU, hU⟩

/-- **The stalk hypothesis for the Tate `q^{2ℤ}`-action**, i.e. the remaining half of "the
projection of the quotient is a local isomorphism". The topological half — that the projection
restricts to an open embedding of a separating open — is
`AlgebraicGeometry.LocallyRingedSpace.isOpenEmbedding_restrict_of_isProperlyDiscontinuousOn`; this
is what `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_stalk_iso` needs on top of it.

**This is an assumption, not a theorem.** It is stated here so that the results below can name
exactly what they depend on. -/
def TateStalkIsoHypothesis : Prop :=
  ∀ U : Opens (tateChainInv R I q hq hI),
    LocallyRingedSpace.IsProperlyDiscontinuousOn (tateInvPeriodSqAction R I q hq hI)
        (U : Set (tateChainInv R I q hq hI)) →
      ∀ y : ((tateChainInv R I q hq hI).toLocallyRingedSpace.restrict U.isOpenEmbedding).toTopCat,
        IsIso (((tateChainInv R I q hq hI).toLocallyRingedSpace.ofRestrict U.isOpenEmbedding ≫
          actionQuotientπ (tateInvPeriodSqAction R I q hq hI)).stalkMap y)

/-- **The Tate quotient as the general criterion produces it.** Everything the criterion asks for
besides the stalk hypothesis is discharged: `tateChainInv_locallyFG` for the source,
`isActionQuotient_actionQuotientπ` for the universal property, and
`tateInvPeriodSq_isFreeProperlyDiscontinuous` for the action. -/
def tateActionQuotientFormalScheme (hstalk : TateStalkIsoHypothesis R I q hq hI) :
    FormalScheme.{u} :=
  LocallyRingedSpace.formalSchemeOfStalkIso (tateChainInv_locallyFG R I q hq hI)
    (isActionQuotient_actionQuotientπ (tateInvPeriodSqAction R I q hq hI))
    (tateInvPeriodSq_isFreeProperlyDiscontinuous R I q hq hI) hstalk

/-- **The criterion upgrades the coequalizer itself, not a look-alike.** True by construction, and
recorded because it is what makes the re-derivation below a re-derivation. -/
@[simp]
theorem tateActionQuotientFormalScheme_toLocallyRingedSpace
    (hstalk : TateStalkIsoHypothesis R I q hq hI) :
    (tateActionQuotientFormalScheme R I q hq hI hstalk).toLocallyRingedSpace =
      actionQuotient (tateInvPeriodSqAction R I q hq hI) :=
  rfl

/-- **`exists_formalScheme_iso_tateActionQuotient`, re-derived from the general criterion.** The
existing proof exhibits the hand-glued `𝔈_q`; this one produces the formal scheme by the general
route and the connecting isomorphism is `Iso.refl`, because the object produced *is* the
coequalizer. -/
theorem exists_formalScheme_iso_tateActionQuotient_of_stalkIso
    (hstalk : TateStalkIsoHypothesis R I q hq hI) :
    ∃ Y : FormalScheme.{u}, Nonempty (Y.toLocallyRingedSpace ≅
      actionQuotient (tateInvPeriodSqAction R I q hq hI)) :=
  ⟨tateActionQuotientFormalScheme R I q hq hI hstalk, ⟨Iso.refl _⟩⟩

/-- **The general criterion lands on the hand-glued model.** This is the check that the general
theory has the right hypotheses: run on the project's only instance, it reproduces `𝔈_q` rather
than some other object. The isomorphism is `tateCurveModelIsoActionQuotient` read backwards. -/
def tateActionQuotientIsoTateCurveModel (hstalk : TateStalkIsoHypothesis R I q hq hI) :
    (tateActionQuotientFormalScheme R I q hq hI hstalk).toLocallyRingedSpace ≅
      (tateCurveModel R I q hq hI).toLocallyRingedSpace :=
  (tateCurveModelIsoActionQuotient R I q hq hI).symm

end AlgebraicGeometry
