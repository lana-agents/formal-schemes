import FormalSchemes.FreeActionQuotientFormalScheme

set_option linter.style.header false

/-!
# Affine charts of an action quotient, one point at a time

`FormalSchemes.FreeActionQuotientFormalScheme` proves that the quotient of a locally finitely
generated formal scheme by a **free, properly discontinuous** action is a formal scheme. That
hypothesis is global: `IsFreeProperlyDiscontinuous` asks *every* point of `X` for a separating
neighbourhood, and `freeActionQuotientFormalScheme` consumes all of them at once.

The proof does not need them all at once. `LocallyRingedSpace.IsOpenImmersion.formalScheme`
(`FormalSchemes.Gluing`) is a **pointwise** criterion — a locally ringed space is a formal scheme as
soon as every one of its points is in the range of an open immersion from an affine formal
spectrum — and `isIso_stalkMap_ofRestrict_comp` takes only `IsProperlyDiscontinuousOn a U`, a
statement about the single open `U`. So a separating neighbourhood of a *single* `x : X` already
produces the chart of `Q` at `π x`, with no hypothesis anywhere else on `X`.

This file records that, by naming the pointwise conclusion and factoring the existing proof through
it. Nothing here is a weakening of `IsProperlyDiscontinuousOn` or of `IsFreeProperlyDiscontinuous`:
both are used exactly as stated, and `freeActionQuotientFormalScheme` is untouched.

## Why the pointwise form is worth naming

An action can be properly discontinuous at some points and not at others, and then the global
criterion says nothing at all while the pointwise one still produces charts. The motivating case is
the one-step shift `σ` on the inversion-glued Tate chain, which
`AlgebraicGeometry.not_isFreeProperlyDiscontinuous_tateInvPeriodAction`
(`FormalSchemes.TateInvPeriodNodePoint`) refutes: there the failure is concentrated on the orbit of
the nodes, and this file is what lets the rest of the chain be dealt with anyway.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.HasAffineChartAt`: the hypothesis of
  `LocallyRingedSpace.IsOpenImmersion.formalScheme`, at one point.
* `AlgebraicGeometry.LocallyRingedSpace.formalSchemeOfHasAffineChartAt`: a locally ringed space with
  a chart at every point is a formal scheme — the criterion restated in those terms.
* `AlgebraicGeometry.LocallyRingedSpace.hasAffineChartAt_of_isoRestrict`: an open of `X`
  *identified* with a formal spectrum gives a chart at each of its points — the converse of
  `LocallyRingedSpace.IsOpenImmersion.isoRestrictOfRangeEq`, which turns a chart into such an
  identification.
* `AlgebraicGeometry.LocallyRingedSpace.hasAffineChartAt_of_isProperlyDiscontinuousOn`: **the
  pointwise chart theorem** — a separating open around `x` gives a chart of `Q` at `π x`.
* `AlgebraicGeometry.LocallyRingedSpace.freeActionQuotientFormalScheme_eq_ofHasAffineChartAt`:
  the global theorem factors through the pointwise one, so the two agree.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace

universe v u

namespace AlgebraicGeometry

namespace LocallyRingedSpace

/-- **`Q` has an affine formal chart at `x`**: some formal spectrum `Spf I` of an adic ring admits
an open immersion into `Q` whose range contains `x`. This is exactly the per-point hypothesis of
`LocallyRingedSpace.IsOpenImmersion.formalScheme`, named so that it can be established one point at
a time. -/
def HasAffineChartAt (Q : LocallyRingedSpace.{u}) (x : Q) : Prop :=
  ∃ (R : Type u) (_ : CommRing R) (_ : TopologicalSpace R) (I : Ideal R) (_ : IsAdicRing I)
    (f : FormalSpectrum.locallyRingedSpaceObj I ⟶ Q),
      (x ∈ Set.range f.base :) ∧ LocallyRingedSpace.IsOpenImmersion f

/-- **A locally ringed space with an affine formal chart at every point is a formal scheme.** This
is `LocallyRingedSpace.IsOpenImmersion.formalScheme` with its hypothesis spelled through
`HasAffineChartAt`; the content is entirely in that theorem. -/
def formalSchemeOfHasAffineChartAt (Q : LocallyRingedSpace.{u})
    (h : ∀ x : Q, HasAffineChartAt Q x) : FormalScheme.{u} :=
  LocallyRingedSpace.IsOpenImmersion.formalScheme Q h

/-- The formal scheme produced has `Q` itself as its underlying locally ringed space. -/
@[simp]
theorem formalSchemeOfHasAffineChartAt_toLocallyRingedSpace (Q : LocallyRingedSpace.{u})
    (h : ∀ x : Q, HasAffineChartAt Q x) :
    (formalSchemeOfHasAffineChartAt Q h).toLocallyRingedSpace = Q :=
  rfl

/-- **An open identified with a formal spectrum is a chart at each of its points.** If
`e : X|_U ≅ Spf L`, then `e.inv ≫ X.ofRestrict U.isOpenEmbedding` is an open immersion whose range
is `U`, so every `y ∈ U` has an affine formal chart.

This is the direction opposite to `LocallyRingedSpace.IsOpenImmersion.isoRestrictOfRangeEq`
(`FormalSchemes.OpenImmersionIsoOfRangeEq`), which converts an open immersion with range `U` into
such an identification. Every *cover-shaped* hypothesis on this tree — the
`AlgebraicGeometry.FormalScheme.local_affine` field,
`FormalSpectrum.isThickeningColimitTarget_of_cover`,
`FormalSpectrum.existsUnique_hom_thickeningMap_spfCover` — supplies data in the `≅` direction,
while `HasAffineChartAt` consumes it in the open-immersion direction; this is the one line between
them, and it is what makes a formal-affine chart *datum* on a target say something about the
target's points. -/
theorem hasAffineChartAt_of_isoRestrict {X : LocallyRingedSpace.{u}} (U : Opens X.toTopCat)
    {C : Type u} [CommRing C] [TopologicalSpace C] (L : Ideal C) [IsAdicRing L]
    (e : X.restrict U.isOpenEmbedding ≅ FormalSpectrum.locallyRingedSpaceObj L)
    {y : X} (hy : y ∈ U) : HasAffineChartAt X y := by
  refine ⟨C, inferInstance, inferInstance, L, inferInstance,
    e.inv ≫ X.ofRestrict U.isOpenEmbedding, ⟨e.hom.base ⟨y, hy⟩, ?_⟩, inferInstance⟩
  simp only [comp_toHom, PresheafedSpace.comp_base, TopCat.hom_comp, ContinuousMap.comp_apply,
    iso_hom_base_inv_base_apply]
  rfl

/-- **The converse**: every point of a formal scheme has an affine formal chart. Together with
`formalSchemeOfHasAffineChartAt` this says `HasAffineChartAt` is not merely sufficient but
characteristic. -/
theorem hasAffineChartAt_of_formalScheme (X : FormalScheme.{u}) (x : X) :
    HasAffineChartAt X.toLocallyRingedSpace x :=
  X.exists_openImmersion x

section Quotient

variable {G : Type v} [Group G] [Small.{u} G] {X : FormalScheme.{u}}
variable {a : G →* Aut X.toLocallyRingedSpace}
variable {Q : LocallyRingedSpace.{u}} {π : X.toLocallyRingedSpace ⟶ Q}

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
-- Comparing the restriction of the ambient space with the affine model needs reducible-transparency
-- defeq checks, as everywhere this tree feeds `IsOpenImmersion.formalScheme`; see `Gluing.lean:48`
-- and `ActionQuotientFormalScheme.lean:86`.
/-- **The pointwise chart theorem.** A separating open `U ∋ x` gives an affine formal chart of the
quotient at `π x`, with no hypothesis at any other point of `X`.

The two ingredients are both local in `U`: `isOpenImmersion_ofRestrict_comp_of_stalk_iso` makes
`X|_U ⟶ Q` an open immersion from `IsProperlyDiscontinuousOn a U` alone, and
`FormalScheme.restrictOpen` supplies an affine chart of `X|_U` through `x`. Composing them is the
chart. This is the body of `formalSchemeOfIsOpenImmersionRestrict` with the outer quantifier
removed, and that theorem is re-derived from it below. -/
theorem hasAffineChartAt_of_isProperlyDiscontinuousOn (hX : X.LocallyFG) (h : IsActionQuotient a π)
    {U : Opens X} (hU : IsProperlyDiscontinuousOn a (U : Set X)) {x : X} (hx : x ∈ U) :
    HasAffineChartAt Q (π.base x) := by
  haveI := isIso_stalkMap_ofRestrict_comp h U hU
  haveI := isOpenImmersion_ofRestrict_comp_of_stalk_iso h hU
  obtain ⟨R, hR, hTR, J, hJ, f, ⟨z, hz⟩, hf⟩ := (X.restrictOpen hX U).exists_openImmersion ⟨x, hx⟩
  refine ⟨R, hR, hTR, J, hJ, ?_, ?_, ?_⟩
  · exact f ≫ (X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding ≫ π)
  · refine ⟨z, ?_⟩
    simp only [LocallyRingedSpace.comp_toHom, PresheafedSpace.comp_base, TopCat.hom_comp,
      ContinuousMap.coe_comp, Function.comp_apply]
    rw [hz]
    rfl
  · exact LocallyRingedSpace.IsOpenImmersion.comp _ _

omit [Small.{u} G] in
/-- **The quotient projection is constant on orbits**, on underlying spaces: the invariance
`(a g).hom ≫ π = π` of `IsActionQuotient` read at a point. So `HasAffineChartAt Q (π x)` is a
property of the orbit of `x`, not of `x`. -/
theorem base_action_base (h : IsActionQuotient a π) (g : G) (x : X) :
    π.base ((a g).hom.base x) = π.base x :=
  congrArg (fun m : X.toLocallyRingedSpace ⟶ Q => m.base x) (h.isInvariant g)

/-- **The global theorem factors through the pointwise one.** Given a separating neighbourhood at
every point, `hasAffineChartAt_of_isProperlyDiscontinuousOn` supplies a chart at every point of `Q`
(each of which is `π x` for some `x`, by `base_surjective_of_isActionQuotient`), so
`formalSchemeOfHasAffineChartAt` reproves `freeActionQuotientFormalScheme`. -/
theorem hasAffineChartAt_of_isFreeProperlyDiscontinuous (hX : X.LocallyFG)
    (h : IsActionQuotient a π) (hfpd : IsFreeProperlyDiscontinuous a) (xbar : Q) :
    HasAffineChartAt Q xbar := by
  obtain ⟨x, rfl⟩ := base_surjective_of_isActionQuotient h xbar
  obtain ⟨U, hUopen, hxU, hU⟩ := hfpd x
  exact hasAffineChartAt_of_isProperlyDiscontinuousOn hX h (U := ⟨U, hUopen⟩) hU hxU

/-- The two routes to "the quotient is a formal scheme" produce the same object: both have `Q` as
their underlying locally ringed space, and `FormalScheme` is a structure over that. -/
theorem freeActionQuotientFormalScheme_eq_ofHasAffineChartAt (hX : X.LocallyFG)
    (h : IsActionQuotient a π) (hfpd : IsFreeProperlyDiscontinuous a) :
    freeActionQuotientFormalScheme hX h hfpd =
      formalSchemeOfHasAffineChartAt Q
        (hasAffineChartAt_of_isFreeProperlyDiscontinuous hX h hfpd) :=
  rfl

end Quotient

end LocallyRingedSpace

end AlgebraicGeometry
