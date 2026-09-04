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

This file records that, by factoring the existing proof through the pointwise conclusion. The
conclusion itself, `AlgebraicGeometry.LocallyRingedSpace.HasAffineChartAt`, is named in
`FormalSchemes.Gluing` beside the criterion it is the hypothesis of, together with
`LocallyRingedSpace.formalSchemeOfHasAffineChartAt` and
`LocallyRingedSpace.hasAffineChartAt_of_isoRestrict`. Nothing here is a weakening of
`IsProperlyDiscontinuousOn` or of `IsFreeProperlyDiscontinuous`: both are used exactly as stated,
and `freeActionQuotientFormalScheme` is untouched.

## Why the pointwise form is worth naming

An action can be properly discontinuous at some points and not at others, and then the global
criterion says nothing at all while the pointwise one still produces charts. The motivating case is
the one-step shift `σ` on the inversion-glued Tate chain, which
`AlgebraicGeometry.not_isFreeProperlyDiscontinuous_tateInvPeriodAction`
(`FormalSchemes.TateInvPeriodNodePoint`) refutes: there the failure is concentrated on the orbit of
the nodes, and this file is what lets the rest of the chain be dealt with anyway.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.hasAffineChartAt_of_formalScheme`: every point of a formal
  scheme has a chart, so `HasAffineChartAt` is characteristic and not merely sufficient.
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

/-- **The converse of `formalSchemeOfHasAffineChartAt`**: every point of a formal scheme has an
affine formal chart. Together the two say `HasAffineChartAt` is not merely sufficient but
characteristic. This is `FormalScheme.exists_openImmersion`, whose conclusion is
`HasAffineChartAt X.toLocallyRingedSpace x` unfolded. -/
theorem hasAffineChartAt_of_formalScheme (X : FormalScheme.{u}) (x : X) :
    HasAffineChartAt X.toLocallyRingedSpace x :=
  X.exists_openImmersion x

/-- **Carrying a formal scheme structure is having a chart at every point**, as an `Iff`. The two
implications are `formalSchemeOfHasAffineChartAt` (`FormalSchemes.Gluing`) and
`hasAffineChartAt_of_formalScheme`; naming the equivalence is what lets a reduction stated in
charts be read as a statement about the object, and back, without the transport across
`FormalScheme.toLocallyRingedSpace` being written out at each site. -/
theorem exists_formalScheme_iff_forall_hasAffineChartAt (Z : LocallyRingedSpace.{u}) :
    (∃ X : FormalScheme.{u}, X.toLocallyRingedSpace = Z) ↔ ∀ z : Z, HasAffineChartAt Z z := by
  constructor
  · rintro ⟨X, rfl⟩ z
    exact hasAffineChartAt_of_formalScheme X z
  · exact fun h => ⟨formalSchemeOfHasAffineChartAt Z h, rfl⟩

section Quotient

variable {G : Type v} [Group G] [Small.{u} G] {X : FormalScheme.{u}}
variable {a : G →* Aut X.toLocallyRingedSpace}
variable {Q : LocallyRingedSpace.{u}} {π : X.toLocallyRingedSpace ⟶ Q}

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
-- Comparing the restriction of the ambient space with the affine model needs reducible-transparency
-- defeq checks. This proof is `LocallyRingedSpace.formalSchemeOfIsOpenImmersionRestrict`
-- (`FormalSchemes.ActionQuotientFormalScheme`) read one point at a time, and the option is on that
-- definition for the same comparison; those two are the only sites that need it *for that
-- comparison*, which is not a claim about the tree's other
-- `set_option backward.isDefEq.respectTransparency false` blocks — there are 53 of them, in 30
-- other files, and they justify themselves locally. The measurement, and the tree-wide rule this
-- comment used to assert in place of it, are recorded there rather than repeated here (issue
-- 1531).
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
