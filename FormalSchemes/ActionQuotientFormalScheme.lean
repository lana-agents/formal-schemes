import FormalSchemes.ActionDiscontinuous
import FormalSchemes.OpenFormalSubscheme
import FormalSchemes.Gluing

set_option linter.style.header false

/-!
# The local criterion for an action quotient to be a formal scheme

`FormalSchemes.ActionDiscontinuous` proves the *topological* half of "the projection of a free,
properly discontinuous action quotient is a local isomorphism": over a separating open `U`, the map
`π.base` restricts to an open embedding. By
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.of_stalk_iso` the remaining half is that the
stalk maps of `X.ofRestrict ≫ π` are isomorphisms, and that is a statement about the structure
sheaf of a coequalizer which nothing on this tree or in Mathlib has.

This file assembles **everything else**. It shows that the stalk half is the *only* thing left:
given it, the quotient of a locally finitely-generated formal scheme by a free, properly
discontinuous action is a formal scheme, and the assembly is a dozen lines.

## Why the hypothesis is stated as an open immersion rather than as a stalk isomorphism

Both forms are provided. `formalSchemeOfIsOpenImmersionRestrict` is the shape
`LocallyRingedSpace.IsOpenImmersion.of_stalk_iso` produces and the shape the local criterion
consumes; `formalSchemeOfStalkIso` takes the stalk hypothesis directly and calls `of_stalk_iso`
itself, so a future proof of the stalk lemma plugs into it with nothing in between.

## Where `LocallyFG` comes from, and that it is not removable

The local criterion `LocallyRingedSpace.IsOpenImmersion.formalScheme` wants, around every point of
the quotient, an open immersion out of an *affine* formal scheme `Spf J`. Producing one inside a
separating open `U` is exactly what `FormalScheme.restrictOpen` gives — its underlying locally
ringed space is `X.restrict U.isOpenEmbedding` definitionally, so
`FormalScheme.exists_openImmersion` applied to it hands over the chart with no neighbourhood-basis
argument. `restrictOpen` requires `X.LocallyFG`, so the theorems below do too. (The alternative
entry point, `FormalScheme.exists_affineChart_subset`, carries the same hypothesis.)

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.isOpenImmersion_ofRestrict_comp_of_stalk_iso`: the two
  halves combine — an open embedding on the base plus stalk isomorphisms make the restriction of
  the projection an open immersion of locally ringed spaces.
* `AlgebraicGeometry.LocallyRingedSpace.formalSchemeOfIsOpenImmersionRestrict`: the quotient is a
  formal scheme, given that the projection restricts to an open immersion over separating opens.
* `AlgebraicGeometry.LocallyRingedSpace.formalSchemeOfStalkIso`: the same, phrased with the stalk
  hypothesis, which is the one remaining unknown.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory Topology TopologicalSpace

universe v u

namespace AlgebraicGeometry

namespace LocallyRingedSpace

variable {G : Type v} [Group G] [Small.{u} G] {X : FormalScheme.{u}}
variable {a : G →* Aut X.toLocallyRingedSpace}
variable {Q : LocallyRingedSpace.{u}} {π : X.toLocallyRingedSpace ⟶ Q}

/-- **The two halves combine.** Over a separating open `U`, the base map of the restricted
projection is an open embedding (`isOpenEmbedding_restrict_of_isProperlyDiscontinuousOn`); if in
addition its stalk maps are isomorphisms, `of_stalk_iso` makes it an open immersion of locally
ringed spaces. The open-embedding half is supplied on the nose — no adapter is needed. -/
theorem isOpenImmersion_ofRestrict_comp_of_stalk_iso (h : IsActionQuotient a π) {U : Opens X}
    (hU : IsProperlyDiscontinuousOn a (U : Set X))
    [∀ y : (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).toTopCat,
      IsIso ((X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding ≫ π).stalkMap y)] :
    LocallyRingedSpace.IsOpenImmersion
      (X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding ≫ π) :=
  LocallyRingedSpace.IsOpenImmersion.of_stalk_iso _
    (isOpenEmbedding_restrict_of_isProperlyDiscontinuousOn h U.isOpen hU)

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
-- Comparing the restriction of the ambient space with the affine model needs reducible-transparency
-- defeq checks, as everywhere this tree feeds `IsOpenImmersion.formalScheme`; see `Gluing.lean:48`
-- and `OpenImmersionSourceFormalScheme.lean:86`. The chart morphism is handed to a focused goal for
-- the same reason: the one-shot `refine ⟨R, ‹_›, ‹_›, J, ‹_›, f ≫ …, ⟨z, ?_⟩, ?_⟩` times out at
-- `whnf` even at a million heartbeats.
/-- **The quotient of a formal scheme by a free, properly discontinuous action is a formal scheme,
given that the projection restricts to an open immersion over separating opens.**

Every point of `Q` is `π x` for some `x` (`base_surjective_of_isActionQuotient`); a separating
neighbourhood `U ∋ x` exists by hypothesis; `X|_U` is a formal scheme, so it has an affine chart
`Spf J ⟶ X|_U` through `x`; and composing that with the open immersion `X|_U ⟶ Q` gives the open
immersion out of an affine formal scheme that `IsOpenImmersion.formalScheme` asks for. -/
def formalSchemeOfIsOpenImmersionRestrict (hX : X.LocallyFG) (h : IsActionQuotient a π)
    (hfpd : IsFreeProperlyDiscontinuous a)
    (hoi : ∀ U : Opens X, IsProperlyDiscontinuousOn a (U : Set X) →
      LocallyRingedSpace.IsOpenImmersion
        (X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding ≫ π)) :
    FormalScheme.{u} := by
  refine LocallyRingedSpace.IsOpenImmersion.formalScheme Q fun xbar => ?_
  obtain ⟨x, rfl⟩ := base_surjective_of_isActionQuotient h xbar
  obtain ⟨U, hUopen, hxU, hU⟩ := hfpd x
  set U' : Opens X := ⟨U, hUopen⟩ with hU'
  have := hoi U' hU
  obtain ⟨R, hR, hTR, J, hJ, f, ⟨z, hz⟩, hf⟩ :=
    (X.restrictOpen hX U').exists_openImmersion ⟨x, hxU⟩
  refine ⟨R, hR, hTR, J, hJ, ?_, ?_, ?_⟩
  · exact f ≫ (X.toLocallyRingedSpace.ofRestrict U'.isOpenEmbedding ≫ π)
  · refine ⟨z, ?_⟩
    simp only [LocallyRingedSpace.comp_toHom, PresheafedSpace.comp_base, TopCat.hom_comp,
      ContinuousMap.coe_comp, Function.comp_apply]
    rw [hz]
    rfl
  · exact LocallyRingedSpace.IsOpenImmersion.comp _ _

/-- **The underlying locally ringed space of the quotient formal scheme is the quotient.** True by
construction; recorded so the criterion can be used to *upgrade* an existing quotient rather than
only to produce a new object. -/
@[simp]
theorem formalSchemeOfIsOpenImmersionRestrict_toLocallyRingedSpace (hX : X.LocallyFG)
    (h : IsActionQuotient a π) (hfpd : IsFreeProperlyDiscontinuous a)
    (hoi : ∀ U : Opens X, IsProperlyDiscontinuousOn a (U : Set X) →
      LocallyRingedSpace.IsOpenImmersion
        (X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding ≫ π)) :
    (formalSchemeOfIsOpenImmersionRestrict hX h hfpd hoi).toLocallyRingedSpace = Q :=
  rfl

/-- **The same criterion, phrased with the stalk hypothesis.** This is the exact statement a proof
of "the stalk maps of an action quotient are isomorphisms over a separating open" would discharge,
so that lemma plus this theorem is the whole of the general result. -/
def formalSchemeOfStalkIso (hX : X.LocallyFG) (h : IsActionQuotient a π)
    (hfpd : IsFreeProperlyDiscontinuous a)
    (hstalk : ∀ (U : Opens X), IsProperlyDiscontinuousOn a (U : Set X) →
      ∀ y : (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).toTopCat,
        IsIso ((X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding ≫ π).stalkMap y)) :
    FormalScheme.{u} :=
  formalSchemeOfIsOpenImmersionRestrict hX h hfpd fun U hU =>
    haveI := hstalk U hU
    isOpenImmersion_ofRestrict_comp_of_stalk_iso h hU

/-- The underlying locally ringed space of `formalSchemeOfStalkIso` is the quotient. -/
@[simp]
theorem formalSchemeOfStalkIso_toLocallyRingedSpace (hX : X.LocallyFG) (h : IsActionQuotient a π)
    (hfpd : IsFreeProperlyDiscontinuous a)
    (hstalk : ∀ (U : Opens X), IsProperlyDiscontinuousOn a (U : Set X) →
      ∀ y : (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).toTopCat,
        IsIso ((X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding ≫ π).stalkMap y)) :
    (formalSchemeOfStalkIso hX h hfpd hstalk).toLocallyRingedSpace = Q :=
  rfl

end LocallyRingedSpace

end AlgebraicGeometry
