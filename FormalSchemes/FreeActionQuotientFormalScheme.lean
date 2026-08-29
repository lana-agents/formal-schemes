import FormalSchemes.ActionQuotientStalk
import FormalSchemes.ActionQuotientFormalScheme
import Mathlib.Algebra.Group.Shrink

set_option linter.style.header false

/-!
# The quotient of a formal scheme by a free, properly discontinuous action is a formal scheme

This closes the chain begun in `FormalSchemes.ActionQuotientColimit`. The pieces were:

| what | where |
| :-- | :-- |
| the quotient exists, as a coequalizer | `ActionQuotientColimit` |
| its underlying space is the orbit space | `ActionQuotientCarrier` |
| `π.base` is open and restricts to an open embedding of a separating open | `ActionDiscontinuous` |
| its sections are the invariant sections | `ActionQuotientInvariantSections` |
| the stalk maps are isomorphisms over a separating open | `ActionQuotientStalk` |
| the two halves make it a formal scheme | `ActionQuotientFormalScheme` |

Only the last row's hypothesis was open, and this file discharges it: it transports
`CategoryTheory.isIso_stalkMap_actionQuotientπ` from the coequalizer projection to an arbitrary
projection exhibiting the quotient, from a group in `Type u` to any `Small.{u}` group, and from `π`
to `X|_U ⟶ X / G`, which is the shape `formalSchemeOfStalkIso` consumes.

## The two transports, and why neither is a special case of the other

* **Along the canonical isomorphism.** `IsActionQuotient.comp_isoActionQuotient_hom` says
  `π ≫ e.hom = actionQuotientπ a` for the canonical `e`, so the stalk map of the coequalizer
  projection factors through the stalk map of `π`; an isomorphism's stalk map is an isomorphism, so
  `IsIso.of_isIso_comp_left` returns the factor.
* **Along `Shrink`.** The sections description of the quotient needs the group to live in the same
  universe as the space, because it computes a colimit over `Discrete G`. Nothing else does:
  `IsActionInvariant`, `IsActionQuotient` and `IsProperlyDiscontinuousOn` are all statements
  quantified over the *elements* of `G`, so they transport along `Shrink.mulEquiv` verbatim, and
  the quotient object does not change — it is the same `π`.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_of_isProperlyDiscontinuousOn`: the stalk
  maps of any projection exhibiting the quotient are isomorphisms over a separating open, for any
  `Small.{u}` group.
* `AlgebraicGeometry.LocallyRingedSpace.isIso_stalkMap_ofRestrict_comp`: the same for the
  restriction of the projection to a separating open.
* `AlgebraicGeometry.LocallyRingedSpace.freeActionQuotientFormalScheme`: **the theorem** — the
  quotient of a locally finitely generated formal scheme by a free, properly discontinuous action
  of a small group is a formal scheme, with `…_toLocallyRingedSpace` recording that it is the
  quotient itself.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace Opposite

universe v u

namespace AlgebraicGeometry

namespace LocallyRingedSpace

section Transport

variable {X : LocallyRingedSpace.{u}} {G : Type u} [Group G] {a : G →* Aut X}
variable [HasCoproduct fun _ : G => X]
  [HasCoequalizer (actionQuotientLeft a) (actionQuotientRight G X)]
variable {Q : LocallyRingedSpace.{u}} {π : X ⟶ Q}

/-- **The stalk maps of an arbitrary quotient projection are isomorphisms over a separating
open.** The coequalizer projection factors as `π` followed by the canonical isomorphism, so this is
`CategoryTheory.isIso_stalkMap_actionQuotientπ` with the isomorphism's stalk map cancelled. -/
theorem isIso_stalkMap_of_isProperlyDiscontinuousOn_of_type (h : IsActionQuotient a π)
    {U : Opens X.toTopCat} (hU : IsProperlyDiscontinuousOn a (U : Set X)) {x : X} (hx : x ∈ U) :
    IsIso (π.stalkMap x) := by
  have key : (π ≫ h.isoActionQuotient.hom).stalkMap x =
      h.isoActionQuotient.hom.stalkMap (π.base x) ≫ π.stalkMap x :=
    LocallyRingedSpace.stalkMap_comp π h.isoActionQuotient.hom x
  haveI h1 : IsIso ((π ≫ h.isoActionQuotient.hom).stalkMap x) := by
    rw [h.comp_isoActionQuotient_hom]
    exact isIso_stalkMap_actionQuotientπ a hU hx
  haveI h2 : IsIso (h.isoActionQuotient.hom.stalkMap (π.base x) ≫ π.stalkMap x) := key ▸ h1
  exact IsIso.of_isIso_comp_left (h.isoActionQuotient.hom.stalkMap (π.base x)) (π.stalkMap x)

end Transport

section Shrink

variable {X : LocallyRingedSpace.{u}} {G : Type v} [Group G] [Small.{u} G] {a : G →* Aut X}

/-- **The action read on `Shrink G`.** The quotient does not change: `IsActionInvariant`,
`IsActionQuotient` and `IsProperlyDiscontinuousOn` are quantified over the elements of the group,
and `Shrink.mulEquiv` is a bijection on elements. -/
def shrinkAction (a : G →* Aut X) : Shrink.{u} G →* Aut X :=
  a.comp (Shrink.mulEquiv (α := G)).toMonoidHom

/-- The shrunk action at a group element. -/
theorem shrinkAction_apply (a : G →* Aut X) (g : Shrink.{u} G) :
    shrinkAction a g = a (Shrink.mulEquiv g) :=
  rfl

/-- **Invariance does not see the shrinking**: `Shrink.mulEquiv` is a bijection on elements, and
invariance is quantified over elements. -/
theorem isActionInvariant_shrinkAction_iff {Z : LocallyRingedSpace.{u}} (f : X ⟶ Z) :
    IsActionInvariant (shrinkAction a) f ↔ IsActionInvariant a f := by
  refine ⟨fun hf g => ?_, fun hf g => hf _⟩
  simpa [shrinkAction_apply] using hf ((Shrink.mulEquiv (α := G)).symm g)

/-- The universal property transports to the shrunk action. -/
def isActionQuotient_shrinkAction {Q : LocallyRingedSpace.{u}} {π : X ⟶ Q}
    (h : IsActionQuotient a π) : IsActionQuotient (shrinkAction a) π where
  isInvariant _ := h.isInvariant _
  desc f hf := h.desc f ((isActionInvariant_shrinkAction_iff f).mp hf)
  fac f _ := h.fac f _
  uniq f _ m hm := h.uniq f _ m hm

/-- Proper discontinuity does not see the shrinking either. -/
theorem isProperlyDiscontinuousOn_shrinkAction {U : Set X}
    (hU : IsProperlyDiscontinuousOn a U) : IsProperlyDiscontinuousOn (shrinkAction a) U := by
  intro g hg
  refine hU (Shrink.mulEquiv g) fun hc => hg ?_
  exact (MulEquiv.map_eq_one_iff _).mp hc

variable {Q : LocallyRingedSpace.{u}} {π : X ⟶ Q}

/-- **The stalk maps of a quotient projection are isomorphisms over a separating open**, for any
group small relative to the space. This is the statement
`AlgebraicGeometry.LocallyRingedSpace.formalSchemeOfStalkIso` asks for. -/
theorem isIso_stalkMap_of_isProperlyDiscontinuousOn (h : IsActionQuotient a π)
    {U : Opens X.toTopCat} (hU : IsProperlyDiscontinuousOn a (U : Set X)) {x : X} (hx : x ∈ U) :
    IsIso (π.stalkMap x) :=
  isIso_stalkMap_of_isProperlyDiscontinuousOn_of_type (isActionQuotient_shrinkAction h)
    (isProperlyDiscontinuousOn_shrinkAction hU) hx

end Shrink

section FormalSchemeQuotient

variable {X : FormalScheme.{u}} {G : Type v} [Group G] [Small.{u} G]
variable {a : G →* Aut X.toLocallyRingedSpace}
variable {Q : LocallyRingedSpace.{u}} {π : X.toLocallyRingedSpace ⟶ Q}

/-- **The restriction of the projection to a separating open has isomorphic stalk maps.** The
composite's stalk map factors as the projection's followed by the restriction's, and the latter is
an isomorphism for every open immersion. -/
theorem isIso_stalkMap_ofRestrict_comp (h : IsActionQuotient a π) (U : Opens X)
    (hU : IsProperlyDiscontinuousOn a (U : Set X))
    (y : (X.toLocallyRingedSpace.restrict U.isOpenEmbedding).toTopCat) :
    IsIso ((X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding ≫ π).stalkMap y) := by
  have hπ : IsIso (π.stalkMap ((X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding).base y)) :=
    isIso_stalkMap_of_isProperlyDiscontinuousOn h (U := U) hU y.2
  rw [LocallyRingedSpace.stalkMap_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hπ (ofRestrict_stalkMap_isIso _ _ _)

/-- **The quotient of a locally finitely generated formal scheme by a free, properly discontinuous
action of a small group is a formal scheme.** Every hypothesis of
`formalSchemeOfStalkIso` is now discharged.

`LocallyFG` is not removable: the affine chart inside a separating open is produced by
`FormalScheme.restrictOpen`, which carries it. -/
def freeActionQuotientFormalScheme (hX : X.LocallyFG) (h : IsActionQuotient a π)
    (hfpd : IsFreeProperlyDiscontinuous a) : FormalScheme.{u} :=
  formalSchemeOfStalkIso hX h hfpd fun U hU y => isIso_stalkMap_ofRestrict_comp h U hU y

/-- **The formal scheme produced is the quotient itself**, not a look-alike: its underlying locally
ringed space is `Q` on the nose. -/
@[simp]
theorem freeActionQuotientFormalScheme_toLocallyRingedSpace (hX : X.LocallyFG)
    (h : IsActionQuotient a π) (hfpd : IsFreeProperlyDiscontinuous a) :
    (freeActionQuotientFormalScheme hX h hfpd).toLocallyRingedSpace = Q :=
  rfl

end FormalSchemeQuotient

end LocallyRingedSpace

end AlgebraicGeometry
