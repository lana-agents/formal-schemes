import FormalSchemes.ActionQuotient
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Products

set_option linter.style.header false

/-!
# The quotient by a group action, constructed as a coequalizer

`FormalSchemes.ActionQuotient` states the universal property of the quotient `X / G` as an
explicit mediating-morphism + uniqueness pair (`CategoryTheory.IsActionQuotient`), and every value
of it on this tree so far has been *hand-built*: the Tate-curve model `𝔈_q` is exhibited as
`T_inv / ⟨σ²⟩` by gluing the parity map patch by patch (`FormalSchemes.TateQuotientMap`).

This file constructs the quotient **generically**, from colimits that the ambient category already
has. Writing `X_G := ∐_{g : G} X`, the two legs

* `actionQuotientLeft a : X_G ⟶ X`, the copairing of the automorphisms `a g`, and
* `actionQuotientRight G X : X_G ⟶ X`, the copairing of `𝟙 X`

have the property that a morphism `f : X ⟶ Z` coequalizes them exactly when it is invariant
(`isActionInvariant_iff`), because `Sigma.ι _ g ≫ -` reads off the `g`-th component. So the
coequalizer of that pair — when it exists — *is* the quotient, and `IsActionQuotient` for its
projection is the coequalizer's own universal property transported across that equivalence.

## Where this applies, and a correction

The design note of `FormalSchemes.ActionQuotient` says the colimit form was avoided because
"colimits of this shape are not available off the shelf in the target categories
(`LocallyRingedSpace`, `FormalScheme`)". **That is false for `LocallyRingedSpace`**, which has
*all* small colimits: `AlgebraicGeometry.LocallyRingedSpace.instHasColimits`
(`Mathlib/Geometry/RingedSpace/LocallyRingedSpace/HasColimits.lean`), assembled from small
coproducts and coequalizers there. It remains true for `FormalScheme`, which has no colimit API on
this tree at all. Since the actions this project cares about — including the Tate `q^{2ℤ}`-action
`tateInvPeriodSqAction` — are actions on the *locally ringed space* `T_inv.toLocallyRingedSpace`,
the construction below applies to them directly; see `FormalSchemes.TateQuotientColimit`, which
identifies `𝔈_q` with the coequalizer built here.

What that does **not** settle is whether the quotient is again a formal scheme. The coequalizer
exists for every action, free or not; being a formal scheme is a separate statement about the
projection being a local isomorphism, and nothing *here* proves it. It is proved, for free and
properly discontinuous actions, in
`FormalSchemes.FreeActionQuotientFormalScheme`
(`AlgebraicGeometry.LocallyRingedSpace.freeActionQuotientFormalScheme`).

## Main definitions

* `CategoryTheory.actionQuotientLeft` / `CategoryTheory.actionQuotientRight`: the two legs
  `∐_{g : G} X ⟶ X` whose coequalizer is the quotient.
* `CategoryTheory.actionQuotient`: the quotient object, as `coequalizer` of those legs.
* `CategoryTheory.actionQuotientπ`: the quotient projection `X ⟶ X / G`.

## Main results

* `CategoryTheory.isActionInvariant_iff`: invariance is exactly the coequalizer condition.
* `CategoryTheory.isActionQuotient_actionQuotientπ`: **the headline** — the coequalizer projection
  exhibits `actionQuotient a` as `X / G`.
* `CategoryTheory.IsActionQuotient.isoActionQuotient`: any hand-built quotient is canonically
  isomorphic to this one, compatibly with the two projections
  (`IsActionQuotient.comp_isoActionQuotient_hom` / `_inv`).

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

universe v u w

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] {G : Type w} [Monoid G] {X : C}

section Legs

variable [HasCoproduct fun _ : G => X]

/-- **The action leg** `∐_{g : G} X ⟶ X`: on the `g`-th summand it is the automorphism `a g`. -/
def actionQuotientLeft (a : G →* Aut X) : (∐ fun _ : G => X) ⟶ X :=
  Sigma.desc fun g => (a g).hom

/-- **The constant leg** `∐_{g : G} X ⟶ X`: the identity on every summand. It does not depend on
the action, only on the index type. -/
def actionQuotientRight (G : Type w) (X : C) [HasCoproduct fun _ : G => X] :
    (∐ fun _ : G => X) ⟶ X :=
  Sigma.desc fun _ => 𝟙 X

@[reassoc (attr := simp)]
theorem ι_actionQuotientLeft (a : G →* Aut X) (g : G) :
    Sigma.ι (fun _ : G => X) g ≫ actionQuotientLeft a = (a g).hom :=
  Sigma.ι_desc _ _

omit [Monoid G] in
@[reassoc (attr := simp)]
theorem ι_actionQuotientRight (g : G) :
    Sigma.ι (fun _ : G => X) g ≫ actionQuotientRight G X = 𝟙 X :=
  Sigma.ι_desc _ _

/-- **Invariance is the coequalizer condition.** A morphism out of `X` is invariant under `a`
exactly when it coequalizes the two legs: testing the equation against `Sigma.ι _ g` reads off the
`g`-th component, which is `(a g).hom ≫ f = f`. -/
theorem isActionInvariant_iff (a : G →* Aut X) {Z : C} (f : X ⟶ Z) :
    IsActionInvariant a f ↔ actionQuotientLeft a ≫ f = actionQuotientRight G X ≫ f := by
  constructor
  · intro h
    refine Sigma.hom_ext _ _ fun g => ?_
    rw [ι_actionQuotientLeft_assoc, ι_actionQuotientRight_assoc, h g]
  · intro h g
    have hg := Sigma.ι (fun _ : G => X) g ≫= h
    rwa [ι_actionQuotientLeft_assoc, ι_actionQuotientRight_assoc] at hg

end Legs

section Quotient

variable (a : G →* Aut X) [HasCoproduct fun _ : G => X]
  [HasCoequalizer (actionQuotientLeft a) (actionQuotientRight G X)]

/-- **The quotient `X / G`**, as the coequalizer of the action leg and the constant leg. -/
def actionQuotient : C :=
  coequalizer (actionQuotientLeft a) (actionQuotientRight G X)

/-- **The quotient projection** `X ⟶ X / G`. -/
def actionQuotientπ : X ⟶ actionQuotient a :=
  coequalizer.π _ _

/-- **The coequalizer is the quotient.** Each field is the corresponding piece of the coequalizer's
universal property, translated along `isActionInvariant_iff`. -/
def isActionQuotient_actionQuotientπ : IsActionQuotient a (actionQuotientπ a) where
  isInvariant := (isActionInvariant_iff a _).mpr (coequalizer.condition _ _)
  desc _ hf := coequalizer.desc _ ((isActionInvariant_iff a _).mp hf)
  fac _ _ := coequalizer.π_desc _ _
  uniq _ _ _ hm := coequalizer.hom_ext (by rw [coequalizer.π_desc]; exact hm)

end Quotient

section Uniqueness

variable {a : G →* Aut X} [HasCoproduct fun _ : G => X]
  [HasCoequalizer (actionQuotientLeft a) (actionQuotientRight G X)]

/-- **Any hand-built quotient is this one.** A value of `IsActionQuotient a π` is canonically
isomorphic to the coequalizer. -/
def IsActionQuotient.isoActionQuotient {Q : C} {π : X ⟶ Q} (h : IsActionQuotient a π) :
    Q ≅ actionQuotient a :=
  h.uniqueUpToIso (isActionQuotient_actionQuotientπ a)

/-- The canonical isomorphism carries the hand-built projection to the coequalizer projection. -/
theorem IsActionQuotient.comp_isoActionQuotient_hom {Q : C} {π : X ⟶ Q}
    (h : IsActionQuotient a π) : π ≫ h.isoActionQuotient.hom = actionQuotientπ a :=
  h.π_comp_uniqueUpToIso_hom (isActionQuotient_actionQuotientπ a)

/-- The inverse of the canonical isomorphism carries the coequalizer projection to the hand-built
one. -/
theorem IsActionQuotient.comp_isoActionQuotient_inv {Q : C} {π : X ⟶ Q}
    (h : IsActionQuotient a π) : actionQuotientπ a ≫ h.isoActionQuotient.inv = π :=
  h.π_comp_uniqueUpToIso_inv (isActionQuotient_actionQuotientπ a)

end Uniqueness

end CategoryTheory
