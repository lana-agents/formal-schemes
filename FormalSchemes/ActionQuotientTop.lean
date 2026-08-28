import FormalSchemes.ActionQuotientType
import Mathlib.Topology.Category.TopCat.Basic

set_option linter.style.header false

/-!
# The quotient of a topological space by a group action is the orbit space

`FormalSchemes.ActionQuotientType` identifies every action quotient in `Type` with the orbit set.
This file does the same one level up: an action quotient in `TopCat` carries the *quotient
topology*, so its projection is a `Topology.IsQuotientMap` and the quotient object is the orbit
space.

The proof is the same shape as in `Type`: the orbit space carries an `IsActionQuotient`
(`Quotient.lift` of a continuous invariant map is continuous), and uniqueness of quotients turns
that into a homeomorphism with any other quotient.

## Main definitions

* `CategoryTheory.topActionOrbitSpace`: the orbit space of an action on a topological space, i.e.
  the orbit set of `FormalSchemes.ActionQuotientType` with the quotient topology.

## Main results

* `CategoryTheory.isActionQuotient_topOrbitMk`: the orbit space is the quotient in `TopCat`.
* `CategoryTheory.IsActionQuotient.isQuotientMap`: **the topological statement** — the projection
  of any action quotient of topological spaces is a quotient map. With
  `CategoryTheory.IsActionQuotient.apply_eq_iff` this says the quotient object *is* the orbit space
  and not merely a continuous bijective image of it.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
-/

noncomputable section

universe u w

namespace CategoryTheory

open Category Topology

variable {G : Type w} [Group G] {X : TopCat.{u}} (a : G →* Aut X)

/-- The orbit relation of an action on a topological space: the orbit relation of the induced
action on its points. -/
abbrev topActionOrbitSetoid : Setoid ((forget TopCat).obj X) :=
  actionOrbitSetoid ((forget TopCat).mapAction a)

/-- **The orbit space** of an action on a topological space: the orbit set with the quotient
topology. -/
abbrev topActionOrbitSpace : TopCat.{u} :=
  TopCat.of (Quotient (topActionOrbitSetoid a))

/-- The projection onto the orbit space. -/
def topOrbitMk : X ⟶ topActionOrbitSpace a :=
  TopCat.ofHom ⟨Quotient.mk (topActionOrbitSetoid a), continuous_quotient_mk'⟩

/-- **The orbit space is the quotient of `X` by `a` in `TopCat`.** The three fields are the `Type`
ones of `FormalSchemes.ActionQuotientType` together with the continuity of `Quotient.lift`. -/
def isActionQuotient_topOrbitMk : IsActionQuotient a (topOrbitMk a) where
  isInvariant g := by
    ext x
    exact Quotient.sound ⟨g⁻¹, action_inv_apply ((forget TopCat).mapAction a) g x⟩
  desc f hf := TopCat.ofHom
    ⟨Quotient.lift f (by
        rintro x y ⟨g, rfl⟩
        exact (congrArg (fun u : X ⟶ _ => u x) (hf g)).symm),
      continuous_quot_lift _ f.hom.continuous⟩
  fac _ _ := rfl
  uniq _ _ m hm := by
    ext q
    induction q using Quotient.ind with
    | _ x => exact congrArg (fun u : X ⟶ _ => u x) hm

variable {a}
variable {Q : TopCat.{u}} {π : X ⟶ Q} (h : IsActionQuotient a π)

/-- Any quotient of `X` by `a` in `TopCat` is the orbit space. -/
def IsActionQuotient.isoTopOrbitQuotient : Q ≅ topActionOrbitSpace a :=
  h.uniqueUpToIso (isActionQuotient_topOrbitMk a)

theorem IsActionQuotient.topOrbitMk_comp_isoTopOrbitQuotient_inv :
    topOrbitMk a ≫ h.isoTopOrbitQuotient.inv = π :=
  h.π_comp_uniqueUpToIso_inv _

include h in
/-- **The projection of an action quotient of topological spaces is a quotient map**: the quotient
object carries the quotient topology, not merely a coarser one making `π` continuous. -/
theorem IsActionQuotient.isQuotientMap : IsQuotientMap π := by
  have key : ⇑h.isoTopOrbitQuotient.inv ∘ Quotient.mk (topActionOrbitSetoid a) = ⇑π := by
    ext x
    exact congrArg (fun u : X ⟶ _ => u x) h.topOrbitMk_comp_isoTopOrbitQuotient_inv
  rw [← key]
  exact IsQuotientMap.comp
    (TopCat.homeoOfIso h.isoTopOrbitQuotient).symm.isQuotientMap isQuotientMap_quot_mk

end CategoryTheory
