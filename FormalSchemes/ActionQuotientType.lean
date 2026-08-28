import FormalSchemes.ActionQuotientFunctor

set_option linter.style.header false

/-!
# The quotient of a type by a group action is the orbit set

`FormalSchemes.ActionQuotient` states the universal property of `X / G` abstractly and
`FormalSchemes.ActionQuotientColimit` builds an object satisfying it as a coequalizer. Neither says
what the quotient *is*. In `Type` it is the orbit set, and this file proves that: the projection
`X ⟶ X / ~` onto the quotient by the orbit relation is a `CategoryTheory.IsActionQuotient`, and
therefore — by uniqueness of quotients — *every* action quotient in `Type` is surjective with
fibres the orbits.

That second consequence is the useful one. Combined with
`CategoryTheory.IsActionQuotient.map`, it computes the underlying set of a quotient formed in any
category admitting a set-valued functor that preserves the two colimits involved; see
`FormalSchemes.ActionQuotientCarrier` for the locally-ringed-space case.

## Main definitions

* `CategoryTheory.actionOrbitSetoid`: the orbit relation `x ~ y ↔ ∃ g, a g x = y` of an action of a
  **group** on a type, as a `Setoid`. Reflexivity, symmetry and transitivity are `1`, `g⁻¹` and
  `g * h` respectively — this is where being a group rather than a monoid is used.

## Main results

* `CategoryTheory.isActionQuotient_orbitMk`: the orbit set is the quotient.
* `CategoryTheory.IsActionQuotient.isoOrbitQuotient`: hence any quotient of `X` by `a` in `Type` is
  canonically isomorphic to the orbit set, compatibly with the projections.
* `CategoryTheory.IsActionQuotient.surjective` and
  `CategoryTheory.IsActionQuotient.apply_eq_iff`: **the computation** — an action quotient
  projection is surjective, and identifies two points exactly when they lie in the same orbit.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
-/

noncomputable section

universe u w

namespace CategoryTheory

open Category

variable {G : Type w} [Group G] {X : Type u} (a : G →* Aut X)

/-! ### The orbit relation -/

theorem action_one_apply (x : X) : (a (1 : G)).hom x = x := by
  rw [map_one]; rfl

theorem action_mul_apply (g h : G) (x : X) :
    (a (g * h)).hom x = (a g).hom ((a h).hom x) := by
  rw [map_mul]; rfl

theorem action_inv_apply (g : G) (x : X) : (a g⁻¹).hom ((a g).hom x) = x := by
  rw [← action_mul_apply, inv_mul_cancel, action_one_apply]

/-- **The orbit relation of an action by automorphisms of a type**, as a `Setoid`: `x ~ y` when
some `a g` carries `x` to `y`.

That this is an equivalence relation is exactly the group structure of `G`: reflexivity is `g = 1`,
symmetry is `g⁻¹` and transitivity is a product. For a mere monoid the relation is only reflexive
and transitive, and the quotient below would be the wrong object. -/
def actionOrbitSetoid : Setoid X where
  r x y := ∃ g : G, (a g).hom x = y
  iseqv :=
    { refl x := ⟨1, action_one_apply a x⟩
      symm := by
        rintro x y ⟨g, rfl⟩
        exact ⟨g⁻¹, action_inv_apply a g x⟩
      trans := by
        rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
        exact ⟨h * g, by rw [action_mul_apply]⟩ }

theorem actionOrbitSetoid_iff (x y : X) :
    (actionOrbitSetoid a) x y ↔ ∃ g : G, (a g).hom x = y :=
  Iff.rfl

/-! ### The orbit set is the quotient -/

/-- **The orbit set is the quotient of `X` by `a`.** `Quotient.mk` is invariant because `x` and
`(a g).hom x` lie in the same orbit; an invariant `f` factors through it as `Quotient.lift f`, and
uniqueness is `Quotient.ind`. -/
def isActionQuotient_orbitMk :
    IsActionQuotient a (↾(Quotient.mk (actionOrbitSetoid a)) :
      X ⟶ Quotient (actionOrbitSetoid a)) where
  isInvariant g := by
    ext x
    exact Quotient.sound ⟨g⁻¹, action_inv_apply a g x⟩
  desc f hf := ↾(Quotient.lift f (by
    rintro x y ⟨g, rfl⟩
    exact (congrArg (fun u : X ⟶ _ => u x) (hf g)).symm))
  fac _ _ := rfl
  uniq _ _ m hm := by
    ext q
    induction q using Quotient.ind with
    | _ x => exact congrArg (fun u : X ⟶ _ => u x) hm

/-! ### What every action quotient in `Type` looks like -/

variable {a}
variable {Q : Type u} {π : X ⟶ Q} (h : IsActionQuotient a π)

/-- **Any quotient of `X` by `a` in `Type` is the orbit set.** -/
def IsActionQuotient.isoOrbitQuotient : Q ≅ Quotient (actionOrbitSetoid a) :=
  h.uniqueUpToIso (isActionQuotient_orbitMk a)

theorem IsActionQuotient.comp_isoOrbitQuotient_hom :
    π ≫ h.isoOrbitQuotient.hom = ↾(Quotient.mk (actionOrbitSetoid a)) :=
  h.π_comp_uniqueUpToIso_hom _

theorem IsActionQuotient.isoOrbitQuotient_hom_apply (x : X) :
    h.isoOrbitQuotient.hom (π x) = Quotient.mk (actionOrbitSetoid a) x :=
  congrArg (fun u : X ⟶ _ => u x) h.comp_isoOrbitQuotient_hom

theorem IsActionQuotient.isoOrbitQuotient_hom_bijective :
    Function.Bijective h.isoOrbitQuotient.hom :=
  (isIso_iff_bijective _).mp inferInstance

include h in
/-- **An action-quotient projection is surjective**: every point of the quotient is the image of a
point of `X`. -/
theorem IsActionQuotient.surjective : Function.Surjective π := fun q => by
  obtain ⟨x, hx⟩ := Quotient.exists_rep (h.isoOrbitQuotient.hom q)
  exact ⟨x, h.isoOrbitQuotient_hom_bijective.1
    ((h.isoOrbitQuotient_hom_apply x).trans hx)⟩

include h in
/-- **The fibres of an action-quotient projection are exactly the orbits.** -/
theorem IsActionQuotient.apply_eq_iff (x y : X) :
    π x = π y ↔ ∃ g : G, (a g).hom x = y := by
  constructor
  · intro hxy
    have hq : Quotient.mk (actionOrbitSetoid a) x = Quotient.mk (actionOrbitSetoid a) y := by
      rw [← h.isoOrbitQuotient_hom_apply, ← h.isoOrbitQuotient_hom_apply, hxy]
    exact Quotient.exact hq
  · rintro ⟨g, rfl⟩
    exact (congrArg (fun u : X ⟶ _ => u x) (h.isInvariant g)).symm

end CategoryTheory
