import Mathlib.CategoryTheory.Endomorphism

set_option linter.style.header false

/-!
# The quotient of an object by a group action: the universal property

This file develops, in an arbitrary category `C`, the universal property of the **quotient of an
object `X` by an action of a group (or monoid) `G` by automorphisms**, packaged as an explicit
mediating-morphism + uniqueness pair. It is the reusable categorical interface behind the quotient
of a formal scheme by a free, properly discontinuous group action (issue 224 / EGA I §10.6; the
motivating instance is `G = ℤ` acting on the inversion-glued Tate chain `T_inv` by the `q^ℤ`
shift `σ`, whose quotient by the *square* `σ²` is the Tate-curve formal model
`𝔈_q = T_inv / q^{2ℤ}` — see the period note in `FormalSchemes.TateCurveModel`).

An action of `G` on `X` by automorphisms is a monoid homomorphism `a : G →* Aut X`.

## Main definitions

* `CategoryTheory.IsActionInvariant a f`: a morphism `f : X ⟶ Z` is *invariant* under `a` when
  `(a g).hom ≫ f = f` for every `g : G`.
* `CategoryTheory.IsActionQuotient a π`: `π : X ⟶ Q` exhibits `Q` as the quotient `X / G`; i.e. `π`
  is invariant and *initial among invariant morphisms* — every invariant `f : X ⟶ Z` factors
  uniquely through `π`.

## Main results

* `CategoryTheory.IsActionQuotient.hom_ext`: a quotient projection is epimorphic *among morphisms
  out of the quotient* — two maps `Q ⟶ Z` agreeing after `π` are equal.
* `CategoryTheory.IsActionQuotient.uniqueUpToIso`: the quotient object is unique up to a (canonical)
  isomorphism compatible with the two projections.

## Design notes

The universal property is phrased as the explicit mediating-morphism + uniqueness pair rather than
as a `CategoryTheory.Limits.IsColimit`. Categorically these agree: `π` is a colimit cocone of the
action functor `CategoryTheory.SingleObj G ⥤ C` (equivalently the joint coequalizer of the family
`{(a g).hom, 𝟙 X}`), and for `C = Type` this colimit is the orbit quotient
(`CategoryTheory.Limits.Types.colimitEquivQuotient`). The explicit form is chosen because colimits
of this shape are not available off the shelf in the target categories (`LocallyRingedSpace`,
`FormalScheme`), and it is exactly the data a hand-built quotient supplies.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

universe v u w

namespace CategoryTheory

open Category

variable {C : Type u} [Category.{v} C] {G : Type w} [Monoid G] {X : C}

/-- A morphism `f : X ⟶ Z` is **invariant** under the action `a : G →* Aut X` when precomposition
with every automorphism `a g` leaves it unchanged: `(a g).hom ≫ f = f`. -/
def IsActionInvariant (a : G →* Aut X) {Z : C} (f : X ⟶ Z) : Prop :=
  ∀ g : G, (a g).hom ≫ f = f

namespace IsActionInvariant

variable {a : G →* Aut X}

/-- Postcomposing an invariant morphism with an arbitrary morphism preserves invariance. -/
theorem comp {Z W : C} {f : X ⟶ Z} (hf : IsActionInvariant a f) (h : Z ⟶ W) :
    IsActionInvariant a (f ≫ h) := fun g => by rw [← assoc, hf g]

end IsActionInvariant

variable (a : G →* Aut X)

/-- `IsActionQuotient a π` witnesses that `π : X ⟶ Q` exhibits `Q` as the **quotient of `X` by the
action `a`**: `π` is invariant, and it is *initial among invariant morphisms* — every invariant
`f : X ⟶ Z` factors as `f = π ≫ desc f hf` through a morphism `desc f hf : Q ⟶ Z` that is the unique
factorisation of `f` through `π`.

This is the explicit form of the universal property; see the module docstring for the colimit
interpretation. -/
structure IsActionQuotient {Q : C} (π : X ⟶ Q) where
  /-- The quotient projection is invariant under the action. -/
  isInvariant : IsActionInvariant a π
  /-- The mediating morphism induced by an invariant morphism `f`. -/
  desc {Z : C} (f : X ⟶ Z) (hf : IsActionInvariant a f) : Q ⟶ Z
  /-- The mediating morphism factors `f` through the projection. -/
  fac {Z : C} (f : X ⟶ Z) (hf : IsActionInvariant a f) : π ≫ desc f hf = f
  /-- The mediating morphism is the unique factorisation of `f` through the projection. -/
  uniq {Z : C} (f : X ⟶ Z) (hf : IsActionInvariant a f) (m : Q ⟶ Z) (hm : π ≫ m = f) :
    m = desc f hf

namespace IsActionQuotient

variable {a}
variable {Q : C} {π : X ⟶ Q}

/-- **Morphisms out of the quotient are determined by their precomposition with the projection.**
Because `π ≫ m` is automatically invariant, `uniq` applies to both maps and forces them equal. -/
theorem hom_ext (hπ : IsActionQuotient a π) {Z : C} {m₁ m₂ : Q ⟶ Z}
    (h : π ≫ m₁ = π ≫ m₂) : m₁ = m₂ := by
  have hinv : IsActionInvariant a (π ≫ m₁) := hπ.isInvariant.comp m₁
  rw [hπ.uniq (π ≫ m₁) hinv m₁ rfl, hπ.uniq (π ≫ m₁) hinv m₂ h.symm]

section UniqueUpToIso

variable {Q₁ Q₂ : C} {π₁ : X ⟶ Q₁} {π₂ : X ⟶ Q₂}
  (h₁ : IsActionQuotient a π₁) (h₂ : IsActionQuotient a π₂)

/-- **The quotient object is unique up to isomorphism.** Two quotient projections `π₁ : X ⟶ Q₁` and
`π₂ : X ⟶ Q₂` for the same action induce mutually inverse mediating morphisms `Q₁ ≅ Q₂`. -/
def uniqueUpToIso : Q₁ ≅ Q₂ where
  hom := h₁.desc π₂ h₂.isInvariant
  inv := h₂.desc π₁ h₁.isInvariant
  hom_inv_id := by
    apply h₁.hom_ext
    rw [← assoc, h₁.fac π₂ h₂.isInvariant, h₂.fac π₁ h₁.isInvariant, comp_id]
  inv_hom_id := by
    apply h₂.hom_ext
    rw [← assoc, h₂.fac π₁ h₁.isInvariant, h₁.fac π₂ h₂.isInvariant, comp_id]

/-- The canonical isomorphism `uniqueUpToIso` intertwines the two quotient projections. -/
theorem π_comp_uniqueUpToIso_hom : π₁ ≫ (uniqueUpToIso h₁ h₂).hom = π₂ :=
  h₁.fac π₂ h₂.isInvariant

/-- The inverse of the canonical isomorphism `uniqueUpToIso` intertwines the two projections. -/
theorem π_comp_uniqueUpToIso_inv : π₂ ≫ (uniqueUpToIso h₁ h₂).inv = π₁ :=
  h₂.fac π₁ h₁.isInvariant

end UniqueUpToIso

end IsActionQuotient

end CategoryTheory
