import FormalSchemes.OpenCover
import FormalSchemes.TopFiniteType

set_option linter.style.header false

/-!
# Formal schemes topologically of finite type over a base

Fix a base adic ring `(R, I)`. Issue 66 built the *affine* layer: an `R`-algebra `A` is
topologically of finite type (tf-type) if it is a continuous quotient of a restricted power
series ring `R{X₁, …, Xₙ}` (`FormalSchemes.TopFiniteType`, `IsTopologicallyFiniteType`), so
`Spf A` is an affine formal scheme over `Spf R`. This file lifts that to the *global* notion,
using the open-cover scaffold of `FormalSchemes.OpenCover`: a formal scheme is **locally
topologically of finite type** over `(R, I)` when it admits an open cover by affine formal
schemes each of which is `Spf` of a tf-type `R`-algebra. This mirrors
`AlgebraicGeometry`'s locally-of-finite-type morphism property (EGA I, 10.13), in the
object-level form the Tate construction consumes.

## Main definitions

* `FormalScheme.IsAffineTopFiniteType R I Y`: the formal scheme `Y` is isomorphic to `Spf L`
  for some tf-type `R`-algebra `A` with ideal of definition `L`.
* `FormalScheme.IsLocallyTopFiniteType R I X`: `X` admits an open cover whose pieces are all
  affine tf-type over `(R, I)`.

## Main results

* `IsTopologicallyFiniteType.isAffineTopFiniteType`: `Spf L` of a tf-type algebra is affine
  tf-type — the affine model is an instance of the predicate.
* `IsAffineTopFiniteType.of_iso`: affine tf-type is invariant under isomorphism of formal
  schemes.
* `IsAffineTopFiniteType.isLocallyTopFiniteType`: affine tf-type schemes are locally tf-type
  (the one-piece cover by the identity), hence `Spf L` of a tf-type algebra is locally tf-type.
* `IsLocallyTopFiniteType.of_iso`: the global predicate is invariant under isomorphism.

## Remaining follow-up

The *relative* refinement — packaging a structural morphism `X ⟶ Spf R` and demanding the
cover maps commute with it (so `X` is genuinely tf-type *over* `Spf R` as a morphism, EGA I
10.13) — is left to follow-up, once fibre products / a morphism-property layer for formal
schemes exist. The predicates here record the object-level notion literally requested by the
issue ("an open affine cover whose pieces are `Spf` of tf-type `R`-algebras").

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7–8.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.13.
-/

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FormalScheme

variable (R : Type u) [CommRing R] (I : Ideal R)

/-- A formal scheme `Y` is **affine topologically of finite type** over the base `(R, I)` if it
is isomorphic to the affine formal scheme `Spf L` of some `R`-algebra `A` topologically of
finite type over `(R, I)`, with ideal of definition `L`. -/
def IsAffineTopFiniteType (Y : FormalScheme.{u}) : Prop :=
  ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : Algebra R A)
    (L : Ideal A) (_ : IsAdicRing L),
    IsTopologicallyFiniteType R I A L ∧ Nonempty (Y ≅ FormalScheme.Spf L)

/-- A formal scheme `X` is **locally topologically of finite type** over the base `(R, I)` if it
admits an open cover whose pieces are all affine tf-type over `(R, I)` (i.e. `Spf` of a tf-type
`R`-algebra). This is the object-level analogue of `AlgebraicGeometry`'s
locally-of-finite-type. -/
def IsLocallyTopFiniteType (X : FormalScheme.{u}) : Prop :=
  ∃ 𝒰 : OpenCover X, ∀ j, IsAffineTopFiniteType R I (𝒰.obj j)

variable {R I}

/-- The affine formal scheme `Spf L` of a tf-type algebra is affine tf-type over `(R, I)`. -/
theorem _root_.AlgebraicGeometry.IsTopologicallyFiniteType.isAffineTopFiniteType
    {A : Type u} [CommRing A] [TopologicalSpace A] [Algebra R A] {L : Ideal A} [IsAdicRing L]
    (h : IsTopologicallyFiniteType R I A L) :
    IsAffineTopFiniteType R I (FormalScheme.Spf L) :=
  ⟨A, inferInstance, inferInstance, inferInstance, L, inferInstance, h,
    ⟨Iso.refl (FormalScheme.Spf L)⟩⟩

/-- Affine tf-type is invariant under isomorphism of formal schemes. -/
theorem IsAffineTopFiniteType.of_iso {Y Y' : FormalScheme.{u}}
    (h : IsAffineTopFiniteType R I Y) (e : Y' ≅ Y) : IsAffineTopFiniteType R I Y' := by
  obtain ⟨A, _, _, _, L, _, hA, ⟨f⟩⟩ := h
  exact ⟨A, inferInstance, inferInstance, inferInstance, L, inferInstance, hA, ⟨e ≪≫ f⟩⟩

/-- The one-object open cover of a formal scheme by itself, along the identity (an open
immersion, being an isomorphism). -/
def _root_.AlgebraicGeometry.FormalScheme.OpenCover.self (X : FormalScheme.{u}) :
    OpenCover X where
  J := PUnit.{u + 1}
  obj _ := X
  map _ := 𝟙 X
  f _ := PUnit.unit
  covers x := ⟨x, rfl⟩
  isOpenImmersion _ := inferInstanceAs
    (LocallyRingedSpace.IsOpenImmersion (𝟙 X.toLocallyRingedSpace))

/-- An affine tf-type formal scheme is locally tf-type: it is covered by itself. -/
theorem IsAffineTopFiniteType.isLocallyTopFiniteType {Y : FormalScheme.{u}}
    (h : IsAffineTopFiniteType R I Y) : IsLocallyTopFiniteType R I Y :=
  ⟨OpenCover.self Y, fun _ => h⟩

/-- `Spf L` of a tf-type algebra is locally tf-type over `(R, I)`. -/
theorem _root_.AlgebraicGeometry.IsTopologicallyFiniteType.isLocallyTopFiniteType
    {A : Type u} [CommRing A] [TopologicalSpace A] [Algebra R A] {L : Ideal A} [IsAdicRing L]
    (h : IsTopologicallyFiniteType R I A L) :
    IsLocallyTopFiniteType R I (FormalScheme.Spf L) :=
  IsAffineTopFiniteType.isLocallyTopFiniteType
    (IsTopologicallyFiniteType.isAffineTopFiniteType h)

/-- The global predicate is invariant under isomorphism: transport a cover of `X` to a cover of
`X'` along `e : X' ≅ X` by post-composing each piece with `e.inv`. -/
theorem IsLocallyTopFiniteType.of_iso {X X' : FormalScheme.{u}}
    (h : IsLocallyTopFiniteType R I X) (e : X' ≅ X) : IsLocallyTopFiniteType R I X' := by
  obtain ⟨𝒰, h𝒰⟩ := h
  have hinv : IsIso e.inv.toLRSHom :=
    inferInstanceAs (IsIso (forgetToLocallyRingedSpace.map e.inv))
  refine ⟨{
    J := 𝒰.J
    obj := 𝒰.obj
    map := fun j => 𝒰.map j ≫ e.inv
    f := fun x => 𝒰.f (e.hom.toLRSHom.base x)
    covers := fun x => ?_
    isOpenImmersion := fun j =>
      inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
        ((𝒰.map j).toLRSHom ≫ e.inv.toLRSHom)) }, h𝒰⟩
  obtain ⟨y, hy⟩ := 𝒰.covers (e.hom.toLRSHom.base x)
  refine ⟨y, ?_⟩
  change e.inv.toLRSHom.base ((𝒰.map (𝒰.f (e.hom.toLRSHom.base x))).toLRSHom.base y) = x
  rw [hy]
  change (e.hom ≫ e.inv).toLRSHom.base x = x
  rw [e.hom_inv_id]
  rfl

end AlgebraicGeometry.FormalScheme
