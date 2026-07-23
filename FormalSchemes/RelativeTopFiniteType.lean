import FormalSchemes.GlobalTopFiniteType

set_option linter.style.header false

/-!
# Morphisms of formal schemes topologically of finite type over the base

Fix a base adic ring `(R, I)`, so `Spf R = FormalScheme.Spf I` is the affine base. Issue 66 built
the affine tf-type layer (`FormalSchemes.TopFiniteType`, `IsTopologicallyFiniteType`) and the
object-level global notion (`FormalSchemes.GlobalTopFiniteType`, `IsLocallyTopFiniteType`: a
formal scheme admits an open cover by `Spf` of tf-type `R`-algebras). This file adds the
**relative** refinement flagged as follow-up there: a *morphism* `f : X ⟶ Spf R` is
topologically of finite type when `X` admits an open cover whose pieces are affine tf-type over
`(R, I)` *and* the cover maps commute, through those affine identifications, with the structural
morphism `Spf L ⟶ Spf R` of each piece. This is the object-level, base-affine form of the
locally-of-finite-type morphism property (EGA I, 10.13); unlike a general relative-finiteness
notion it needs no fibre products, only the open-cover scaffold and the affine structural map.

## Main definitions

* `IsTopologicallyFiniteType.structHom`: the structural morphism `Spf L ⟶ Spf R` of a tf-type
  `R`-algebra `A` (ideal of definition `L`), packaged as a morphism of formal schemes (the
  `FormalScheme.Hom` wrapper of the locally-ringed-space `IsTopologicallyFiniteType.structMap`).
* `FormalScheme.IsRelativelyTopFiniteType R I f`: the morphism `f : X ⟶ Spf R` is topologically
  of finite type, i.e. `X` has an open cover whose pieces are affine tf-type over `(R, I)` and
  whose maps commute with `f` over the structural morphisms.

## Main results

* `IsTopologicallyFiniteType.isRelativelyTopFiniteType`: the affine structural morphism
  `structHom : Spf L ⟶ Spf R` of a tf-type algebra is itself relatively tf-type (the affine model
  instantiates the predicate, via the one-piece self-cover).
* `IsRelativelyTopFiniteType.isLocallyTopFiniteType`: a relatively tf-type morphism `f : X ⟶ Spf R`
  has relatively tf-type *source* `X` — i.e. the relative notion refines the object-level
  `IsLocallyTopFiniteType`, forgetting the morphism.

## Remaining follow-up

The fully general relative notion for a morphism `f : X ⟶ Y` between arbitrary formal schemes
(covers of both `X` and `Y`, compatibility on preimages) and its stability properties
(composition, base change) still want a morphism-property / fibre-product layer for formal
schemes (also wanted by issue 62's §10.15 separatedness). This file records the base-affine case
`Y = Spf R` the Tate construction consumes.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7–8.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.13.
-/

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {I : Ideal R} [TopologicalSpace R] [IsAdicRing I]

/-- The structural morphism `Spf L ⟶ Spf R` of a tf-type adic `R`-algebra `A` (ideal of
definition `L`), packaged as a morphism of formal schemes. It is the `FormalScheme.Hom` wrapper
of the locally-ringed-space structural map `IsTopologicallyFiniteType.structMap`. -/
def IsTopologicallyFiniteType.structHom {A : Type u} [CommRing A] [TopologicalSpace A]
    [Algebra R A] {L : Ideal A} [IsAdicRing L] (h : IsTopologicallyFiniteType R I A L) :
    FormalScheme.Spf L ⟶ FormalScheme.Spf I :=
  FormalScheme.Hom.mk (IsTopologicallyFiniteType.structMap h.map_eq)

namespace FormalScheme

variable (R I) in
/-- A morphism `f : X ⟶ Spf R` of formal schemes is **topologically of finite type** over the
base `(R, I)` if `X` admits an open cover whose every piece is (identified with) `Spf L` for a
tf-type `R`-algebra `A` with ideal of definition `L`, such that the cover map into `X` followed
by `f` agrees — through that identification — with the piece's structural morphism
`Spf L ⟶ Spf R`. This is the object-level, base-affine form of
`AlgebraicGeometry`'s locally-of-finite-type morphism property (EGA I, 10.13). -/
def IsRelativelyTopFiniteType {X : FormalScheme.{u}} (f : X ⟶ FormalScheme.Spf I) : Prop :=
  ∃ 𝒰 : OpenCover X, ∀ j,
    ∃ (A : Type u) (_ : CommRing A) (_ : TopologicalSpace A) (_ : Algebra R A)
      (L : Ideal A) (_ : IsAdicRing L) (h : IsTopologicallyFiniteType R I A L)
      (e : 𝒰.obj j ≅ FormalScheme.Spf L),
      𝒰.map j ≫ f = e.hom ≫ IsTopologicallyFiniteType.structHom h

/-- The affine structural morphism `Spf L ⟶ Spf R` of a tf-type algebra is relatively tf-type:
it is witnessed by the one-object self-cover with the identity identification. -/
theorem _root_.AlgebraicGeometry.IsTopologicallyFiniteType.isRelativelyTopFiniteType
    {A : Type u} [CommRing A] [TopologicalSpace A] [Algebra R A] {L : Ideal A} [IsAdicRing L]
    (h : IsTopologicallyFiniteType R I A L) :
    IsRelativelyTopFiniteType R I (IsTopologicallyFiniteType.structHom h) :=
  ⟨OpenCover.self (FormalScheme.Spf L), fun _ =>
    ⟨A, inferInstance, inferInstance, inferInstance, L, inferInstance, h, Iso.refl _, by
      simp [OpenCover.self]⟩⟩

/-- A relatively tf-type morphism `f : X ⟶ Spf R` has relatively tf-type source: its cover
witnesses that `X` is locally tf-type over `(R, I)` (forgetting the morphism). So the relative
notion refines the object-level `IsLocallyTopFiniteType`. -/
theorem IsRelativelyTopFiniteType.isLocallyTopFiniteType {X : FormalScheme.{u}}
    {f : X ⟶ FormalScheme.Spf I} (h : IsRelativelyTopFiniteType R I f) :
    IsLocallyTopFiniteType R I X := by
  obtain ⟨𝒰, h𝒰⟩ := h
  refine ⟨𝒰, fun j => ?_⟩
  obtain ⟨A, _, _, _, L, _, hA, e, _⟩ := h𝒰 j
  exact ⟨A, inferInstance, inferInstance, inferInstance, L, inferInstance, hA, ⟨e⟩⟩

end FormalScheme

end AlgebraicGeometry
