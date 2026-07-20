import FormalSchemes.Spf

set_option linter.style.header false

/-!
# Formal schemes

A **formal scheme** (EGA I, 10.4.2) is a locally ringed space that is locally isomorphic to the
formal spectrum `Spf R` of an adic ring `R` — just as a scheme is a locally ringed space locally
isomorphic to the prime spectrum of a ring. This file defines the category of formal schemes,
mirroring the definition of `AlgebraicGeometry.Scheme`:

* `FormalScheme`: a locally ringed space such that every point has an open neighbourhood
  isomorphic, as a locally ringed space, to `FormalSpectrum.locallyRingedSpaceObj I` for some
  adic ring `(R, I)`.
* `FormalScheme.Hom`, and the category instance: morphisms of formal schemes are morphisms of
  the underlying locally ringed spaces; formal schemes form a full subcategory of locally
  ringed spaces (`FormalScheme.forgetToLocallyRingedSpace`).
* `FormalScheme.Spf I`: the **affine formal scheme** attached to an adic ring `R` with ideal of
  definition `I`.

Following the design of the rest of this development, the structure sheaf is a sheaf of plain
commutative rings (the topology on the sections is recoverable from the tower of thickenings);
EGA's topologically ringed spaces are recovered through the limit description of the sections
(`FormalSpectrum.sectionsBasicOpenEquiv`).

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4.
* [The Stacks Project, Tag 0AIL](https://stacks.math.columbia.edu/tag/0AIL)
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A **formal scheme** is a locally ringed space such that every point is contained in some
open set `U`, such that the restriction to `U` is isomorphic, as a locally ringed space, to the
formal spectrum of an adic ring (EGA I, 10.4.2). -/
structure FormalScheme extends LocallyRingedSpace where
  local_affine :
    ∀ x : toLocallyRingedSpace,
      ∃ (U : OpenNhds x) (R : Type u) (_ : CommRing R) (_ : TopologicalSpace R) (I : Ideal R)
        (_ : IsAdicRing I),
        Nonempty (toLocallyRingedSpace.restrict U.isOpenEmbedding ≅
          FormalSpectrum.locallyRingedSpaceObj I)

namespace FormalScheme

instance : CoeSort FormalScheme Type* where
  coe X := X.carrier

/-- A morphism between formal schemes is a morphism between the underlying locally ringed
spaces. -/
structure Hom (X Y : FormalScheme)
    extends toLRSHom' : X.toLocallyRingedSpace.Hom Y.toLocallyRingedSpace where

/-- Cast a morphism of formal schemes into a morphism of locally ringed spaces. -/
abbrev Hom.toLRSHom {X Y : FormalScheme.{u}} (f : X.Hom Y) :
    X.toLocallyRingedSpace ⟶ Y.toLocallyRingedSpace :=
  f.toLRSHom'

/-- Formal schemes are a full subcategory of locally ringed spaces. -/
instance : Category FormalScheme where
  Hom := Hom
  id X := Hom.mk (𝟙 X.toLocallyRingedSpace)
  comp f g := Hom.mk (f.toLRSHom ≫ g.toLRSHom)

@[ext]
theorem Hom.ext' {X Y : FormalScheme.{u}} {f g : X ⟶ Y} (h : f.toLRSHom = g.toLRSHom) :
    f = g := by
  cases f
  cases g
  cases h
  rfl

/-- The forgetful functor from formal schemes to locally ringed spaces. -/
def forgetToLocallyRingedSpace : FormalScheme ⥤ LocallyRingedSpace where
  obj := FormalScheme.toLocallyRingedSpace
  map f := f.toLRSHom

instance : forgetToLocallyRingedSpace.Faithful where
  map_injective := fun h => Hom.ext' h

instance : forgetToLocallyRingedSpace.Full where
  map_surjective f := ⟨Hom.mk f, rfl⟩

end FormalScheme

set_option linter.style.setOption false in
set_option maxHeartbeats 1000000 in
-- Checking that the restriction of `Spf R` to `⊤` matches `locallyRingedSpaceObj I` unfolds the
-- structure sheaf (a limit of pushforward sheaves) against the restriction machinery, which is
-- slow.
/-- The **affine formal scheme** `Spf R` attached to an adic ring `R` with ideal of definition
`I`: the formal spectrum together with its structure sheaf, viewed as a formal scheme. -/
def FormalScheme.Spf {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R)
    [IsAdicRing I] : FormalScheme where
  __ := FormalSpectrum.locallyRingedSpaceObj I
  local_affine x :=
    ⟨⟨⊤, trivial⟩, R, ‹_›, ‹_›, I, ‹_›,
      ⟨(FormalSpectrum.locallyRingedSpaceObj I).restrictTopIso⟩⟩

end AlgebraicGeometry
