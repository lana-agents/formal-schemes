import FormalSchemes.RelativeTopFiniteType

set_option linter.style.header false

/-!
# Glued formal schemes are topologically of finite type over the base (EGA I §10.13)

Fix a base adic ring `(R, I)`. A formal scheme built by gluing affine patches `Spf (L i)`, each
of which is topologically of finite type over `(R, I)`, is topologically of finite type over
`Spf R` as soon as the glued structural morphism restricts to the patches' own structural
morphisms. That is exactly the data `FormalScheme.IsRelativelyTopFiniteType` asks for
(`FormalSchemes.RelativeTopFiniteType`), so the only real work is producing the open cover.

This file is the general form of the argument that `FormalSchemes.TateTopFiniteType` runs for the
Tate curve model `𝔈_q` (issue 806); that file is now a five-line instance of
`isRelativelyTopFiniteType_of_patches`.

## Main definitions and results

* `AlgebraicGeometry.FormalScheme.GlueData.openCoverOfPatches`: the open cover of a glued formal
  scheme by its own patches, presented as `Spf (L i)`.
* `AlgebraicGeometry.FormalScheme.GlueData.isRelativelyTopFiniteType_of_patches`: **a formal
  scheme glued from tf-type affine patches, along a structural morphism restricting to theirs, is
  topologically of finite type over `Spf R`.**

## Implementation notes

`FormalScheme.GlueData.openCover` (`FormalSchemes.OpenCover`) already covers a glued formal scheme
by its pieces, but its `obj i` is `(D.isFormalScheme i).choose` — an opaque `Classical.choose`. No
statement of the form "each piece is `Spf` of a *particular* algebra" can be made about it without
first transporting along `choose_spec.some`, and the transport then reappears inside every
compatibility obligation. `openCoverOfPatches` takes the identification as an argument instead,
which costs one hypothesis and keeps the obligation transparent.

That identification is an **isomorphism family**
`e i : (Spf (L i)).toLocallyRingedSpace ≅ D.toLocallyRingedSpaceGlueData.U i` rather than an
equality `D.toLocallyRingedSpaceGlueData.U i = locallyRingedSpaceObj (L i)`. The equality is not
merely less general: with a *propositional* equality the natural chart law

  `∀ i, D.ι i ≫ s = IsTopologicallyFiniteType.structMap (h i).map_eq`

does not typecheck at all, since `D.ι i ≫ s` has source `D.toLocallyRingedSpaceGlueData.U i` while
`structMap` has source `locallyRingedSpaceObj (L i)`; one would have to insert an `eqToHom` into
the hypothesis, which is strictly worse than an iso. Concrete glue data whose patches are
definitionally affine — the Tate datum is one, which is why `tateCurveFormalGlueData` can pass
`Iso.refl _` as its own `isFormalScheme` witness — supply `fun _ => Iso.refl _` here and lose
nothing.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.13.
-/

noncomputable section

open CategoryTheory FormalSpectrum

universe u

namespace AlgebraicGeometry

namespace FormalScheme

namespace GlueData

variable {R : Type u} [CommRing R] {I : Ideal R} [TopologicalSpace R] [IsAdicRing I]
variable (D : GlueData.{u}) {A : D.toLocallyRingedSpaceGlueData.J → Type u}
variable [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)] [∀ i, Algebra R (A i)]
variable {L : ∀ i, Ideal (A i)} [∀ i, IsAdicRing (L i)]

/-- **The open cover of a glued formal scheme by its patches**, presented as the affine formal
schemes `Spf (L i)` rather than as the `Classical.choose`n formal schemes of
`FormalScheme.GlueData.openCover`. The identification of the `i`-th patch with `Spf (L i)` is
supplied as the isomorphism family `e`; for glue data whose patches are definitionally affine,
`fun _ => Iso.refl _` does. -/
def openCoverOfPatches
    (e : ∀ i, (FormalScheme.Spf (L i)).toLocallyRingedSpace ≅
      D.toLocallyRingedSpaceGlueData.U i) :
    OpenCover D.gluedFormalScheme where
  J := D.toLocallyRingedSpaceGlueData.J
  obj i := FormalScheme.Spf (L i)
  map i := Hom.mk ((e i).hom ≫ D.ι i)
  f x := (D.ι_jointly_surjective x).choose
  covers x := by
    obtain ⟨y, hy⟩ := (D.ι_jointly_surjective x).choose_spec
    refine ⟨(e _).inv.base y, ?_⟩
    have hcancel : (e _).hom.base ((e _).inv.base y) = y := by simp
    simp only [Hom.toLRSHom, LocallyRingedSpace.comp_toHom, PresheafedSpace.comp_base,
      TopCat.hom_comp, ContinuousMap.coe_comp, Function.comp_apply]
    rw [hcancel]
    exact hy
  isOpenImmersion i := LocallyRingedSpace.IsOpenImmersion.comp _ _

/-- **A formal scheme glued from tf-type affine patches is topologically of finite type over the
base** (EGA I §10.13). The inputs are: a tf-type presentation `h i` of each patch algebra
`(A i, L i)`, an identification `e i` of the `i`-th patch of the glue datum with `Spf (L i)`, a
structural morphism `s` out of the glued formal scheme, and the chart law `hs` saying that `s`
restricts on the `i`-th patch to that patch's own structural morphism `Spf (L i) ⟶ Spf R`.

This is the general form of `tateCurveModel_isRelativelyTopFiniteType`
(`FormalSchemes.TateTopFiniteType`), which is its only consumer at the time of writing and which
instantiates it at `e := fun _ => Iso.refl _`. -/
theorem isRelativelyTopFiniteType_of_patches
    (h : ∀ i, IsTopologicallyFiniteType R I (A i) (L i))
    (e : ∀ i, (FormalScheme.Spf (L i)).toLocallyRingedSpace ≅
      D.toLocallyRingedSpaceGlueData.U i)
    (s : D.gluedFormalScheme.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I)
    (hs : ∀ i, (e i).hom ≫ D.ι i ≫ s = IsTopologicallyFiniteType.structMap (h i).map_eq) :
    IsRelativelyTopFiniteType R I (Hom.mk s : D.gluedFormalScheme ⟶ FormalScheme.Spf I) := by
  refine ⟨D.openCoverOfPatches e, fun i =>
    ⟨A i, inferInstance, inferInstance, inferInstance, L i, inferInstance, h i, Iso.refl _, ?_⟩⟩
  refine FormalScheme.Hom.ext' ?_
  change ((e i).hom ≫ D.ι i) ≫ s = 𝟙 _ ≫ IsTopologicallyFiniteType.structMap (h i).map_eq
  rw [Category.id_comp, Category.assoc]
  exact hs i

end GlueData

end FormalScheme

end AlgebraicGeometry

end
