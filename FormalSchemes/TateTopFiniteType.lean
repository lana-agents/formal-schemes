import FormalSchemes.GlueDataTopFiniteType
import FormalSchemes.RelativeTopFiniteType
import FormalSchemes.TateQuotientMap

set_option linter.style.header false

/-!
# The Tate curve model is topologically of finite type over `Spf R` (EGA I §10.13)

Fix an adic base `R` with finitely generated ideal of definition `I` and a Tate parameter `q ∈ I`.
The Tate curve formal model `𝔈_q = tateCurveModel R I q` is glued from two copies of the formal
annulus `Spf A`, `A = R{x, y} / (x·y − q)`, and its structural morphism to `Spf R` restricts to
`annulusStructMap` on each patch (`ι_tateCurveModelStructMap`).

That is *exactly* the data `FormalScheme.IsRelativelyTopFiniteType` asks for, because the annulus
is topologically of finite type over the base by construction: it is presented as a quotient of the
restricted power series ring `R{x, y}`, which is what `annulus_isTopologicallyFiniteType` records.
This file assembles the two into the §10.13 statement for `𝔈_q`, as an instance of the general
glue-datum criterion `FormalScheme.GlueData.isRelativelyTopFiniteType_of_patches`
(`FormalSchemes.GlueDataTopFiniteType`, issue 808).

Together with `tate_isSeparated` (`FormalSchemes.TateSeparatedValue`, issues 706/798), this says:

> **`𝔈_q` is a separated formal scheme, topologically of finite type over `Spf R`.**

`TateSeparatedValue.lean` is deliberately *not* imported here — its import closure is more than
three times this file's, and the separatedness statement is not needed to state or prove anything
below.

## Main definitions and results

* `AlgebraicGeometry.tateCurveModelOpenCover`: the two-chart open cover of `𝔈_q` by its own
  patches `Spf A`, indexed by `ULift Bool`.
* `AlgebraicGeometry.tateCurveModel_isRelativelyTopFiniteType`: **the structural morphism
  `𝔈_q ⟶ Spf R` is topologically of finite type.**
* `AlgebraicGeometry.tateCurveModel_isLocallyTopFiniteType`: the object-level consequence, `𝔈_q` is
  locally of finite type over `(R, I)`.

## Implementation notes

Nothing here is Tate-specific, which is why the argument lives in
`FormalSchemes.GlueDataTopFiniteType` and this file only instantiates it. The patch identification
it asks for is `fun _ => Iso.refl _`: the patch `U b` of the Tate glue datum is *definitionally*
`locallyRingedSpaceObj (annulusIdealOfDefinition R I q)`, which is why `tateCurveFormalGlueData`
can pass `Iso.refl _` as its own `isFormalScheme` witness (`TateCurveModel.lean`). Neither the
canonical `FormalScheme.GlueData.openCover` nor its opaque `(D.isFormalScheme i).choose` pieces are
involved.

The chart law is then `ι_tateCurveModelStructMap` composed with `Category.id_comp`, and the two
structural morphisms match on the nose: `annulusStructMap` is *defined* as
`IsTopologicallyFiniteType.structMap (annulus_map_eq R I q)` (`TateAnnulus.lean`), and the
criterion asks for `structMap (h b).map_eq`; the two proof arguments are proofs of the same `Prop`,
hence definitionally equal.

That last step must be spelled `(Category.id_comp _).trans …` rather than
`rw [Iso.refl_hom, Category.id_comp]`. Rewriting introduces an intermediate
`𝟙 (Spf (annulusIdealOfDefinition R I q)).toLocallyRingedSpace` whose codomain is the `Spf` object
where the composite needs the glue datum's patch `U b` — the same object, but only up to an
unfolding that is not type-correct at `instances` transparency. `exact`-style term application
checks the two against each other by defeq and goes through.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.13.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R]

/-- **The two-chart open cover of the Tate curve model** by its own patches: both pieces are the
affine formal annulus `Spf A`, `A = R{x, y} / (x·y − q)`, and the `b`-th map is the glue datum's
open immersion `ι b`. This is `FormalScheme.GlueData.openCoverOfPatches` at the identity
identification.

Compared with the canonical `FormalScheme.GlueData.openCover`, the pieces here are the actual
affine formal scheme rather than a `Classical.choose`n one isomorphic to it, which is what makes
the §10.13 identification below the identity. -/
def tateCurveModelOpenCover (hq : q ∈ I) (hI : I.FG) :
    FormalScheme.OpenCover (tateCurveModel R I q hq hI) :=
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  (tateCurveFormalGlueData R I q hq hI).openCoverOfPatches
    (L := fun _ => annulusIdealOfDefinition R I q) (fun _ => Iso.refl _)

/-- **The Tate curve model is topologically of finite type over `Spf R`** (EGA I §10.13): its
structural morphism `𝔈_q ⟶ Spf R` admits the two-chart cover of `tateCurveModelOpenCover`, whose
every piece is `Spf` of the annulus algebra `A = R{x, y} / (x·y − q)` — topologically of finite
type by `annulus_isTopologicallyFiniteType` — compatibly with the structural morphisms.

Together with `tate_isSeparated` this is the pair of basic EGA properties of `𝔈_q`. -/
theorem tateCurveModel_isRelativelyTopFiniteType (hq : q ∈ I) (hI : I.FG) :
    FormalScheme.IsRelativelyTopFiniteType R I
      (FormalScheme.Hom.mk (tateCurveModelStructMap R I q hq hI)) := by
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  refine (tateCurveFormalGlueData R I q hq hI).isRelativelyTopFiniteType_of_patches
    (L := fun _ => annulusIdealOfDefinition R I q)
    (fun _ => annulus_isTopologicallyFiniteType R I q) (fun _ => Iso.refl _)
    (tateCurveModelStructMap R I q hq hI) fun b =>
    (Category.id_comp _).trans (ι_tateCurveModelStructMap R I q hq hI b)

/-- **The Tate curve model is locally of finite type over `(R, I)`**, the object-level form of
`tateCurveModel_isRelativelyTopFiniteType`. -/
theorem tateCurveModel_isLocallyTopFiniteType (hq : q ∈ I) (hI : I.FG) :
    FormalScheme.IsLocallyTopFiniteType R I (tateCurveModel R I q hq hI) :=
  (tateCurveModel_isRelativelyTopFiniteType R I q hq hI).isLocallyTopFiniteType

end AlgebraicGeometry

end
