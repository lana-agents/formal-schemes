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
This file assembles the two into the §10.13 statement for `𝔈_q`.

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

The cover is built by hand rather than taken from `FormalScheme.GlueData.openCover`
(`FormalSchemes.OpenCover`). That canonical cover's `obj i` is `(D.isFormalScheme i).choose` — an
opaque `Classical.choose` — so exhibiting the identification `obj i ≅ Spf A` that §10.13 needs
would have to go through `choose_spec.some`, and the resulting composite would then have to be
compared with `ι i` inside the compatibility obligation. Building the cover directly costs three
short fields and keeps the obligation defeq-transparent: the patch `U b` of the Tate glue datum is
*definitionally* `locallyRingedSpaceObj (annulusIdealOfDefinition R I q)`, which is why
`tateCurveFormalGlueData` can pass `Iso.refl _` as its own `isFormalScheme` witness
(`TateCurveModel.lean`).

With the cover in that shape the identification `e` is `Iso.refl _`, and the compatibility
`𝒰.map b ≫ f = e.hom ≫ structHom h` reduces, after `FormalScheme.Hom.ext'` and `Category.id_comp`,
to `ι_tateCurveModelStructMap`. The two structural morphisms match on the nose:
`annulusStructMap` is *defined* as `IsTopologicallyFiniteType.structMap (annulus_map_eq R I q)`
(`TateAnnulus.lean`), and `structHom` wraps `structMap h.map_eq`; the two proof arguments are
proofs of the same `Prop`, hence definitionally equal.

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
open immersion `ι b`.

Compared with the canonical `FormalScheme.GlueData.openCover`, the pieces here are the actual
affine formal scheme rather than a `Classical.choose`n one isomorphic to it, which is what makes
the §10.13 identification below the identity. -/
def tateCurveModelOpenCover (hq : q ∈ I) (hI : I.FG) :
    FormalScheme.OpenCover (tateCurveModel R I q hq hI) :=
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  { J := ULift.{u} Bool
    obj := fun _ => FormalScheme.Spf (annulusIdealOfDefinition R I q)
    map := fun b => FormalScheme.Hom.mk ((tateCurveFormalGlueData R I q hq hI).ι b)
    f := fun x => ((tateCurveFormalGlueData R I q hq hI).ι_jointly_surjective x).choose
    covers := fun x =>
      ⟨((tateCurveFormalGlueData R I q hq hI).ι_jointly_surjective x).choose_spec.choose,
        ((tateCurveFormalGlueData R I q hq hI).ι_jointly_surjective x).choose_spec.choose_spec⟩
    isOpenImmersion := fun b => (tateCurveFormalGlueData R I q hq hI).ι_isOpenImmersion b }

/-- **The Tate curve model is topologically of finite type over `Spf R`** (EGA I §10.13): its
structural morphism `𝔈_q ⟶ Spf R` admits the two-chart cover of `tateCurveModelOpenCover`, whose
every piece is `Spf` of the annulus algebra `A = R{x, y} / (x·y − q)` — topologically of finite
type by `annulus_isTopologicallyFiniteType` — compatibly with the structural morphisms.

Together with `tate_isSeparated` this is the pair of basic EGA properties of `𝔈_q`. -/
theorem tateCurveModel_isRelativelyTopFiniteType (hq : q ∈ I) (hI : I.FG) :
    FormalScheme.IsRelativelyTopFiniteType R I
      (FormalScheme.Hom.mk (tateCurveModelStructMap R I q hq hI)) := by
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  refine ⟨tateCurveModelOpenCover R I q hq hI, fun b =>
    ⟨annulusAlgebra R I q, inferInstance, inferInstance, inferInstance,
      annulusIdealOfDefinition R I q, inferInstance, annulus_isTopologicallyFiniteType R I q,
      Iso.refl _, ?_⟩⟩
  refine FormalScheme.Hom.ext' ?_
  change (tateCurveFormalGlueData R I q hq hI).ι b ≫ tateCurveModelStructMap R I q hq hI =
    𝟙 _ ≫ IsTopologicallyFiniteType.structMap
      (annulus_isTopologicallyFiniteType R I q).map_eq
  rw [Category.id_comp]
  exact ι_tateCurveModelStructMap R I q hq hI b

/-- **The Tate curve model is locally of finite type over `(R, I)`**, the object-level form of
`tateCurveModel_isRelativelyTopFiniteType`. -/
theorem tateCurveModel_isLocallyTopFiniteType (hq : q ∈ I) (hI : I.FG) :
    FormalScheme.IsLocallyTopFiniteType R I (tateCurveModel R I q hq hI) :=
  (tateCurveModel_isRelativelyTopFiniteType R I q hq hI).isLocallyTopFiniteType

end AlgebraicGeometry

end
