import FormalSchemes.TateCurveModel
import FormalSchemes.GlobalTopFiniteType

set_option linter.style.header false

/-!
# The Tate curve formal model is locally topologically of finite type

Fix an adic base `R` with finitely generated ideal of definition `I` and a Tate parameter
`q ∈ I`. The Tate curve formal model `𝔈_q = T/q^ℤ` (`AlgebraicGeometry.tateCurveModel`,
`FormalSchemes.TateCurveModel`) is the two-chart circular quotient glued from two copies of the
formal Tate annulus `Spf A`, `A = R{x, y}/(x·y − q)`. This short file records that `𝔈_q` is a
genuine **admissible formal `R`-scheme** in the sense of Bosch (LNM 2105, §7–8): it is
*locally topologically of finite type* over `(R, I)` (`FormalScheme.IsLocallyTopFiniteType`,
`FormalSchemes.GlobalTopFiniteType`).

This is the first non-affine instance of the object-level global tf-type predicate: the affine
model `Spf A` was already known to be affine tf-type (`annulus_isTopologicallyFiniteType`), and
`𝔈_q` inherits the property from its canonical cover by the two annulus patches.

## Main results

* `AlgebraicGeometry.tateCurveModel_isLocallyTopFiniteType`: `𝔈_q` is locally topologically of
  finite type over `(R, I)`, witnessed by the canonical two-patch cover, each piece being `Spf A`.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7–9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.13.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- **The Tate curve formal model is locally topologically of finite type over `(R, I)`.** Its
canonical cover (`FormalScheme.GlueData.openCover`) has both pieces isomorphic to the formal Tate
annulus `Spf A`, which is affine tf-type by `annulus_isTopologicallyFiniteType`; the property
transports along the covering isomorphism (`IsAffineTopFiniteType.of_iso`), exhibiting `𝔈_q` as
an admissible formal `R`-scheme. -/
theorem tateCurveModel_isLocallyTopFiniteType (hq : q ∈ I) (hI : I.FG) [IsNoetherianRing R] :
    FormalScheme.IsLocallyTopFiniteType R I (tateCurveModel R I q hq hI) := by
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  refine ⟨(tateCurveFormalGlueData R I q hq hI).openCover, fun j => ?_⟩
  -- The `j`-th cover piece is `(isFormalScheme j).choose`; its spec gives an LRS isomorphism to
  -- `D.U j`, which is definitionally `(Spf A).toLocallyRingedSpace`.
  have e := ((tateCurveFormalGlueData R I q hq hI).isFormalScheme j).choose_spec.some
  refine (annulus_isTopologicallyFiniteType R I q).isAffineTopFiniteType.of_iso ?_
  exact FormalScheme.forgetToLocallyRingedSpace.preimageIso e

end AlgebraicGeometry
