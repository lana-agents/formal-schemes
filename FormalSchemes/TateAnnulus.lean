import FormalSchemes.TopFiniteType
import FormalSchemes.TopFiniteTypeBaseChange

set_option linter.style.header false

/-!
# The formal Tate annulus `Spf R{x, y}/(xy − q)`

Fix an adic ring `R` with ideal of definition `I` and a distinguished element `q ∈ R` (the
**Tate parameter**; in the motivating case `R` is a complete rank-1 valuation ring and `q` is a
topologically nilpotent non-zero-divisor with `0 < |q| < 1`). The **formal Tate annulus** is the
affine formal scheme
```
Spf A,   A := R{x, y} / (x·y − q),
```
where `R{x, y} = RestrictedPowerSeries R I 2` is the two-variable restricted power series ring
(the formal polydisc of dimension two). It is the basic patch out of which Raynaud's formal model
of the Tate curve is glued: the infinite chain `⋯ — U_{n} — U_{n+1} — ⋯` of these annuli, with
transition maps `x_{n+1} = y_n`, is cut out inside the formal multiplicative group and its
quotient by the shift `q^ℤ` is the Tate curve (Bosch, *Lectures on Formal and Rigid Geometry*,
§9).

This file constructs the single annulus patch as an algebra and as a formal scheme, building on
the *topologically of finite type* machinery of `FormalSchemes.TopFiniteType`:

* `annulusAlgebra R I q`: the quotient `R{x, y} / (x·y − q)`, an `R`-algebra;
* `annulus_isTopologicallyFiniteType`: `A` is topologically of finite type over `(R, I)`, being
  a quotient of the polydisc `R{x, y}` (`IsTopologicallyFiniteType.of_surjective`);
* `annulus_coord_mul`: the defining relation `x · y = q` holds in `A`;
* `annulus_map_eq`: the ideal of definition of `A` is the extension `I·A`;
* `annulus_isAdicRing` / `annulus_isAdicRing_of_kerClosed`: `A` is a complete adic ring — over a
  Noetherian base the presentation kernel is automatically adically closed
  (`isAdicRing_of_noetherian`), otherwise closedness is an explicit hypothesis;
* `annulus`: the affine formal scheme `Spf A` over a Noetherian base;
* `annulusStructMap`: the structural morphism `Spf A ⟶ Spf R` of locally ringed spaces.

The gluing of the `U_n` into the Tate chain, the `ℤ`-action by the shift, and the overlap
identification `A[x⁻¹]^\wedge ≅ R{x, x⁻¹}` (a copy of the formal `Ĝm`) are left to the follow-up
parts of issue 68.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*], Ch. V (the Tate curve).
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.13.
-/

noncomputable section

open Ideal AlgebraicGeometry

universe u

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- The two-variable restricted power series ring `R{x, y}`, the coordinate ring of the formal
polydisc of dimension two, out of which the Tate annulus is cut. -/
abbrev annulusRing : Type u := RestrictedPowerSeries R I 2

/-- The first coordinate `x` of `R{x, y}`. -/
abbrev annulusX : annulusRing R I :=
  AdicCompletion.of _ _ (MvPolynomial.X 0)

/-- The second coordinate `y` of `R{x, y}`. -/
abbrev annulusY : annulusRing R I :=
  AdicCompletion.of _ _ (MvPolynomial.X 1)

/-- The Tate relation `x·y − q` inside `R{x, y}`. -/
abbrev annulusRel : annulusRing R I :=
  annulusX R I * annulusY R I - algebraMap R (annulusRing R I) q

/-- The ideal `(x·y − q)` cutting the Tate annulus out of the polydisc `R{x, y}`. -/
abbrev annulusIdeal : Ideal (annulusRing R I) :=
  Ideal.span {annulusRel R I q}

/-- The coordinate ring `A = R{x, y} / (x·y − q)` of the **formal Tate annulus**, as an
`R`-algebra. -/
abbrev annulusAlgebra : Type u := annulusRing R I ⧸ annulusIdeal R I q

/-- The quotient presentation `R{x, y} ↠ A` exhibiting the annulus as a quotient of the formal
polydisc. -/
abbrev annulusMk : annulusRing R I →ₐ[R] annulusAlgebra R I q :=
  Ideal.Quotient.mkₐ R (annulusIdeal R I q)

/-- The ideal of definition of the Tate annulus `A`: the image of the ideal of definition of the
polydisc `R{x, y}` under the presentation. -/
abbrev annulusIdealOfDefinition : Ideal (annulusAlgebra R I q) :=
  (RestrictedPowerSeries.idealOfDefinition R I 2).map (annulusMk R I q).toRingHom

/-- The topology on the Tate annulus is the adic topology of its ideal of definition. -/
instance annulusTopologicalSpace : TopologicalSpace (annulusAlgebra R I q) :=
  (annulusIdealOfDefinition R I q).adicTopology

theorem annulusMk_surjective : Function.Surjective (annulusMk R I q) :=
  Ideal.Quotient.mkₐ_surjective R _

/-- **The Tate annulus is topologically of finite type over `(R, I)`**: it is a quotient of the
formal polydisc `R{x, y}` by the ideal `(x·y − q)`, carrying the quotient filtration. -/
theorem annulus_isTopologicallyFiniteType :
    IsTopologicallyFiniteType R I (annulusAlgebra R I q) (annulusIdealOfDefinition R I q) :=
  (RestrictedPowerSeries.isTopologicallyFiniteType R I 2).of_surjective
    (annulusMk R I q) (annulusMk_surjective R I q) rfl

/-- **The defining relation of the Tate annulus**: in `A = R{x, y}/(x·y − q)` the images of the
coordinates satisfy `x · y = q`. -/
theorem annulus_coord_mul :
    annulusMk R I q (annulusX R I) * annulusMk R I q (annulusY R I)
      = algebraMap R (annulusAlgebra R I q) q := by
  have h : annulusMk R I q (annulusRel R I q) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  rw [annulusRel, map_sub, map_mul, AlgHom.commutes, sub_eq_zero] at h
  exact h

/-- The ideal of definition of the Tate annulus is the extension `I·A` of the base ideal of
definition. -/
theorem annulus_map_eq :
    I.map (algebraMap R (annulusAlgebra R I q)) = annulusIdealOfDefinition R I q :=
  (annulus_isTopologicallyFiniteType R I q).map_eq

/-- **The Tate annulus is a complete adic ring over a Noetherian base**: when the presenting
polydisc `R{x, y}` is Noetherian, the kernel `(x·y − q)` is automatically adically closed (Krull
intersection), so the quotient `A` is a complete adic ring with ideal of definition `I·A` and its
formal spectrum is an affine formal scheme. -/
theorem annulus_isAdicRing (hI : I.FG)
    [IsNoetherianRing (RestrictedPowerSeries R I 2)] :
    IsAdicRing (annulusIdealOfDefinition R I q) :=
  IsTopologicallyFiniteType.isAdicRing_of_noetherian hI (annulusMk_surjective R I q) rfl

/-- **The Tate annulus is a complete adic ring**, general form: if the presentation kernel
`(x·y − q)` is adically closed (automatic in the Noetherian case, `annulus_isAdicRing`) then `A`
is a complete adic ring with ideal of definition `I·A`. -/
theorem annulus_isAdicRing_of_kerClosed (hI : I.FG)
    (hker : (annulusMk R I q).toRingHom.AdicKerClosed
      (RestrictedPowerSeries.idealOfDefinition R I 2)) :
    IsAdicRing (annulusIdealOfDefinition R I q) :=
  IsTopologicallyFiniteType.isAdicRing hI (annulusMk_surjective R I q) rfl hker

/-- The **formal Tate annulus** `Spf A = Spf R{x, y}/(x·y − q)` as an affine formal scheme over a
Noetherian base (Bosch, §9). -/
def annulus (hI : I.FG) [IsNoetherianRing (RestrictedPowerSeries R I 2)] : FormalScheme :=
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  FormalScheme.Spf (annulusIdealOfDefinition R I q)

/-- The **structural morphism** `Spf A ⟶ Spf R` of the Tate annulus, as a morphism of locally
ringed spaces coming from the `R`-algebra structure of `A`. -/
def annulusStructMap [TopologicalSpace R] [IsAdicRing I] (hI : I.FG)
    [IsNoetherianRing (RestrictedPowerSeries R I 2)] :
    FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q) ⟶
      FormalSpectrum.locallyRingedSpaceObj I :=
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  IsTopologicallyFiniteType.structMap (annulus_map_eq R I q)

end
