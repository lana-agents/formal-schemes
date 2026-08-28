import FormalSchemes.RelativeTopFiniteTypeTrans
import FormalSchemes.TateTopFiniteType
import FormalSchemes.TopFiniteTypeBasis

set_option linter.style.header false

/-!
# The Tate curve model over a topologically-finite-type base

`FormalSchemes.RelativeTopFiniteTypeTrans` proves EGA I 10.13's composition law for the
base-affine notion. This file runs it on the project's only non-affine witness, so that the law is
applied rather than merely stated, and instantiates the result at a tower with no unwitnessed
hypothesis.

The two modules are kept apart deliberately: issue 62's item (1) — the morphism-level notion at a
non-affine target — will consume the general lemmas, and importing `FormalSchemes.TateTopFiniteType`
into them would put the whole Tate closure on that import edge for no reason.

## What is proved

`AlgebraicGeometry.tateCurveModel_isRelativelyTopFiniteType`
(`FormalSchemes.TateTopFiniteType`) says the Tate curve model `𝔈_q` is topologically of finite
type over its own base `Spf R`, and its source is genuinely not affine — it is glued from two
annulus charts. Composing with the structural morphism of a tf-type base gives

> if `(R, I)` is itself topologically of finite type over `(R₀, I₀)`, then `𝔈_q ⟶ Spf R₀` is
> topologically of finite type,

and its object-level form, that `𝔈_q` is locally tf-type over `(R₀, I₀)`.

`polydisc_tateCurveModel_isLocallyTopFiniteType` is that statement at
`R = R₀{X₁, …, Xₙ}`, where the tf-type structure is the identity presentation and so is available
unconditionally. Its two side conditions — that the Tate parameter lies in the ideal of definition
of the polydisc, and that that ideal is finitely generated — are discharged by
`RestrictedPowerSeries.algebraMap_mem_idealOfDefinition` and
`RestrictedPowerSeries.idealOfDefinition_fg` below rather than assumed, so nothing here is a
conditional statement dressed as an application.

## Main results

* `RestrictedPowerSeries.isTopologicallyFiniteType_self`: the polydisc is tf-type over its base by
  its identity presentation.
* `AlgebraicGeometry.tateCurveModel_isRelativelyTopFiniteType_base`,
  `AlgebraicGeometry.tateCurveModel_isLocallyTopFiniteType_base`: the Tate curve over a tf-type
  base.
* `AlgebraicGeometry.polydisc_tateCurveModel_isLocallyTopFiniteType`: the unconditional
  instantiation.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.13.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7, §9.
-/

noncomputable section

open CategoryTheory

universe u

namespace RestrictedPowerSeries

variable (R₀ : Type u) [CommRing R₀] (I₀ : Ideal R₀) (n : ℕ)

/-- **The formal polydisc is topologically of finite type over its own base**, by the identity
presentation. This is the cheapest nontrivial value of `IsTopologicallyFiniteType`, and it is what
makes the instantiation below unconditional. -/
theorem isTopologicallyFiniteType_self :
    IsTopologicallyFiniteType R₀ I₀ (RestrictedPowerSeries R₀ I₀ n) (idealOfDefinition R₀ I₀ n) :=
  ⟨n, AlgHom.id R₀ _, Function.surjective_id, Ideal.map_id _⟩

/-- The polydisc's ideal of definition is finitely generated when the base ideal is: it is the
extension `I₀·R₀{X₁, …, Xₙ}`. -/
theorem idealOfDefinition_fg (hI₀ : I₀.FG) : (idealOfDefinition R₀ I₀ n).FG :=
  AlgebraicGeometry.IsTopologicallyFiniteType.fg (isTopologicallyFiniteType_self R₀ I₀ n) hI₀

variable {R₀ I₀}

/-- An element of the base ideal maps into the polydisc's ideal of definition, so a Tate parameter
downstairs is a Tate parameter upstairs. -/
theorem algebraMap_mem_idealOfDefinition {q₀ : R₀} (hq₀ : q₀ ∈ I₀) :
    algebraMap R₀ (RestrictedPowerSeries R₀ I₀ n) q₀ ∈ idealOfDefinition R₀ I₀ n :=
  IsTopologicallyFiniteType.map_eq (isTopologicallyFiniteType_self R₀ I₀ n) ▸
    Ideal.mem_map_of_mem _ hq₀

end RestrictedPowerSeries

namespace AlgebraicGeometry

open FormalScheme

variable {R₀ : Type u} [CommRing R₀] {I₀ : Ideal R₀}
variable {R : Type u} [CommRing R] [TopologicalSpace R] [Algebra R₀ R] [IsNoetherianRing R]
variable {I : Ideal R} [IsAdicRing I] {q : R}

section AffineBase

variable [TopologicalSpace R₀] [IsAdicRing I₀]

/-- **The Tate curve model over a tf-type base is topologically of finite type over the deeper
base.** `IsRelativelyTopFiniteType.comp_structHom` applied to
`tateCurveModel_isRelativelyTopFiniteType`, whose source `𝔈_q` is glued from two annulus charts and
so is not affine — the composition law is being used here, not restated at an affine source. -/
theorem tateCurveModel_isRelativelyTopFiniteType_base (hI₀ : I₀.FG)
    (hR : IsTopologicallyFiniteType R₀ I₀ R I) (hq : q ∈ I) (hI : I.FG) :
    IsRelativelyTopFiniteType R₀ I₀
      (FormalScheme.Hom.mk (tateCurveModelStructMap R I q hq hI) ≫
        IsTopologicallyFiniteType.structHom hR) :=
  (tateCurveModel_isRelativelyTopFiniteType R I q hq hI).comp_structHom hI₀ hR

end AffineBase

/-- **The Tate curve model is locally of finite type over the deeper base**, the object-level form
of `tateCurveModel_isRelativelyTopFiniteType_base`. -/
theorem tateCurveModel_isLocallyTopFiniteType_base (hI₀ : I₀.FG)
    (hR : IsTopologicallyFiniteType R₀ I₀ R I) (hq : q ∈ I) (hI : I.FG) :
    IsLocallyTopFiniteType R₀ I₀ (tateCurveModel R I q hq hI) :=
  (tateCurveModel_isLocallyTopFiniteType R I q hq hI).trans hI₀ hR

/-- **The Tate curve over the formal polydisc is topologically of finite type over the base.**

The tower is `𝔈_q ⟶ Spf (I₀·R₀{X₁, …, Xₙ}) ⟶ Spf I₀` with the Tate parameter the image of a
`q₀ ∈ I₀`. Nothing is assumed beyond `I₀.FG`, `q₀ ∈ I₀` and Noetherianness of `R₀`: the middle
term's tf-type structure is `RestrictedPowerSeries.isTopologicallyFiniteType_self`, and the two
side conditions of `tateCurveModel` are supplied by
`RestrictedPowerSeries.algebraMap_mem_idealOfDefinition` and
`RestrictedPowerSeries.idealOfDefinition_fg`. -/
theorem polydisc_tateCurveModel_isLocallyTopFiniteType [IsNoetherianRing R₀] (hI₀ : I₀.FG)
    {q₀ : R₀} (hq₀ : q₀ ∈ I₀) (n : ℕ) :
    haveI : IsAdicRing (RestrictedPowerSeries.idealOfDefinition R₀ I₀ n) :=
      RestrictedPowerSeries.isAdicRing R₀ I₀ n hI₀
    IsLocallyTopFiniteType R₀ I₀
      (tateCurveModel (RestrictedPowerSeries R₀ I₀ n)
        (RestrictedPowerSeries.idealOfDefinition R₀ I₀ n)
        (algebraMap R₀ (RestrictedPowerSeries R₀ I₀ n) q₀)
        (RestrictedPowerSeries.algebraMap_mem_idealOfDefinition n hq₀)
        (RestrictedPowerSeries.idealOfDefinition_fg R₀ I₀ n hI₀)) :=
  haveI : IsAdicRing (RestrictedPowerSeries.idealOfDefinition R₀ I₀ n) :=
    RestrictedPowerSeries.isAdicRing R₀ I₀ n hI₀
  tateCurveModel_isLocallyTopFiniteType_base hI₀
    (RestrictedPowerSeries.isTopologicallyFiniteType_self R₀ I₀ n) _ _

end AlgebraicGeometry
