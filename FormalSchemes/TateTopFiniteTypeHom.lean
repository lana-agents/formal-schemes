import FormalSchemes.TopFiniteTypeHom
import FormalSchemes.TateTopFiniteTypeTrans

set_option linter.style.header false

/-!
# The Tate curve as a value of the general finite-type predicate

`FormalSchemes.TopFiniteTypeHom` defines `AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHom` for
a morphism `f : X ⟶ Y` between arbitrary formal schemes. This file records that the predicate has
a value at a **named geometric object with a non-affine source**, rather than only at the affine
local models it is built from.

The morphism is the Tate curve over the formal polydisc,

```
𝔈_q ⟶ Spf (I₀·R₀{X₁, …, Xₙ}) ⟶ Spf I₀,
```

whose source `𝔈_q` is glued from two annulus charts and so is not affine. It is the tower that
`AlgebraicGeometry.polydisc_tateCurveModel_isRelativelyTopFiniteType`
(`FormalSchemes.TateTopFiniteTypeTrans`, issue 1158) already carries for the base-affine notion,
pushed across `IsRelativelyTopFiniteType.isTopFiniteTypeHom`; the `I₀.FG` that reduction consumes
is a hypothesis of the Tate statement already, so nothing new is assumed.

Why this is worth a declaration rather than a remark: a predicate stated as an existential over
covers can be satisfied vacuously, and this tree's practice is to land non-vacuity as a theorem.
The three witnesses now on the tree exercise different things and none subsumes another.
`IsTopologicallyFiniteType.isTopFiniteTypeHom` is the affine local model, with one chart on each
side. `AlgebraicGeometry.FormalScheme.isTopFiniteTypeHom_id` has a genuinely multi-chart cover on
**both** sides as soon as the formal scheme it is handed is not affine, but its finiteness data is
the identity presentation (`IsTopologicallyFiniteType.self`), so it says nothing about the tf-type
condition. This one has a **non-affine source** and finiteness data that is not an identity — and a
one-chart target, since it comes through the base-affine reduction, which uses
`AlgebraicGeometry.FormalScheme.OpenCover.self`.

A witness with a multi-chart target cover **and** non-identity finiteness data was for a long time
unavailable, the reason being the composition gap recorded in `FormalSchemes.TopFiniteTypeHom`:
the only route to one is a tower. That gap is closed —
`AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHom.trans`
(`FormalSchemes.TopFiniteTypeHomTrans`) — and
`AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHom.comp_chartMap` is the general form of such a
witness: any tf-type morphism into a chart of an affine cover, composed with that chart's
inclusion, is witnessed against a target cover indexed by a sum, with the finiteness data of the
first factor. Composing the morphism below with a chart inclusion is an instance of it; the
instance is not landed here, since the tree has no non-affine formal scheme carrying `Spf I₀` as a
named chart.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.13.
-/

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

open FormalScheme

variable {R₀ : Type u} [CommRing R₀] {I₀ : Ideal R₀} [TopologicalSpace R₀] [IsAdicRing I₀]

/-- **The Tate curve over the formal polydisc is topologically of finite type as a morphism.**

`polydisc_tateCurveModel_isRelativelyTopFiniteType` (`FormalSchemes.TateTopFiniteTypeTrans`) read
through `IsRelativelyTopFiniteType.isTopFiniteTypeHom`. The source `𝔈_q` is glued from two annulus
charts, so this is a value of the predicate at a non-affine source; nothing is assumed beyond the
`IsNoetherianRing R₀`, `I₀.FG` and `q₀ ∈ I₀` the Tate statement already carries. -/
theorem polydisc_tateCurveModel_isTopFiniteTypeHom [IsNoetherianRing R₀] (hI₀ : I₀.FG)
    {q₀ : R₀} (hq₀ : q₀ ∈ I₀) (n : ℕ) :
    haveI : IsAdicRing (RestrictedPowerSeries.idealOfDefinition R₀ I₀ n) :=
      RestrictedPowerSeries.isAdicRing R₀ I₀ n hI₀
    IsTopFiniteTypeHom
      (FormalScheme.Hom.mk (tateCurveModelStructMap (RestrictedPowerSeries R₀ I₀ n)
          (RestrictedPowerSeries.idealOfDefinition R₀ I₀ n)
          (algebraMap R₀ (RestrictedPowerSeries R₀ I₀ n) q₀)
          (RestrictedPowerSeries.algebraMap_mem_idealOfDefinition n hq₀)
          (RestrictedPowerSeries.idealOfDefinition_fg R₀ I₀ n hI₀)) ≫
        IsTopologicallyFiniteType.structHom
          (RestrictedPowerSeries.isTopologicallyFiniteType R₀ I₀ n)) :=
  haveI : IsAdicRing (RestrictedPowerSeries.idealOfDefinition R₀ I₀ n) :=
    RestrictedPowerSeries.isAdicRing R₀ I₀ n hI₀
  (polydisc_tateCurveModel_isRelativelyTopFiniteType hI₀ hq₀ n).isTopFiniteTypeHom hI₀

end AlgebraicGeometry
