import FormalSchemes.SpfHomFormalScheme
import FormalSchemes.TateChainInvLocallyFG

set_option linter.style.header false

/-!
# The Tate chain is a target of the colimit property

`FormalSchemes.SpfHomFormalScheme` proves that a locally finitely generated formal scheme is a
target of EGA I 10.6.10. `AlgebraicGeometry.tateChainInv` is one
(`AlgebraicGeometry.tateChainInv_locallyFG`), and it is glued from countably many copies of
`Spf (annulusIdealOfDefinition R I q)`, so it is neither `Spec` of a ring nor a formal spectrum.

## Main results

* `AlgebraicGeometry.isThickeningColimitTarget_tateChainInv`: `T_inv` has the colimit property.
* `AlgebraicGeometry.existsUnique_hom_thickeningMap_tateChainInv`: a compatible family of
  morphisms `Spec (S ⧸ Jⁿ⁺¹) ⟶ T_inv` comes from a unique `Spf J ⟶ T_inv`.

## Why this is the ambient and not the answer to issue 1197

`T_inv` is the ambient formal scheme of issue 1197's node chart; the object that issue is about is
the **quotient** `T_inv/⟨σ⟩`, which is not known to be a formal scheme. So nothing here applies to
it — `FormalSchemes.TateInvNodeChartHomExt` records why applying a mapping-out property of `Spf`
to the quotient is circular, and that is unchanged. What this does settle is the one side of the
comparison that is not circular: morphisms out of a formal spectrum into the chain itself *are*
compatible families of morphisms out of schemes.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6 (10.6.10).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace FormalSpectrum

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (q : R)
variable (hq : q ∈ I) (hI : I.FG)

/-- **The Tate chain `T_inv` is a target of the colimit property.** This is
`FormalSpectrum.isThickeningColimitTarget_formalScheme` at
`AlgebraicGeometry.tateChainInv_locallyFG`; the cover it consumes is the chain's own patches, so
this is a use of `FormalSpectrum.isThickeningColimitTarget_of_cover` at a target that no single
chart exhausts. -/
theorem isThickeningColimitTarget_tateChainInv :
    IsThickeningColimitTarget (tateChainInv R I q hq hI).toLocallyRingedSpace :=
  isThickeningColimitTarget_formalScheme _ (tateChainInv_locallyFG R I q hq hI)

/-- **EGA I, 10.6.10 at the Tate chain**: a compatible family `Spec (S ⧸ Jⁿ⁺¹) ⟶ T_inv` comes from
a unique `Spf J ⟶ T_inv`. -/
theorem existsUnique_hom_thickeningMap_tateChainInv {S : Type u} [CommRing S]
    [TopologicalSpace S] (J : Ideal S) [IsAdicRing J] (hJ : J.FG)
    (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (S ⧸ J ^ (n + 1))) ⟶
      (tateChainInv R I q hq hI).toLocallyRingedSpace)
    (hf : ∀ n : ℕ, Spec.locallyRingedSpaceMap (stepRingHom J n) ≫ f (n + 1) = f n) :
    ∃! g : locallyRingedSpaceObj J ⟶ (tateChainInv R I q hq hI).toLocallyRingedSpace,
      ∀ n : ℕ, thickeningMap J n ≫ g = f n :=
  existsUnique_hom_thickeningMap_of_isThickeningColimitTarget J f hf
    (isThickeningColimitTarget_tateChainInv R I q hq hI) hJ

end AlgebraicGeometry
