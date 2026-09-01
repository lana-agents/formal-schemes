import FormalSchemes.TateFibreProductHom
import FormalSchemes.TateTopFiniteType

set_option linter.style.header false

/-!
# `𝔈_q` is separated and topologically of finite type — as statements about one object

Two properties of the Tate curve formal model were proved separately and, until this file, about
**different terms**:

* `tate_isSeparated` (`FormalSchemes.TateSeparatedValue`, issues 706/798) is about the datum
  `tateCurveExposeXDatum R I q B hq hI`, i.e. about its glued object
  `(tateCurveExposeXDatum …).xGlued`;
* `tateCurveModel_isRelativelyTopFiniteType` (`FormalSchemes.TateTopFiniteType`, issue 806) is
  about `tateCurveModel R I q hq hI`.

Those are the same formal scheme mathematically, but in Lean they are joined by 704's comparison
isomorphism `tateXGluedIso` (`FormalSchemes.TateXGluedIso`) and **not** by a definitional equality.
So no declaration asserted both properties of one object. This file transports the finite-type half
across that isomorphism, so that both now hold of `(tateCurveExposeXDatum …).xGlued` — the object
`tate_isSeparated` speaks about.

> **`𝔈_q` is a separated formal scheme, topologically of finite type over `Spf R`**, with no
> hypotheses beyond `hq : q ∈ I`, `hI : I.FG` and the ambient instances.

## Main results

* `AlgebraicGeometry.tateXGluedHom_comp_tateCurveModelStructMap`: 704's comparison isomorphism is
  a morphism over the base, in the direction this file needs.
* `AlgebraicGeometry.tateCurveExposeX_isRelativelyTopFiniteType`: the datum's glued object is
  topologically of finite type over `Spf R`, along the datum's own structural morphism.
* `AlgebraicGeometry.tateCurveExposeX_isLocallyTopFiniteType`: its object-level consequence.

## Implementation notes

`FormalSchemes.TateSeparatedValue` is deliberately **not** imported, even though the headline above
quotes it: its import closure is 214 modules against this file's 182, and nothing below needs the
separatedness statement to be proved — only to be cited. Following the same convention as
`TateTopFiniteType.lean`, the pairing is stated in prose and the separatedness half is referred to
by name.

The direction of 704's isomorphism is `tateXGluedIso : (tateCurveExposeXDatum …).xGlued ≅
tateCurveModel`, so `IsRelativelyTopFiniteType.of_iso` applies with `e := tateXGluedIso` and
produces a statement about `tateXGluedIso.hom ≫ Hom.mk (tateCurveModelStructMap …)`. Identifying
that composite with `Hom.mk ((tateCurveExposeXDatum …).xStructMap)` is
`tateXGluedHom_comp_tateCurveModelStructMap`, which is `tateXGluedInv_comp_xStructMap`
(`FormalSchemes.TateFibreProductHom`) cancelled against `tateXGluedIsoLRS.hom_inv_id`. The
`private` `tateXGluedHom_comp_inv` is not reachable from here, but the bundled iso's `hom_inv_id`
is the same equation.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.13, §10.15.
-/

noncomputable section

open CategoryTheory FormalSpectrum

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R]
variable (B : Type u) [CommRing B] [Algebra R B]

/-- **704's comparison isomorphism is a morphism over the base**, in the `hom` direction: the
identification of the datum's glued object with the Tate curve model, followed by the model's
structural morphism, is the datum's own structural morphism.

`tateXGluedInv_comp_xStructMap` is the same statement in the `Iso.inv` direction; the two are
related by cancelling `Iso.hom_inv_id` for `tateXGluedIsoLRS`. -/
theorem tateXGluedHom_comp_tateCurveModelStructMap (hq : q ∈ I) (hI : I.FG) :
    tateXGluedHom R I q B hq hI ≫ tateCurveModelStructMap R I q hq hI =
      (tateCurveExposeXDatum R I q B hq hI).xStructMap := by
  have hcancel : tateXGluedHom R I q B hq hI ≫ tateXGluedInv R I q B hq hI = 𝟙 _ :=
    (tateXGluedIsoLRS R I q B hq hI).hom_inv_id
  exact (congrArg (fun m : (tateCurveModel R I q hq hI).toLocallyRingedSpace ⟶
      locallyRingedSpaceObj I => tateXGluedHom R I q B hq hI ≫ m)
    (tateXGluedInv_comp_xStructMap R I q B hq hI)).symm.trans
    ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun m : (tateCurveExposeXDatum R I q B hq hI).xGlued.toLocallyRingedSpace ⟶
          (tateCurveExposeXDatum R I q B hq hI).xGlued.toLocallyRingedSpace =>
            m ≫ (tateCurveExposeXDatum R I q B hq hI).xStructMap) hcancel).trans
        (Category.id_comp _)))

/-- **The glued object of the Tate `X`-expose datum is topologically of finite type over
`Spf R`** (EGA I §10.13). This is `tateCurveModel_isRelativelyTopFiniteType` (issue 806)
transported across 704's comparison isomorphism, so that it holds of the *same* object as
`tate_isSeparated` (issues 706/798).

Together they say: **`𝔈_q` is a separated formal scheme, topologically of finite type over
`Spf R`.** -/
theorem tateCurveExposeX_isRelativelyTopFiniteType (hq : q ∈ I) (hI : I.FG) :
    FormalScheme.IsRelativelyTopFiniteType R I
      (FormalScheme.Hom.mk ((tateCurveExposeXDatum R I q B hq hI).xStructMap)) := by
  have hEq : (tateXGluedIso R I q B hq hI).hom ≫
      FormalScheme.Hom.mk (tateCurveModelStructMap R I q hq hI) =
      (FormalScheme.Hom.mk ((tateCurveExposeXDatum R I q B hq hI).xStructMap) :
        (tateCurveExposeXDatum R I q B hq hI).xGlued ⟶ FormalScheme.Spf I) := by
    refine FormalScheme.Hom.ext' ?_
    change (tateXGluedIso R I q B hq hI).hom.toLRSHom ≫ tateCurveModelStructMap R I q hq hI =
      (tateCurveExposeXDatum R I q B hq hI).xStructMap
    rw [show (tateXGluedIso R I q B hq hI).hom.toLRSHom = tateXGluedHom R I q B hq hI from
      forgetToLocallyRingedSpace_map_tateXGluedIso_hom R I q B hq hI]
    exact tateXGluedHom_comp_tateCurveModelStructMap R I q B hq hI
  exact hEq ▸ FormalScheme.IsRelativelyTopFiniteType.of_iso
    (tateCurveModel_isRelativelyTopFiniteType R I q hq hI) (tateXGluedIso R I q B hq hI)

/-- **The glued object of the Tate `X`-expose datum is locally topologically of finite type over
`(R, I)`**, the object-level form of `tateCurveExposeX_isRelativelyTopFiniteType`. -/
theorem tateCurveExposeX_isLocallyTopFiniteType (hq : q ∈ I) (hI : I.FG) :
    FormalScheme.IsLocallyTopFiniteType R I
      ((tateCurveExposeXDatum R I q B hq hI).xGlued) :=
  (tateCurveExposeX_isRelativelyTopFiniteType R I q B hq hI).isLocallyTopFiniteType

end AlgebraicGeometry

end
