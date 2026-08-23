import FormalSchemes.AffineSeparatedValue
import FormalSchemes.GeneralSeparatedScheme

set_option linter.style.header false

/-!
# `Spf A` is separated over `Spf R`, as a formal scheme (EGA I §10.15)

`FormalSchemes.GeneralSeparatedScheme` introduced `FormalScheme.IsSeparatedOverSpf X s`, the
scheme-level separatedness predicate, and proved that any affine charted presentation of `X` over
`s` computes it — but supplied **no value**, so nothing inhabited it. This file supplies the first
one, the affine case:

```
spf_isSeparatedOverSpf :
  FormalScheme.IsSeparatedOverSpf hI (FormalScheme.Spf (I·A)) (Spf A ⟶ Spf R)
```

**This is the first statement in the tree that a formal scheme is separated without naming any
charts.** It is the affine case of §10.15, and it says of the *object* `Spf A` what
`oneChart_isSeparated` (`FormalSchemes.AffineSeparatedValue`) says of the one-chart presentation.

## The bridge

`oneChart_isSeparated` is a value about the presentation `oneChartExposeXDatum R I hI A`, and
`oneChartXGluedIso` (`FormalSchemes.AffineSeparatedIso`) identifies that presentation's glued object
with `Spf A`. What `FormalScheme.isSeparatedOverSpf_iff` additionally needs is that the
identification lies **over the base**, and that is `oneChartXGluedIso_hom_comp_structMap`, supplied
here.

It is short, because the load-bearing half already exists: `oneChartXGluedIso_inv_toLRSHom`
(`FormalSchemes.AffineSeparatedValue`) computes the isomorphism's inverse leg as the single chart
inclusion `ι`, and `AffineChartedFibreDatumX.ι_xStructMap` says the glued structural morphism
restricts along `ι` to the per-chart one. On a one-element index the per-chart structural morphism
*is* the structural morphism of `Spf A` over `Spf R` — `oneChartXStructMapChart`, which is `rfl`.
Everything else is `Iso.inv_comp_eq`.

The two steps are stated in the inverse spelling (`oneChartXGluedIso_inv_comp_xStructMap`) and the
forward one (`oneChartXGluedIso_hom_comp_structMap`) separately, and both proofs are term-mode. A
tactic proof that reassociates the composite by `rw` hits the `instances`-transparency wall
described in `FormalSchemes.GeneralSeparatedPresentation`'s module docstring: the index `⟨⟨⟩⟩` is
elaborated at `(oneChartExposeXDatum …).J` on one side of the rewrite and at the glue datum's own
index type on the other, and `rw` will not build a motive across that. `congrArg (· ≫ _)` and
`Iso.inv_comp_eq` are checked at default transparency and go through untouched.

## The hypotheses this value does *not* carry

`oneChart_isSeparated` needs `[IsAdicRing (CompletedTensorProduct.idealOfDefinition R I A A)]`,
because its proof runs through the affine diagonal of `Spf (A ⊗̂_R A)`. That instance is
**discharged** here by `CompletedTensorProduct.isAdicRing`, which needs only `hI : I.FG`, so
`spf_isSeparatedOverSpf` assumes nothing beyond what naming `Spf A` over `Spf R` already requires.
The statement never mentions the completed tensor product, so there was no reason to inherit it.

## What this does not do

`BothChartedFibreDatumXY.IsSeparated` and every existing value are untouched; nothing is deprecated
and no consumer moves. The two remaining values are the identical shape and each is its own piece of
work, not done here:

* `𝔈_q`, from `tate_isSeparated` (`FormalSchemes.TateSeparatedValue`) — a heavier import closure, so
  it belongs in its own module rather than this one;
* the three-chart open cover, from `datumX_isSeparated`
  (`FormalSchemes.ThreeChartCoverSeparated`) — note `ThreeChartCoverCharts` is a known
  memory-ceiling module, so measure before importing anything near it.

Each needs the analogue of `oneChartXGluedIso_hom_comp_structMap` for its own gluing isomorphism;
neither of those compatibilities exists yet.

## Main results

* `oneChartXStructMapChart`: on the one-chart datum, the per-chart structural morphism is the
  structural morphism of `Spf A` over `Spf R`.
* `oneChartXGluedIso_inv_comp_xStructMap`, `oneChartXGluedIso_hom_comp_structMap`: the one-chart
  gluing isomorphism lies over `Spf R`.
* `spf_isSeparatedOverSpf`: **`Spf A` is separated over `Spf R`**, as a formal scheme.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum
open CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {I : Ideal R} (hI : I.FG)
variable [TopologicalSpace R] [IsAdicRing I]
variable {A : Type u} [CommRing A] [Algebra R A] [TopologicalSpace A]
variable [IsAdicRing (I.map (algebraMap R A))]

/-- The one-chart index type has no two distinct elements. Stated at the datum's own index type
`(oneChartExposeXDatum R I hI A).J`, matching `FormalSchemes.AffineSeparatedValue`'s private copy,
so that the vacuous overlap data built from it is the same term. -/
private theorem oneChartUnitNeElim {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
    {A : Type u} [CommRing A] [Algebra R A] [TopologicalSpace A]
    [IsAdicRing (I.map (algebraMap R A))]
    {i j : (oneChartExposeXDatum R I hI A).J} (h : i ≠ j) : False :=
  h (Subsingleton.elim (α := ULift.{u} Unit) i j)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The one-chart datum's per-chart structural morphism is the structural morphism of `Spf A`.**
There is only one chart and its algebra is `A` itself, so `xStructMapChart` unfolds to the map of
formal spectra induced by `algebraMap R A`. This is what makes `spf_isSeparatedOverSpf` a statement
about the structural morphism a reader would write down, rather than about a chart artefact. -/
theorem oneChartXStructMapChart :
    (oneChartExposeXDatum R I hI A).xStructMapChart ⟨⟨⟩⟩ =
      locallyRingedSpaceMap I (I.map (algebraMap R A)) (algebraMap R A) Ideal.le_comap_map :=
  rfl

/-- **The one-chart gluing isomorphism lies over `Spf R`**, inverse spelling: its inverse followed
by the glued structural morphism is the structural morphism of `Spf A`.

The inverse leg is the single chart inclusion `ι` (`oneChartXGluedIso_inv_toLRSHom`), along which
the glued structural morphism restricts to the per-chart one (`ι_xStructMap`), which is the
structural morphism of `Spf A` (`oneChartXStructMapChart`, `rfl`). -/
theorem oneChartXGluedIso_inv_comp_xStructMap :
    (oneChartXGluedIso hI (A := A)).inv.toLRSHom ≫ (oneChartExposeXDatum R I hI A).xStructMap =
      locallyRingedSpaceMap I (I.map (algebraMap R A)) (algebraMap R A) Ideal.le_comap_map :=
  (congrArg (· ≫ (oneChartExposeXDatum R I hI A).xStructMap)
    (oneChartXGluedIso_inv_toLRSHom hI)).trans
      ((oneChartExposeXDatum R I hI A).ι_xStructMap ⟨⟨⟩⟩)

/-- **The one-chart gluing isomorphism lies over `Spf R`**, forward spelling: this is the
compatibility `FormalScheme.isSeparatedOverSpf_iff` consumes, so it is stated in that shape.

`Iso.inv_comp_eq` at the locally-ringed-space isomorphism underlying `oneChartXGluedIso` turns the
inverse spelling into this one; the `Functor.mapIso` wrapper is definitionally
`FormalScheme.Hom.toLRSHom` on both legs. -/
theorem oneChartXGluedIso_hom_comp_structMap :
    (oneChartXGluedIso hI (A := A)).hom.toLRSHom ≫
        locallyRingedSpaceMap I (I.map (algebraMap R A)) (algebraMap R A) Ideal.le_comap_map =
      (oneChartExposeXDatum R I hI A).xStructMap :=
  ((Iso.inv_comp_eq
    (FormalScheme.forgetToLocallyRingedSpace.mapIso (oneChartXGluedIso hI (A := A)))).mp
      (oneChartXGluedIso_inv_comp_xStructMap hI)).symm

/-- **`Spf A` is separated over `Spf R`** (EGA I §10.15), as a property of the formal scheme
`Spf A` and its structural morphism — no chart data appears in the statement.

This is the first inhabitant of `FormalScheme.IsSeparatedOverSpf`. It is `oneChart_isSeparated`, the
value about the one-chart *presentation*, read through `FormalScheme.isSeparatedOverSpf_iff` at the
gluing isomorphism `oneChartXGluedIso` and its structural compatibility. -/
theorem spf_isSeparatedOverSpf :
    FormalScheme.IsSeparatedOverSpf hI (FormalScheme.Spf (I.map (algebraMap R A)))
      (locallyRingedSpaceMap I (I.map (algebraMap R A)) (algebraMap R A) Ideal.le_comap_map) := by
  haveI := CompletedTensorProduct.isAdicRing R I A A hI
  exact (FormalScheme.isSeparatedOverSpf_iff hI (oneChartExposeXDatum R I hI A)
    (fun _ _ _ h _ _ => (oneChartUnitNeElim h).elim)
    (fun _ _ _ h _ _ => (oneChartUnitNeElim h).elim)
    (fun _ _ _ h _ _ => (oneChartUnitNeElim h).elim)
    (FormalScheme.forgetToLocallyRingedSpace.mapIso (oneChartXGluedIso hI))
    (oneChartXGluedIso_hom_comp_structMap hI)).mpr (oneChart_isSeparated hI)

end AlgebraicGeometry

end
