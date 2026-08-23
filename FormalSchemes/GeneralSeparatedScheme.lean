import FormalSchemes.GeneralSeparatedPresentation

set_option linter.style.header false

/-!
# Separatedness as a property of the formal scheme

`BothChartedFibreDatumXY.IsSeparated DX σX hστX hσcX` (`FormalSchemes.GeneralSeparated`) is a
predicate on a **presentation**: an affine charted datum together with its double-overlap cocycle
data. `FormalSchemes.GeneralSeparatedPresentation` shows that two presentations whose glued factors
are isomorphic over `Spf R` are separated or not together. This file draws the conclusion and
states separatedness as a predicate on the formal scheme and its structural morphism:

```
X.IsSeparatedOverSpf hI s ↔ IsSeparated DX σX hστX hσcX   for any presentation of `X` over `s`
```

`IsSeparatedOverSpf` quantifies existentially over presentations, and `isSeparatedOverSpf_iff` says
the choice does not matter — *any* presentation computes it. That equivalence is exactly what the
presentation-independence theorem is for; without it the existential would be a weaker statement
than the predicate it is meant to replace.

The declaration a reader of EGA I §10.15 will quote is `isSeparatedOverSpf_of_iso`: separatedness
over `Spf R` transports along an isomorphism of formal schemes over the base, with no chart data
anywhere in the statement.

## What this does not do

`BothChartedFibreDatumXY.IsSeparated` is **untouched**, nothing is deprecated, and no existing
consumer moves. Every concrete value in the tree — `oneChart_isSeparated`
(`FormalSchemes.AffineSeparatedValue`), `tate_isSeparated` (`FormalSchemes.TateSeparatedValue`),
`datumX_isSeparated` (`FormalSchemes.ThreeChartCoverSeparated`) — still proves the
presentation-level predicate, and enters this vocabulary through
`isSeparatedOverSpf_of_isSeparated` without being edited. Whether the presentation-level
predicate should eventually be retired in favour of this one is a separate question, and one that
should be argued against real consumers.

There is also **no concrete value here**, deliberately: the values live downstream, in the modules
that own the objects they are about. There are three.

* `Spf A` — `spf_isSeparatedOverSpf` (`FormalSchemes.AffineSeparatedScheme`), read off
  `oneChart_isSeparated` through the one-chart gluing isomorphism `oneChartXGluedIso`
  (`FormalSchemes.AffineSeparatedIso`) and its structural compatibility
  `oneChartXGluedIso_hom_comp_structMap`.
* `𝔈_q` — `tateCurveModel_isSeparatedOverSpf` (`FormalSchemes.TateSeparatedScheme`).
* The three-chart open cover — `datumX_isSeparatedOverSpf` and `gluedX_isSeparatedOverSpf`
  (`FormalSchemes.ThreeChartCoverSeparatedScheme`), restated chart-free as
  `ThreeChartCover.coverSubscheme_isSeparatedOverSpf`
  (`FormalSchemes.ThreeChartCoverOpenSubscheme`).

## Main results

* `FormalScheme.IsSeparatedOverSpf`: `X` is separated over `s : X ⟶ Spf R` when some affine charted
  presentation of `X` compatible with `s` is separated.
* `FormalScheme.isSeparatedOverSpf_iff`: **any** presentation computes it.
* `FormalScheme.isSeparatedOverSpf_of_isSeparated`: a presentation-level value enters the
  scheme-level vocabulary.
* `FormalScheme.isSeparatedOverSpf_of_iso`, `FormalScheme.isSeparatedOverSpf_iff_of_iso`:
  **separatedness transports along an isomorphism over the base**, stated without charts.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum
open CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace AlgebraicGeometry.FormalScheme

variable {R : Type u} [CommRing R] {I : Ideal R} (hI : I.FG)
variable [TopologicalSpace R] [IsAdicRing I]

/-- **`X` is separated over `Spf R`** (EGA I §10.15), as a property of the formal scheme `X` and its
structural morphism `s`: some affine charted datum whose glued object is isomorphic to `X` over `s`
is separated in the sense of `BothChartedFibreDatumXY.IsSeparated`.

The existential is harmless because `isSeparatedOverSpf_iff` shows every presentation of `X` over
`s` computes this predicate, not merely the witnessing one.

Note what else the existential asserts: that `X` *admits* an affine charted presentation over `s` at
all. `FormalScheme` only asks that `X` be locally isomorphic to some `Spf`, whereas a presentation
additionally demands a single chart family over the same base `R` whose overlaps are basic opens, so
this predicate is false — not merely unproved — for a formal scheme carrying no such presentation.
Every formal scheme in this development is built from charted data, so no consumer is affected. -/
def IsSeparatedOverSpf (X : FormalScheme.{u})
    (s : X.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I) : Prop :=
  ∃ (BX : Type u) (_ : CommRing BX) (_ : Algebra R BX)
    (DX : AffineChartedFibreDatumX R I hI BX)
    (σX : letI := DX.commRing; letI := DX.algebra;
      ∀ (i i' i'' : DX.J), i ≠ i' → i ≠ i'' → i' ≠ i'' →
      (awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i i' * DX.g i i'') ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (DX.A i'))) (DX.g i' i'' * DX.g i' i)))
    (hστX : letI := DX.commRing; letI := DX.algebra;
      ∀ (i i' i'' : DX.J) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
      (σX i i' i'' h1 h2 h3).symm.toAlgHom.comp (furtherLocSnd I (DX.g i' i'') (DX.g i' i) hI) =
        (furtherLocFst I (DX.g i i') (DX.g i i'') hI).comp (DX.τ i i' h1).symm.toAlgHom)
    (hσcX : letI := DX.commRing; letI := DX.algebra;
      ∀ (i i' i'' : DX.J) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
      (σX i i' i'' h1 h2 h3).trans ((σX i' i'' i h3 h1.symm h2.symm).trans
        (σX i'' i i' h2.symm h3.symm h1)) =
        AlgEquiv.refl (R := R)
          (A₁ := awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i i' * DX.g i i'')))
    (e : DX.xGlued.toLocallyRingedSpace ≅ X.toLocallyRingedSpace),
    e.hom ≫ s = DX.xStructMap ∧ BothChartedFibreDatumXY.IsSeparated DX σX hστX hσcX

variable {BX : Type u} [CommRing BX] [Algebra R BX]

/-- **Any presentation computes scheme-level separatedness.** Given one affine charted presentation
`DX` of `X` over `s`, the existential predicate `IsSeparatedOverSpf` holds exactly when *that*
presentation is separated.

The forward direction is the whole content: a witnessing presentation `DX'` need have nothing to do
with `DX`, and what identifies them is the presentation-independence theorem
`BothChartedFibreDatumXY.isSeparated_iff_of_xGlued_iso` applied to the composite isomorphism
`e' ≫ e⁻¹` of the two glued factors. The backward direction is the anonymous constructor. -/
theorem isSeparatedOverSpf_iff {X : FormalScheme.{u}}
    {s : X.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I}
    (DX : AffineChartedFibreDatumX R I hI BX)
    (σX : letI := DX.commRing; letI := DX.algebra;
      ∀ (i i' i'' : DX.J), i ≠ i' → i ≠ i'' → i' ≠ i'' →
      (awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i i' * DX.g i i'') ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (DX.A i'))) (DX.g i' i'' * DX.g i' i)))
    (hστX : letI := DX.commRing; letI := DX.algebra;
      ∀ (i i' i'' : DX.J) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
      (σX i i' i'' h1 h2 h3).symm.toAlgHom.comp (furtherLocSnd I (DX.g i' i'') (DX.g i' i) hI) =
        (furtherLocFst I (DX.g i i') (DX.g i i'') hI).comp (DX.τ i i' h1).symm.toAlgHom)
    (hσcX : letI := DX.commRing; letI := DX.algebra;
      ∀ (i i' i'' : DX.J) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
      (σX i i' i'' h1 h2 h3).trans ((σX i' i'' i h3 h1.symm h2.symm).trans
        (σX i'' i i' h2.symm h3.symm h1)) =
        AlgEquiv.refl (R := R)
          (A₁ := awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i i' * DX.g i i'')))
    (e : DX.xGlued.toLocallyRingedSpace ≅ X.toLocallyRingedSpace)
    (he : e.hom ≫ s = DX.xStructMap) :
    IsSeparatedOverSpf hI X s ↔ BothChartedFibreDatumXY.IsSeparated DX σX hστX hσcX := by
  constructor
  · rintro ⟨BX', _, _, DX', σX', hστX', hσcX', e', he', hsep'⟩
    refine (BothChartedFibreDatumXY.isSeparated_iff_of_xGlued_iso DX' σX' hστX' hσcX'
      DX σX hστX hσcX (e'.trans e.symm) ?_).mp hsep'
    rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← he, Iso.inv_hom_id_assoc]
    exact he'
  · exact fun h => ⟨BX, inferInstance, inferInstance, DX, σX, hστX, hσcX, e, he, h⟩

/-- **A presentation-level separatedness value enters the scheme-level vocabulary.** Its own glued
object, with its own structural morphism, is separated over `Spf R`. This is how every concrete
value in the tree reaches `IsSeparatedOverSpf` without being edited. -/
theorem isSeparatedOverSpf_of_isSeparated
    (DX : AffineChartedFibreDatumX R I hI BX)
    (σX : letI := DX.commRing; letI := DX.algebra;
      ∀ (i i' i'' : DX.J), i ≠ i' → i ≠ i'' → i' ≠ i'' →
      (awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i i' * DX.g i i'') ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (DX.A i'))) (DX.g i' i'' * DX.g i' i)))
    (hστX : letI := DX.commRing; letI := DX.algebra;
      ∀ (i i' i'' : DX.J) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
      (σX i i' i'' h1 h2 h3).symm.toAlgHom.comp (furtherLocSnd I (DX.g i' i'') (DX.g i' i) hI) =
        (furtherLocFst I (DX.g i i') (DX.g i i'') hI).comp (DX.τ i i' h1).symm.toAlgHom)
    (hσcX : letI := DX.commRing; letI := DX.algebra;
      ∀ (i i' i'' : DX.J) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
      (σX i i' i'' h1 h2 h3).trans ((σX i' i'' i h3 h1.symm h2.symm).trans
        (σX i'' i i' h2.symm h3.symm h1)) =
        AlgEquiv.refl (R := R)
          (A₁ := awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i i' * DX.g i i'')))
    (h : BothChartedFibreDatumXY.IsSeparated DX σX hστX hσcX) :
    IsSeparatedOverSpf hI DX.xGlued DX.xStructMap :=
  ⟨BX, inferInstance, inferInstance, DX, σX, hστX, hσcX, Iso.refl _, Category.id_comp _, h⟩

/-- **Separatedness over `Spf R` transports along an isomorphism over the base.** No chart data
appears in this statement: it is a property of a formal scheme and its structural morphism, which is
what the presentation-independence theorem of `FormalSchemes.GeneralSeparatedPresentation` was for.

A presentation of `X` over `sX` is a presentation of `Y` over `sY` after composing the witnessing
isomorphism with `f`. -/
theorem isSeparatedOverSpf_of_iso {X Y : FormalScheme.{u}}
    {sX : X.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I}
    {sY : Y.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I}
    (f : X.toLocallyRingedSpace ≅ Y.toLocallyRingedSpace) (hf : f.hom ≫ sY = sX)
    (h : IsSeparatedOverSpf hI X sX) : IsSeparatedOverSpf hI Y sY := by
  obtain ⟨BX', _, _, DX', σX', hστX', hσcX', e, he, hsep⟩ := h
  refine ⟨BX', inferInstance, inferInstance, DX', σX', hστX', hσcX', e.trans f, ?_, hsep⟩
  rw [Iso.trans_hom, Category.assoc, hf]
  exact he

/-- **Separatedness over `Spf R` is invariant under isomorphism over the base**, the `Iff` form of
`isSeparatedOverSpf_of_iso`. The backward direction is the forward one at `f.symm`, whose base
compatibility is `Iso.inv_comp_eq`. -/
theorem isSeparatedOverSpf_iff_of_iso {X Y : FormalScheme.{u}}
    {sX : X.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I}
    {sY : Y.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I}
    (f : X.toLocallyRingedSpace ≅ Y.toLocallyRingedSpace) (hf : f.hom ≫ sY = sX) :
    IsSeparatedOverSpf hI X sX ↔ IsSeparatedOverSpf hI Y sY :=
  ⟨isSeparatedOverSpf_of_iso hI f hf,
    isSeparatedOverSpf_of_iso hI f.symm ((Iso.inv_comp_eq f).mpr hf.symm)⟩

end AlgebraicGeometry.FormalScheme

end
