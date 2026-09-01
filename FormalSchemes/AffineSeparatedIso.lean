import FormalSchemes.AffineSeparatedInstance

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The one-chart gluing isomorphisms for `Spf A`'s separatedness (EGA I §10.15)

`FormalSchemes/AffineSeparatedInstance.lean` (issue 506) presented `Spf A` as a **one-chart**
`AffineChartedFibreDatumX` datum, `oneChartExposeXDatum`. Its glued object `xGlued` and the glued
fibre product `generalFibreProduct` of the associated `diagonalDatum` are built through
`GlueData.ofGlueData'` → `gluedFormalScheme` over a **one-element** index, so each is only
*isomorphic* to its single chart, not definitionally equal.

This file supplies the two identifying isomorphisms, which the affine
`BothChartedFibreDatumXY.IsSeparated` value (the follow-up 506c) transports the affine diagonal
closed-immersion across:

* `oneChartXGluedIso : (oneChartExposeXDatum …).xGlued ≅ Spf A`;
* `oneChartFibreProductIso : (diagonalDatum (oneChartExposeXDatum …) …).generalFibreProduct
  ≅ Spf (A ⊗̂_R A)`.

Both rest on the reusable `FormalScheme.GlueData.isIso_ι_of_subsingleton`: when a glue datum's
index type has at most one element, the single chart inclusion `ι i` is an isomorphism (an open
immersion whose base is surjective, because that one chart already covers the whole space). The
fully faithful forgetful functor `forgetToLocallyRingedSpace` then lifts the locally-ringed-space
isomorphism to a `FormalScheme` isomorphism.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
* [The Stacks Project, Tag 01KJ](https://stacks.math.columbia.edu/tag/01KJ).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
open CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace AlgebraicGeometry

/-- **A subsingleton-index glue datum's chart inclusion is an isomorphism.** If the index type of a
`FormalScheme.GlueData` has at most one element, the single chart already covers the whole glued
space, so the open immersion `ι i` is surjective on points, hence an isomorphism of locally ringed
spaces. -/
theorem FormalScheme.GlueData.isIso_ι_of_subsingleton (D : FormalScheme.GlueData.{u})
    [Subsingleton D.toLocallyRingedSpaceGlueData.J]
    (i : D.toLocallyRingedSpaceGlueData.J) : IsIso (D.ι i) := by
  haveI : Epi (D.ι i).base := by
    rw [TopCat.epi_iff_surjective]
    intro x
    obtain ⟨j, y, rfl⟩ := D.ι_jointly_surjective x
    obtain rfl := Subsingleton.elim j i
    exact ⟨y, rfl⟩
  exact LocallyRingedSpace.IsOpenImmersion.to_iso (D.ι i)

variable {R : Type u} [CommRing R] {I : Ideal R} (hI : I.FG)
variable [TopologicalSpace R] [IsAdicRing I]
variable {A : Type u} [CommRing A] [Algebra R A] [TopologicalSpace A]
variable [IsAdicRing (I.map (algebraMap R A))]

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The one-chart glued object `xGlued` of `Spf A` is `Spf A`.** The one-element index has a
single chart which already covers `xGlued`, so its inclusion `ι default` is an isomorphism; the
fully faithful forgetful functor lifts it to a `FormalScheme` iso.

The base `R` carries no topology and no adic hypothesis here: only the chart algebra `A` has to be
an adic ring. That matters for `FormalSchemes/CompletionAsChartedGlued.lean`, which instantiates
this at `A := R^` over a base `R` that is not complete. -/
def oneChartXGluedIso :
    (oneChartExposeXDatum R I hI A).xGlued ≅ FormalScheme.Spf (I.map (algebraMap R A)) := by
  let d : (oneChartExposeXDatum R I hI A).xFormalGlueData.toLocallyRingedSpaceGlueData.J := ⟨⟨⟩⟩
  haveI : Subsingleton
      (oneChartExposeXDatum R I hI A).xFormalGlueData.toLocallyRingedSpaceGlueData.J :=
    inferInstanceAs (Subsingleton (ULift Unit))
  haveI hi : IsIso ((oneChartExposeXDatum R I hI A).xFormalGlueData.ι d) :=
    FormalScheme.GlueData.isIso_ι_of_subsingleton
      (oneChartExposeXDatum R I hI A).xFormalGlueData d
  exact ((Functor.FullyFaithful.ofFullyFaithful FormalScheme.forgetToLocallyRingedSpace).preimageIso
    (X := FormalScheme.Spf (I.map (algebraMap R A)))
    (Y := (oneChartExposeXDatum R I hI A).xGlued)
    (@asIso _ _ _ _ ((oneChartExposeXDatum R I hI A).xFormalGlueData.ι d) hi)).symm

/-- The vacuous double-overlap `σ`-datum of the one-chart datum: the one-element index has no two
distinct elements, so every hypothesis is contradictory. -/
private theorem oneChartUnit_ne_elim {i j : ULift.{u} Unit} (h : i ≠ j) : False :=
  h (Subsingleton.elim i j)

variable [IsAdicRing (CompletedTensorProduct.idealOfDefinition R I A A)]

/-- **The one-chart fibre product `X ×_{Spf R} X` of `Spf A` is `Spf (A ⊗̂_R A)`.** The associated
`diagonalDatum` glues over the one-element product index `ULift Unit × ULift Unit`; its single
product chart `Spf (idealOfDefinition R I A A)` already covers the glued object, so the inclusion is
an isomorphism, lifted to a `FormalScheme` iso as in `oneChartXGluedIso`. -/
def oneChartFibreProductIso :
    (BothChartedFibreDatumXY.diagonalDatum (oneChartExposeXDatum R I hI A)
        (fun _ _ _ h _ _ => (oneChartUnit_ne_elim h).elim)
        (fun _ _ _ h _ _ => (oneChartUnit_ne_elim h).elim)
        (fun _ _ _ h _ _ =>
          (oneChartUnit_ne_elim h).elim)).toBothChartedFibreDatum.generalFibreProduct ≅
      FormalScheme.Spf (CompletedTensorProduct.idealOfDefinition R I A A) := by
  set D2 := (BothChartedFibreDatumXY.diagonalDatum (oneChartExposeXDatum R I hI A)
      (fun _ _ _ h _ _ => (oneChartUnit_ne_elim h).elim)
      (fun _ _ _ h _ _ => (oneChartUnit_ne_elim h).elim)
      (fun _ _ _ h _ _ => (oneChartUnit_ne_elim h).elim)).toBothChartedFibreDatum
  let d : D2.formalGlueData.toLocallyRingedSpaceGlueData.J := ⟨⟨⟨⟩⟩, ⟨⟨⟩⟩⟩
  haveI : Subsingleton D2.formalGlueData.toLocallyRingedSpaceGlueData.J :=
    inferInstanceAs (Subsingleton (ULift Unit × ULift Unit))
  haveI hi : IsIso (D2.formalGlueData.ι d) :=
    FormalScheme.GlueData.isIso_ι_of_subsingleton D2.formalGlueData d
  exact ((Functor.FullyFaithful.ofFullyFaithful FormalScheme.forgetToLocallyRingedSpace).preimageIso
    (X := D2.generalFibreProduct)
    (Y := FormalScheme.Spf (CompletedTensorProduct.idealOfDefinition R I A A))
    (asIso (D2.formalGlueData.ι d)).symm)

end AlgebraicGeometry

end
