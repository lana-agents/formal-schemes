import FormalSchemes.AffineSeparatedValue
import FormalSchemes.GeneralSeparatedTopological

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The affine `BothChartedFibreDatumXY.IsSeparated` value, seen through the topological criterion

`FormalSchemes/AffineSeparatedValue.lean` (issue 513) proved that `Spf A` is separated over `Spf R`
by transporting the affine diagonal's closed immersion across the one-chart gluing isomorphisms.
`FormalSchemes/GeneralSeparatedTopological.lean` characterises separatedness of *any*
datum-presented formal scheme as a purely topological condition on the diagonal's base map. This
file applies the characterisation to the one existing `BothChartedFibreDatumXY.IsSeparated` value,
which both validates the new API against a concrete datum and extracts a fact not previously stated:
the base map of the one-chart general diagonal is a closed topological embedding.

Note that the vacuity lemma `oneChartNeElim'` is restated here at the datum's own index type
`(oneChartExposeXDatum R I hI A).J` rather than at `ULift Unit`; as recorded in issue 513, the
`ULift Unit` phrasing is only defeq at default transparency and makes goals mentioning the resulting
datum fail to elaborate at `instances` transparency.

## Main results

* `AlgebraicGeometry.oneChart_isClosedEmbedding_diagonal_base`: the base map of the general diagonal
  of the one-chart datum presenting `Spf A` is a closed embedding.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
* [The Stacks Project, Tag 01KJ](https://stacks.math.columbia.edu/tag/01KJ).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum Topology
open CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {I : Ideal R} (hI : I.FG)
variable [TopologicalSpace R] [IsAdicRing I]
variable {A : Type u} [CommRing A] [Algebra R A] [TopologicalSpace A]
variable [IsAdicRing (I.map (algebraMap R A))]
variable [IsAdicRing (CompletedTensorProduct.idealOfDefinition R I A A)]

/-- The one-chart index type has no two distinct elements, stated at the datum's own index type
(see the module docstring). -/
private theorem oneChartNeElim' {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
    {A : Type u} [CommRing A] [Algebra R A] [TopologicalSpace A]
    [IsAdicRing (I.map (algebraMap R A))]
    {i j : (oneChartExposeXDatum R I hI A).J} (h : i ≠ j) : False :=
  h (Subsingleton.elim (α := ULift.{u} Unit) i j)

/-- **The base map of the one-chart general diagonal is a closed embedding**: `Spf A` is separated
over `Spf R` (issue 513), and separatedness is exactly this topological condition. -/
theorem oneChart_isClosedEmbedding_diagonal_base :
    IsClosedEmbedding ⇑(BothChartedFibreDatumXY.schemeDiagonal' (oneChartExposeXDatum R I hI A)
      (fun _ _ _ h _ _ => (oneChartNeElim' h).elim)
      (fun _ _ _ h _ _ => (oneChartNeElim' h).elim)
      (fun _ _ _ h _ _ => (oneChartNeElim' h).elim)).toLRSHom.base :=
  (BothChartedFibreDatumXY.isSeparated_iff_isClosedEmbedding_diagonal_base _ _ _ _).mp
    (oneChart_isSeparated hI)

end AlgebraicGeometry

end
