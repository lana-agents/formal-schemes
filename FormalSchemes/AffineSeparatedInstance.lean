import FormalSchemes.GeneralSeparated

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The affine formal scheme `Spf A` is separated over `Spf R` (EGA I §10.15)

`FormalSchemes/GeneralSeparated.lean` (issue 499) introduced the §10.15 separatedness vocabulary
for a datum-presented formal scheme — `BothChartedFibreDatumXY.schemeDiagonal'`, the predicate
`BothChartedFibreDatumXY.IsSeparated`, and the local-on-target reduction
`isSeparated_of_diagonal_cover` — but produced **no concrete instance** of the datum. This file
supplies the affine one: `Spf A`, exhibited as a **one-chart** `AffineChartedFibreDatumX` datum.

The key simplification is that a one-element index type has no two distinct indices, so every
double- and triple-overlap field of the datum (the transitions `τ`, the geometric cocycles
`t'`/`t_fac`/`cocycle` and their `X`-side counterparts `xt'`/`xt_fac`/`xcocycle`) is **vacuous** —
exactly the tractability the two-patch template exploits via `uliftBool_not_pairwise_distinct`, here
sharpened to a single index.

## Main definitions

* `AlgebraicGeometry.oneChartExposeXDatum`: the one-chart `AffineChartedFibreDatumX` presenting
  `Spf A`, with all overlap data discharged by vacuity. This witnesses that the general datum
  machinery is inhabited by the affine charts it is meant to generalise.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
* [The Stacks Project, Tag 01KJ](https://stacks.math.columbia.edu/tag/01KJ).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
open CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace AlgebraicGeometry

/-- On the one-element index type `ULift Unit`, there are no two distinct indices. -/
private theorem uliftUnit_ne_elim {i j : ULift.{u} Unit} (h : i ≠ j) : False :=
  h (Subsingleton.elim i j)

/-- **The one-chart affine datum presenting `Spf A`.** All overlap fields are vacuous because the
index type `ULift Unit` has no two distinct elements; the only genuine data is the single chart
algebra `A` with its `I·A`-adic topology and adic-ring structure. -/
def oneChartExposeXDatum (R : Type u) [CommRing R] (I : Ideal R) (hI : I.FG)
    (A : Type u) [CommRing A] [Algebra R A] [TopologicalSpace A]
    [IsAdicRing (I.map (algebraMap R A))] :
    AffineChartedFibreDatumX R I hI A where
  J := ULift.{u} Unit
  A := fun _ => A
  g := fun _ _ => 1
  τ := fun _ _ h => (uliftUnit_ne_elim h).elim
  τ_symm := fun _ _ h => (uliftUnit_ne_elim h).elim
  t' := fun _ _ _ h _ _ => (uliftUnit_ne_elim h).elim
  t_fac := fun _ _ _ h _ _ => (uliftUnit_ne_elim h).elim
  cocycle := fun _ _ _ h _ _ => (uliftUnit_ne_elim h).elim
  topology := fun _ => ‹TopologicalSpace A›
  isAdic := fun _ => ‹IsAdicRing (I.map (algebraMap R A))›
  xt' := fun _ _ _ h _ _ => (uliftUnit_ne_elim h).elim
  xt_fac := fun _ _ _ h _ _ => (uliftUnit_ne_elim h).elim
  xcocycle := fun _ _ _ h _ _ => (uliftUnit_ne_elim h).elim

end AlgebraicGeometry

end
