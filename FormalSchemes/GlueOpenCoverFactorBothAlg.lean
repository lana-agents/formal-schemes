import FormalSchemes.GlueOpenCoverFactorBoth
import FormalSchemes.GeneralFibreProductChartLift
import FormalSchemes.SpfGammaFunctorial

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Per-piece `R`-algebra data for the two-sided refined cover — the `chartLift` input

For a two-sided fibre-product datum `D : BothChartedFibreDatumXY R I hI` and a pair of morphisms
`a : Z ⟶ D.xGlued`, `b : Z ⟶ D.yGlued` out of a `LocallyFG` source `Z`, the common refinement
`FormalSchemes.GlueOpenCoverFactorBoth` (issue 412c Part 1) produces a cover
`bothRefinedCover D a b` of `Z` each of whose pieces `Spf S_c` maps, via `xFactor`/`yFactor`, into a
single `X`-chart
`Spf(A_i)` and a single `Y`-chart `Spf(B_j)` (`i = xIndex c`, `j = yIndex c`).

This file extracts, per piece, the **`R`-algebra data** that the affine mediating morphism
`BothChartedFibreDatumXY.chartLift` (issue 398) consumes: an `R`-algebra structure on the chart ring
`S_c`, the ideal-of-definition inequality `hIL`, and two `R`-algebra maps `xAlg c : A_i →ₐ[R] S_c`,
`yAlg c : B_j →ₐ[R] S_c`.

## The design (continuity-restricted regime, EGA I 10.4.6)

The chart ring `S_c := (bothRefinedChart c).R` is an *arbitrary* adic ring, so its `R`-algebra
structure is **constructed** from the structure morphism, not assumed. The composite
`Spf S_c ⟶ Z ⟶ Spf R` (via the `X`-leg `a ≫ D.xStructMap`) has a global-sections ring hom
`σ_c : R →+* S_c` (`refinedStructHom`), and we take `Algebra R S_c := σ_c.toAlgebra`
(`refinedAlgebra`). The two factorizations then give `A_i →+* S_c`, `B_j →+* S_c` (again by
`globalSectionsMap`), and these are automatically `R`-algebra maps: the commuting triangle is the
pure identity `map ≫ a ≫ xStructMap = xFactor ≫ xStructMapChart i` (from `xFactor_comp_ι` and
`ι_xStructMap`), pushed through the functoriality of `globalSectionsMap`; the `Y`-side uses the
cone-compatibility `hcomm : a ≫ xStructMap = b ≫ yStructMap`. **No continuity hypothesis is needed
for the algebra maps themselves.** The only continuity input is the single per-piece witness
`hs c : I ≤ L_c.comap σ_c`, which upgrades to `hIL c : I.map (algebraMap R S_c) ≤ L_c` — exactly the
`chartLift` precondition. This is the continuity an arbitrary LRS morphism into `Spf R` need not
satisfy (issue 156), threaded by the consumer (issues 234c/234d).

## Main definitions

* `BothChartedFibreDatumXY.refinedStructHom` / `refinedAlgebra`: `σ_c : R →+* S_c` and the induced
  `Algebra R S_c`.
* `BothChartedFibreDatumXY.refinedAlgebra_hIL`: `I.map (algebraMap R S_c) ≤ L_c` from the continuity
  witness `hs`.
* `BothChartedFibreDatumXY.xAlg` / `yAlg`: the `R`-algebra maps `A_i →ₐ[R] S_c`, `B_j →ₐ[R] S_c` —
  the `(f, g)` pair `chartLift` consumes.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4.6, §10.7.
-/

noncomputable section

open CategoryTheory TopologicalSpace Topology FormalSpectrum

universe u

namespace AlgebraicGeometry.BothChartedFibreDatumXY

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable [TopologicalSpace R] [IsAdicRing I]
variable {Z : FormalScheme.{u}} (D : BothChartedFibreDatumXY R I hI)
variable (a : Z.toLocallyRingedSpace ⟶ D.xGlued.toLocallyRingedSpace)
variable (b : Z.toLocallyRingedSpace ⟶ D.yGlued.toLocallyRingedSpace)
variable (hZ : Z.LocallyFG)

/-- The structure ring homomorphism `σ_c : R →+* S_c` of a refined-cover piece: the global-sections
map of the composite `Spf S_c ⟶ Z ⟶ Spf R` (the source cone over the base, via the `X`-leg). -/
def refinedStructHom (c : Z) :
    R →+* (D.bothRefinedChart a b hZ c).R :=
  globalSectionsMap I (D.bothRefinedChart a b hZ c).J
    ((D.bothRefinedChart a b hZ c).map ≫ a ≫ D.xStructMap)

/-- The `R`-algebra structure on the chart ring `S_c` of a refined-cover piece, induced by the
structure morphism `σ_c := refinedStructHom c`. -/
@[reducible]
def refinedAlgebra (c : Z) :
    Algebra R (D.bothRefinedChart a b hZ c).R :=
  (D.refinedStructHom a b hZ c).toAlgebra

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The `X`-leg factorization pushed to the base: on a refined-cover piece, the composite into the
base through `a` equals the composite through the selected `X`-chart's structure map. Pure identity
from `xFactor_comp_ι` (Part 1) and `ι_xStructMap`. -/
theorem map_comp_a_xStructMap_eq (c : Z) :
    letI := D.commRingA; letI := D.algebraA
    (D.bothRefinedChart a b hZ c).map ≫ a ≫ D.xStructMap =
      D.xFactor a b hZ c ≫ D.xStructMapChart (D.xIndex a b hZ c) := by
  letI := D.commRingA; letI := D.algebraA
  rw [← D.ι_xStructMap (D.xIndex a b hZ c), D.xFactor_comp_ι_assoc a b hZ c]
  exact (Category.assoc _ _ _).symm

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The `Y`-leg factorization pushed to the base, analogue of `map_comp_a_xStructMap_eq`. -/
theorem map_comp_b_yStructMap_eq (c : Z) :
    letI := D.commRingB; letI := D.algebraB
    (D.bothRefinedChart a b hZ c).map ≫ b ≫ D.yStructMap =
      D.yFactor a b hZ c ≫ D.yStructMapChart (D.yIndex a b hZ c) := by
  letI := D.commRingB; letI := D.algebraB
  rw [← D.ι_yStructMap (D.yIndex a b hZ c), D.yFactor_comp_ι_assoc a b hZ c]
  exact (Category.assoc _ _ _).symm

/-- `globalSectionsMap` of the `X`-chart structure map `xStructMapChart i` is the algebra map
`R → A_i`. -/
theorem globalSectionsMap_xStructMapChart (i : D.JX) :
    letI := D.commRingA; letI := D.algebraA; letI := D.topologyA; letI := D.isAdicA
    globalSectionsMap I (I.map (algebraMap R (D.A i))) (D.xStructMapChart i) =
      algebraMap R (D.A i) := by
  letI := D.commRingA; letI := D.algebraA; letI := D.topologyA; letI := D.isAdicA
  exact globalSectionsMap_locallyRingedSpaceMap I (I.map (algebraMap R (D.A i)))
    (algebraMap R (D.A i)) Ideal.le_comap_map

/-- `globalSectionsMap` of the `Y`-chart structure map `yStructMapChart j` is the algebra map
`R → B_j`. -/
theorem globalSectionsMap_yStructMapChart (j : D.JY) :
    letI := D.commRingB; letI := D.algebraB; letI := D.topologyB; letI := D.isAdicB
    globalSectionsMap I (I.map (algebraMap R (D.B j))) (D.yStructMapChart j) =
      algebraMap R (D.B j) := by
  letI := D.commRingB; letI := D.algebraB; letI := D.topologyB; letI := D.isAdicB
  exact globalSectionsMap_locallyRingedSpaceMap I (I.map (algebraMap R (D.B j)))
    (algebraMap R (D.B j)) Ideal.le_comap_map

/-- **The `X`-side per-piece `R`-algebra map** `xAlg c : A_i →ₐ[R] S_c` (`i = xIndex c`), the ring
hom `globalSectionsMap (I·A_i) L_c (xFactor c)` upgraded to an `R`-algebra map. The commuting
triangle is the pure factorization identity, so no continuity hypothesis is required. -/
def xAlg (c : Z) :
    letI := D.commRingA; letI := D.algebraA; letI := D.refinedAlgebra a b hZ c
    D.A (D.xIndex a b hZ c) →ₐ[R] (D.bothRefinedChart a b hZ c).R := by
  letI := D.commRingA; letI := D.algebraA; letI := D.topologyA; letI := D.isAdicA
  letI := D.refinedAlgebra a b hZ c
  let φ : D.A (D.xIndex a b hZ c) →+* (D.bothRefinedChart a b hZ c).R :=
    globalSectionsMap (I.map (algebraMap R (D.A (D.xIndex a b hZ c))))
      (D.bothRefinedChart a b hZ c).J (D.xFactor a b hZ c)
  refine { φ with commutes' := ?_ }
  intro r
  have hcomp : φ.comp (algebraMap R (D.A (D.xIndex a b hZ c))) =
        globalSectionsMap I (D.bothRefinedChart a b hZ c).J
          ((D.bothRefinedChart a b hZ c).map ≫ a ≫ D.xStructMap) := by
    rw [show φ = _ from rfl, ← D.globalSectionsMap_xStructMapChart (D.xIndex a b hZ c),
      ← globalSectionsMap_comp]
    exact congrArg (globalSectionsMap I (D.bothRefinedChart a b hZ c).J)
      (D.map_comp_a_xStructMap_eq a b hZ c).symm
  exact RingHom.congr_fun
    (hcomp.trans (RingHom.algebraMap_toAlgebra (D.refinedStructHom a b hZ c)).symm) r

/-- **The `Y`-side per-piece `R`-algebra map** `yAlg c : B_j →ₐ[R] S_c` (`j = yIndex c`), the
analogue of `xAlg`. Its commuting triangle uses the cone-compatibility
`hcomm : a ≫ xStructMap = b ≫ yStructMap` to identify the base composite through `b` with the one
through `a` defining the algebra. -/
def yAlg (c : Z)
    (hcomm : a ≫ D.xStructMap = b ≫ D.yStructMap) :
    letI := D.commRingB; letI := D.algebraB; letI := D.refinedAlgebra a b hZ c
    D.B (D.yIndex a b hZ c) →ₐ[R] (D.bothRefinedChart a b hZ c).R := by
  letI := D.commRingB; letI := D.algebraB; letI := D.topologyB; letI := D.isAdicB
  letI := D.refinedAlgebra a b hZ c
  let φ : D.B (D.yIndex a b hZ c) →+* (D.bothRefinedChart a b hZ c).R :=
    globalSectionsMap (I.map (algebraMap R (D.B (D.yIndex a b hZ c))))
      (D.bothRefinedChart a b hZ c).J (D.yFactor a b hZ c)
  refine { φ with commutes' := ?_ }
  intro r
  have hcomp : φ.comp (algebraMap R (D.B (D.yIndex a b hZ c))) =
        globalSectionsMap I (D.bothRefinedChart a b hZ c).J
          ((D.bothRefinedChart a b hZ c).map ≫ a ≫ D.xStructMap) := by
    rw [show φ = _ from rfl, ← D.globalSectionsMap_yStructMapChart (D.yIndex a b hZ c),
      ← globalSectionsMap_comp]
    refine congrArg (globalSectionsMap I (D.bothRefinedChart a b hZ c).J)
      ((D.map_comp_b_yStructMap_eq a b hZ c).symm.trans ?_)
    rw [hcomm]
  exact RingHom.congr_fun
    (hcomp.trans (RingHom.algebraMap_toAlgebra (D.refinedStructHom a b hZ c)).symm) r

/-- **The `chartLift` precondition `hIL`.** Given the continuity witness `hs : I ≤ L_c.comap σ_c`,
the ideal of definition `I·S_c` induced by the constructed `R`-algebra structure lies in `L_c`. -/
theorem refinedAlgebra_hIL (c : Z)
    (hs : I ≤ (D.bothRefinedChart a b hZ c).J.comap (D.refinedStructHom a b hZ c)) :
    letI := D.refinedAlgebra a b hZ c
    I.map (algebraMap R (D.bothRefinedChart a b hZ c).R) ≤ (D.bothRefinedChart a b hZ c).J := by
  letI := D.refinedAlgebra a b hZ c
  rw [show (algebraMap R (D.bothRefinedChart a b hZ c).R) = D.refinedStructHom a b hZ c from
    RingHom.algebraMap_toAlgebra _]
  exact Ideal.map_le_iff_le_comap.mpr hs

end AlgebraicGeometry.BothChartedFibreDatumXY

end
