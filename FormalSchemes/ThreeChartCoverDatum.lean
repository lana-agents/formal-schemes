import FormalSchemes.ThreeChartCoverTransitions

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The three-chart open-cover datum: `Spf A` presented by three basic opens

Issue 594 (`FormalSchemes.ThreeChartDatum`) gave the first `AffineChartedFibreDatumX` on a
three-element index type, but in the shape "three copies of `Spf A` glued along `D(f_i·f_j)`":
every chart algebra there is literally `A`, and the glued object is a genuinely non-separated
formal scheme. This file assembles the other three-chart shape, the one EGA I §10.7 examples
take — an **open cover**:

* `J := ULift (Fin 3)`, chart algebras `A i := A{1/f_i}` — which genuinely differ from one
  another;
* overlap elements `g i j := ` the image of `f_i · f_j` in `A{1/f_i}`, cutting out
  `D(f_j) ∩ D(f_i)` inside the chart `Spf A{1/f_i}`.

The charts and their overlap identifications are in `FormalSchemes.ThreeChartCoverCharts`, the
transitions and their laws in `FormalSchemes.ThreeChartCoverTransitions`; this file only feeds
them to the smart constructor `AffineChartedFibreDatumX.ofAlgebraData` and records that the six
geometric triple-overlap fields are non-vacuous.

The glued `X` is the open subscheme `D(f₀) ∪ D(f₁) ∪ D(f₂)` of `Spf A`, hence separated — the
first non-Tate concrete instance of `BothChartedFibreDatumXY.IsSeparated`
(`FormalSchemes.GeneralSeparated`). That separatedness is `ThreeChartCover.datumX_isSeparated`
(`FormalSchemes.ThreeChartCoverSeparated`), stated of the formal scheme as
`datumX_isSeparatedOverSpf` (`FormalSchemes.ThreeChartCoverSeparatedScheme`) and chart-free as
`coverSubscheme_isSeparatedOverSpf` (`FormalSchemes.ThreeChartCoverOpenSubscheme`).

Note that `A` itself is **not** required to be an adic ring: only the chart algebras `A{1/f_i}`
occur as charts, and a completed localization is adic for free.

## Main definitions and results

* `AlgebraicGeometry.ThreeChartCover.datumX`: the `AffineChartedFibreDatumX`, with the glued
  objects `gluedX` and `fibreProductX`.
* `AlgebraicGeometry.ThreeChartCover.datumX_t'_eq`, `datumX_xt'_eq`,
  `datumX_xt'_zero_one_two`: the non-vacuity statements.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7, §10.15.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
open CompletedTensorAwayInterchange

universe u

namespace AlgebraicGeometry

namespace ThreeChartCover

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {A : Type u} [CommRing A] [Algebra R A]
variable (f : ULift.{u} (Fin 3) → A)

/-! ### The datum -/

section Datum

variable (B : Type u) [CommRing B] [Algebra R B]

/-- **The three-chart open-cover datum.** `Spf A` presented by the three basic opens `D(f_i)`,
with chart algebras `A{1/f_i}` and overlaps `D(g_ij) = D(f_i) ∩ D(f_j)`, over the affine base
change `Spf B`. All six geometric triple-overlap fields are derived from `tau` / `sigma` by
`AffineChartedFibreDatumX.ofAlgebraData` and are non-vacuous (see `datumX_xt'_eq`). -/
def datumX (hI : I.FG) : AffineChartedFibreDatumX R I hI B :=
  AffineChartedFibreDatumX.ofAlgebraData hI
    (A := chartAlgebra I f)
    (g := overlapElt I f)
    (topology := fun _ => inferInstance)
    (isAdic := fun i => chartIsAdicRing I f hI i)
    (τ := fun i j _ => tau I f hI i j)
    (τ_symm := fun i j _ => tau_symm I f hI i j)
    (σ := fun i j k _ _ _ => sigma I f hI i j k)
    (hστ := fun i j k _ _ _ => sigma_tau I f hI i j k)
    (hσc := fun i j k _ _ _ => sigma_cocycle I f hI i j k)

/-- **The glued formal scheme** `X = D(f₀) ∪ D(f₁) ∪ D(f₂) ⊆ Spf A`. Unlike the glued object of
`FormalSchemes.ThreeChartDatum`, this one is an *open subscheme of an affine formal scheme*. -/
def gluedX (hI : I.FG) : FormalScheme.{u} :=
  (datumX I f B hI).xGlued

/-- **The fibre product** `X ×_{Spf R} Spf B`. -/
def fibreProductX (hI : I.FG) : FormalScheme.{u} :=
  (datumX I f B hI).fibreProduct

end Datum

/-! ### Non-vacuity of the geometric fields -/

section Vacuity

variable (B : Type u) [CommRing B] [Algebra R B]

/-- **Non-vacuity of the fibre-product triple.** At a pairwise distinct triple the geometric
transition `t'` is the derived transition built from `sigma`, not `False.elim`. -/
theorem datumX_t'_eq (hI : I.FG) (i j k : ULift.{u} (Fin 3))
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (datumX I f B hI).t' i j k hij hik hjk =
      AffineChartedFibreDatum.algDataT' (B := B) hI (chartAlgebra I f) (overlapElt I f)
        (fun i j k _ _ _ => sigma I f hI i j k) i j k hij hik hjk :=
  rfl

/-- **Non-vacuity of the `X`-side triple.** -/
theorem datumX_xt'_eq (hI : I.FG) (i j k : ULift.{u} (Fin 3))
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (datumX I f B hI).xt' i j k hij hik hjk =
      AffineChartedFibreDatumX.xAlgDataT' hI (chartAlgebra I f) (overlapElt I f)
        (fun i j k _ _ _ => sigma I f hI i j k) i j k hij hik hjk :=
  rfl

/-- **Non-vacuity, concretely**, at the triple `0, 1, 2`. -/
theorem datumX_xt'_zero_one_two (hI : I.FG) :
    (datumX I f B hI).xt' ⟨0⟩ ⟨1⟩ ⟨2⟩ (ThreeChart.up_ne_up (by decide))
        (ThreeChart.up_ne_up (by decide)) (ThreeChart.up_ne_up (by decide)) =
      AffineChartedFibreDatumX.xAlgDataT' hI (chartAlgebra I f) (overlapElt I f)
        (fun i j k _ _ _ => sigma I f hI i j k) ⟨0⟩ ⟨1⟩ ⟨2⟩
        (ThreeChart.up_ne_up (by decide)) (ThreeChart.up_ne_up (by decide))
        (ThreeChart.up_ne_up (by decide)) :=
  rfl

end Vacuity

end ThreeChartCover

end AlgebraicGeometry

end
