import FormalSchemes.ThreeChartCoverTransitions

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The basic-open cover datum: `Spf A` presented by a family of basic opens

Issue 594 (`FormalSchemes.ThreeChartDatum`) gave the first `AffineChartedFibreDatumX` whose
geometric triple-overlap fields are exercised, but in the shape "one copy of `Spf A` per index,
glued along `D(f_i·f_j)`": every chart algebra there is literally `A`, and the glued object is a
genuinely non-separated formal scheme. This file assembles the other shape, the one EGA I §10.7
examples take — an **open cover**:

* an index type `J` and a family `f : J → A`, chart algebras `A i := A{1/f_i}` — which genuinely
  differ from one another;
* overlap elements `g i j := ` the image of `f_i · f_j` in `A{1/f_i}`, cutting out
  `D(f_j) ∩ D(f_i)` inside the chart `Spf A{1/f_i}`.

The charts and their overlap identifications are in `FormalSchemes.ThreeChartCoverCharts`, the
transitions and their laws in `FormalSchemes.ThreeChartCoverTransitions`; this file only feeds
them to the smart constructor `AffineChartedFibreDatumX.ofAlgebraData` and records that the six
geometric triple-overlap fields are non-vacuous at an index type that has a pairwise distinct
triple.

The glued `X` is separated over `Spf R` — the first non-Tate concrete instance of
`BothChartedFibreDatumXY.IsSeparated` (`FormalSchemes.GeneralSeparated`). That is
`ThreeChartCover.datumX_isSeparated` (`FormalSchemes.ThreeChartCoverSeparated`), stated of the
formal scheme as `ThreeChartCover.datumX_isSeparatedOverSpf`
(`FormalSchemes.ThreeChartCoverSeparatedScheme`), and it holds at every index type. It is proved
from the datum's own chart codiagonals and **not** from any identification of `X` with a subscheme
of `Spf A`; that identification is a separate theorem and it is currently available only at three
indices, as `ThreeChartCover.isOpenImmersion_gluedXToBase` together with
`ThreeChartCover.range_gluedXToBase_base` (`FormalSchemes.ThreeChartCoverOpenImmersion`), whose
chart-free restatement is `ThreeChartCover.coverSubscheme_isSeparatedOverSpf`
(`FormalSchemes.ThreeChartCoverOpenSubscheme`). See "What is still at three indices" below.

Note that `A` itself is **not** required to be an adic ring: only the chart algebras `A{1/f_i}`
occur as charts, and a completed localization is adic for free.

## The index type, and the name

`J` is an arbitrary `Type u` here and in everything this file sits on. That was not always so: the
datum, its charts and its transitions were written at `J := ULift (Fin 3)` and lifted afterwards,
by replacing the binder and nothing else — no proof, no statement and no consumer changed. The
lift was taken because an arbitrary open of `Spf A` is a union of basic opens with no bound on how
many, and `FormalScheme.IsSeparatedOverSpf` is existential over a presentation, so a separatedness
statement about such an open cannot be reached from a datum on a fixed finite index type. The
three gaps named under "What is *not* proved here" in `FormalSchemes.GeneralSeparatedHom` all pass
through that statement.

**The namespace is still named after three charts, and that is now a misnomer.** It is left standing
deliberately rather than overlooked: the name is spelled out in modules all over this library, the
geometry layer below is still written at three indices, and renaming a half-lifted chain would
mean renaming it twice. The rename is tracked as its own row on the board, to be taken once the
geometry layer is lifted.

## What is still at three indices

`FormalSchemes.ThreeChartCoverToBase`, `FormalSchemes.ThreeChartCoverOverBase`,
`FormalSchemes.ThreeChartCoverTopFiniteType`, `FormalSchemes.ThreeChartCoverOpenImmersion` and
`FormalSchemes.ThreeChartCoverOpenSubscheme` — everything that maps the glued object back to
`Spf A` — are unchanged. Their
lift is not a binder change: `ThreeChartCover.range_gluedXToBase_base_sup`,
`ThreeChartCover.isIso_gluedXToBase` and `ThreeChartCover.gluedXIsoSpf` state the covering
hypothesis as a three-fold `⊔` of basic opens, whose general form is an indexed supremum, and
moving to it changes those signatures and their call sites.

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
variable {J : Type u} (f : J → A)

/-! ### The datum -/

section Datum

variable (B : Type u) [CommRing B] [Algebra R B]

/-- **The basic-open cover datum.** `Spf A` presented by the basic opens `D(f_i)`, `i : J`,
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

/-- **The glued formal scheme** `X = ⋃ D(f_i) ⊆ Spf A`. Unlike the glued object of
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
theorem datumX_t'_eq (hI : I.FG) (i j k : J)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (datumX I f B hI).t' i j k hij hik hjk =
      AffineChartedFibreDatum.algDataT' (B := B) hI (chartAlgebra I f) (overlapElt I f)
        (fun i j k _ _ _ => sigma I f hI i j k) i j k hij hik hjk :=
  rfl

/-- **Non-vacuity of the `X`-side triple.** -/
theorem datumX_xt'_eq (hI : I.FG) (i j k : J)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (datumX I f B hI).xt' i j k hij hik hjk =
      AffineChartedFibreDatumX.xAlgDataT' hI (chartAlgebra I f) (overlapElt I f)
        (fun i j k _ _ _ => sigma I f hI i j k) i j k hij hik hjk :=
  rfl

/-- **Non-vacuity, concretely**, at the triple `0, 1, 2` of `ULift (Fin 3)` — the one statement
here that is about a particular index type, and the reason this file's own name says three. -/
theorem datumX_xt'_zero_one_two (f : ULift.{u} (Fin 3) → A) (hI : I.FG) :
    (datumX I f B hI).xt' ⟨0⟩ ⟨1⟩ ⟨2⟩ (ULift.up_injective.ne (by decide))
        (ULift.up_injective.ne (by decide)) (ULift.up_injective.ne (by decide)) =
      AffineChartedFibreDatumX.xAlgDataT' hI (chartAlgebra I f) (overlapElt I f)
        (fun i j k _ _ _ => sigma I f hI i j k) ⟨0⟩ ⟨1⟩ ⟨2⟩
        (ULift.up_injective.ne (by decide)) (ULift.up_injective.ne (by decide))
        (ULift.up_injective.ne (by decide)) :=
  rfl

end Vacuity

end ThreeChartCover

end AlgebraicGeometry

end
