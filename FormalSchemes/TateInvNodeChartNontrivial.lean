import FormalSchemes.SpfSectionsNontrivial
import FormalSchemes.TateInvNodeChartPrincipalRegularBase

set_option linter.style.header false

/-!
# The node chart's ring is not the zero ring

`FormalSchemes.TateInvNodeChartPrincipalRegularBase` proves

```
IsAdicComplete (tateInvNodeChartAwayIdeal …) (tateInvNodeChartAwaySubring …)
```

at `R = ℤ⟦X⟧`, `I = (X)`, `q = X`, and `FormalSchemes.TateInvNodeChartAmbient` proves the
companion Hausdorff statement. **Both are vacuously true when the ring they speak about is `0`**,
and no statement on this tree says it is not. This file says it.

`AlgebraicGeometry.nontrivial_tateInvNodeChartAwaySubring`: for `I ≠ ⊤` the node chart ring is a
nonzero ring, and `AlgebraicGeometry.nontrivial_tateInvNodeChartAwaySubring_powerSeriesInt` is
that at the universal Tate base, where
`AlgebraicGeometry.isAdicComplete_tateInvNodeChartAwayIdeal_powerSeriesInt` and
`AlgebraicGeometry.fg_tateInvNodeChartAwayIdeal_powerSeriesInt` also hold. Those two are therefore
statements about a nonzero ring.

## The argument, which is short because the tree already has both halves

The chart ring is a `Subring` — of `Γ(Spf A, tateInvPatchSaturateOpens hq hI hS)` in the
`AlgebraicGeometry.tateInvChartAnnulusSubring` spelling, and of `A{1/(x + y − 1)}` in the
`AlgebraicGeometry.tateInvNodeChartAwaySubring` one — so its nontriviality **is** the ambient
ring's, and the two ambients are identified by `AlgebraicGeometry.tateInvNodeChartAmbientEquiv`.
For the first ambient, `FormalSpectrum.nontrivial_sections_of_mem`
(`FormalSchemes.SpfSectionsNontrivial`) reduces the question to exhibiting a point of the open, and
`AlgebraicGeometry.tateInvNodeChartLocus_nonempty` — which needs exactly `I ≠ ⊤` — is that point,
transported to the saturated open by
`AlgebraicGeometry.tateInvPatchSaturateOpens_tateInvNodeChartLocus`, the record that the node
chart's domain is its own saturation.

So `I ≠ ⊤` is the whole hypothesis: it is what makes `Spf A` nonempty at all, by
`annulus_formalSpectrum_nonempty` — **root** namespace, like the rest of the `annulus*` family.
No hypothesis on `q` beyond `q ∈ I`, and nothing about regularity, enters.

## Main results

* `AlgebraicGeometry.nontrivial_tateInvChartAnnulusSubring` and
  `AlgebraicGeometry.nontrivial_tateInvChartAnnulusSubring_of_nonempty`: for an **arbitrary** open
  `S` of the model patch, the chart ring of `FormalSchemes.TateInvChartAnnulusRing` is nonzero as
  soon as the saturated open `tateInvPatchSaturateOpens hq hI hS` has a point. This is the general
  form; the rest of the file is the node chart's instance of it.
* `AlgebraicGeometry.nontrivial_tateInvNodeChartSubring`: the node chart ring, in the
  presheaf-section spelling, for `I ≠ ⊤`.
* `AlgebraicGeometry.nontrivial_tateInvNodeChartAmbient`: the ambient `A{1/(x + y − 1)}` itself.
* **`AlgebraicGeometry.nontrivial_tateInvNodeChartAwaySubring`**: the node chart ring inside
  `A{1/(x + y − 1)}`, which is the spelling the completeness and finite-generation results use.
* `AlgebraicGeometry.nontrivial_tateInvNodeChartAwaySubring_powerSeriesInt`: that at
  `R = ℤ⟦X⟧`, `I = Ideal.span {X}`, `q = X`, with `I ≠ ⊤` supplied by
  `PowerSeries.span_X_isPrime`.

## What is *not* proved here

**Not issue 1223's goal 3.** That asks for an element of the chart ring *outside the image of*
`Γ(Spf R, ·)`; nothing below exhibits one, and `0` and `1` are both in that image. This file is
1223's stated fallback ("if that is out of reach, say so and instead show the ring is nonzero for
`I ≠ ⊤`") and nothing more. At `S = Set.univ` there is no such element at all
(`AlgebraicGeometry.exists_algebraMap_eq_of_mem_tateInvChartAnnulusSubring_univ`), which is a
statement about `⊤` and not about the node chart's `S`.

Nothing here is about the *size* of the chart ring in the other direction either: that it is
strictly smaller than the ambient sections at `S = Set.univ` is
`AlgebraicGeometry.tateInvChartAnnulusSubring_univ_ne_top`
(`FormalSchemes.TateInvGlobalProperness`), and this file neither uses nor extends it.

No converse: `I = ⊤` is not shown to make the ring `0`. It makes `Spf A` empty, so the argument
below simply stops.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, 10.1.6.
* [Deligne–Rapoport, *Les schémas de modules de courbes elliptiques*], II.1.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum TopologicalSpace
open Opposite TopCat.Presheaf

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {I : Ideal R} {q : R}
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] {hq : q ∈ I} {hI : I.FG}
variable {S : Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))}

/-! ### The general form, at an arbitrary open of the model patch -/

/-- **The chart ring at an arbitrary `S` is nonzero once the saturated open has a point.** It is a
`Subring` of the sections over that open, and `FormalSpectrum.nontrivial_sections_of_mem` makes
those sections nonzero. -/
theorem nontrivial_tateInvChartAnnulusSubring (hS : IsOpen S)
    {x : FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)}
    (hx : x ∈ tateInvPatchSaturateOpens hq hI hS) :
    Nontrivial (tateInvChartAnnulusSubring (hq := hq) (hI := hI) hS) :=
  haveI := FormalSpectrum.nontrivial_sections_of_mem (I := annulusIdealOfDefinition R I q) hx
  inferInstance

/-- **The same with the hypothesis as a `Set.Nonempty`**, which is the shape the tree's
nonemptiness lemmas produce. -/
theorem nontrivial_tateInvChartAnnulusSubring_of_nonempty (hS : IsOpen S)
    (hne : ((tateInvPatchSaturateOpens hq hI hS :
      Opens (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))) :
        Set (FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q))).Nonempty) :
    Nontrivial (tateInvChartAnnulusSubring (hq := hq) (hI := hI) hS) :=
  nontrivial_tateInvChartAnnulusSubring hS hne.choose_spec

/-! ### The node chart -/

variable (R I q)

/-- **The node chart ring is nonzero**, in the presheaf-section spelling. The point comes from
`AlgebraicGeometry.tateInvNodeChartLocus_nonempty`, and
`AlgebraicGeometry.tateInvPatchSaturateOpens_tateInvNodeChartLocus` says the saturated open is the
node chart locus itself, so the point lands where it is needed with no further work. -/
theorem nontrivial_tateInvNodeChartSubring (hq : q ∈ I) (hI : I.FG) (hItop : I ≠ ⊤) :
    Nontrivial (tateInvNodeChartSubring R I q hq hI) := by
  obtain ⟨x, hx⟩ := tateInvNodeChartLocus_nonempty R I q hq hI hItop
  refine nontrivial_tateInvChartAnnulusSubring (hq := hq) (hI := hI) _ (x := x) ?_
  rw [tateInvPatchSaturateOpens_tateInvNodeChartLocus R I q hq hI]
  exact hx

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The node chart's ambient ring `A{1/(x + y − 1)}` is nonzero.** The sections over the node
chart locus are nonzero for the reason above, and
`AlgebraicGeometry.tateInvNodeChartAmbientEquiv` carries that across; a ring homomorphism into a
nontrivial ring has nontrivial domain, applied to the inverse equivalence. -/
theorem nontrivial_tateInvNodeChartAmbient (hq : q ∈ I) (hI : I.FG) (hItop : I ≠ ⊤) :
    Nontrivial
      (awayCompletion (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)) := by
  obtain ⟨x, hx⟩ := tateInvNodeChartLocus_nonempty R I q hq hI hItop
  haveI : Nontrivial ((FormalSpectrum.locallyRingedSpaceObj
      (annulusIdealOfDefinition R I q)).presheaf.obj
        (op (tateInvPatchSaturateOpens hq hI (isOpen_tateInvNodeChartLocus R I q)))) := by
    refine FormalSpectrum.nontrivial_sections_of_mem _ (x := x) ?_
    rw [tateInvPatchSaturateOpens_tateInvNodeChartLocus R I q hq hI]
    exact hx
  exact (tateInvNodeChartAmbientEquiv R I q hq hI).symm.toRingHom.domain_nontrivial

/-- **The node chart ring is nonzero**, in the `A{1/(x + y − 1)}` spelling — the one the
completeness, Hausdorff and finite-generation results are stated in. It is a `Subring` of the
ambient ring, so this is the previous theorem. -/
theorem nontrivial_tateInvNodeChartAwaySubring (hq : q ∈ I) (hI : I.FG) (hItop : I ≠ ⊤) :
    Nontrivial (tateInvNodeChartAwaySubring R I q hq hI) :=
  haveI := nontrivial_tateInvNodeChartAmbient R I q hq hI hItop
  inferInstance

/-! ### The universal Tate base -/

section Witness

/-- **The node chart ring is nonzero at `R = ℤ⟦X⟧`, `I = (X)`, `q = X`**, the base at which
`AlgebraicGeometry.isAdicComplete_tateInvNodeChartAwayIdeal_powerSeriesInt` and
`AlgebraicGeometry.fg_tateInvNodeChartAwayIdeal_powerSeriesInt` hold. Those two are therefore
statements about a nonzero ring: `IsAdicComplete` and `Ideal.FG` are both satisfied by the zero
ring for reasons with nothing to do with the node chart.

`I ≠ ⊤` is `PowerSeries.span_X_isPrime`'s `Ideal.IsPrime.ne_top`; the `X`-adic topology is supplied
by the `letI`, exactly as in the two results cited above. -/
theorem nontrivial_tateInvNodeChartAwaySubring_powerSeriesInt :
    letI : TopologicalSpace (PowerSeries ℤ) :=
      (Ideal.span {(PowerSeries.X : PowerSeries ℤ)}).adicTopology
    haveI : IsAdicRing (Ideal.span {(PowerSeries.X : PowerSeries ℤ)}) := ⟨rfl⟩
    Nontrivial (tateInvNodeChartAwaySubring (PowerSeries ℤ)
      (Ideal.span {(PowerSeries.X : PowerSeries ℤ)}) PowerSeries.X
      (Ideal.mem_span_singleton_self _) (Submodule.fg_span_singleton _)) :=
  letI : TopologicalSpace (PowerSeries ℤ) :=
    (Ideal.span {(PowerSeries.X : PowerSeries ℤ)}).adicTopology
  haveI : IsAdicRing (Ideal.span {(PowerSeries.X : PowerSeries ℤ)}) := ⟨rfl⟩
  nontrivial_tateInvNodeChartAwaySubring _ _ _ (Ideal.mem_span_singleton_self _)
    (Submodule.fg_span_singleton _) (PowerSeries.span_X_isPrime (R := ℤ)).ne_top

end Witness

end AlgebraicGeometry
