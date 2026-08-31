import FormalSchemes.SpfRingEquivIso
import FormalSchemes.TateInvNodeChartQuotientOpen
import FormalSchemes.TateInvNodeChartSpfNonempty

set_option linter.style.header false

/-!
# `hnode`'s residue, moved onto the quotient's own sections

`AlgebraicGeometry.exists_formalScheme_of_exists_openImmersion_spf_of_isLeftRegular_base`
(`FormalSchemes.TateInvNodeChartSpf`) reduced `hnode` — hence issue 69's headline question for the
period-`q` quotient — to a single open immersion out of `Spf` of one named ring. That ring is
`AlgebraicGeometry.tateInvNodeChartAwaySubring`, a subring of `A{1/(x + y − 1)}`, and it is *not*
the spelling a chart naturally comes in: the source of a chart of `T_inv/⟨σ⟩` over an open `V` is
`Spf` of `Γ (T_inv/⟨σ⟩, V)`.

`FormalSchemes.TateInvNodeChartQuotientOpen` supplied the missing pieces on the ring side — a
named open `AlgebraicGeometry.tateInvNodeChartQuotientOpens`, the identification
`AlgebraicGeometry.tateInvNodeChartQuotientRingEquiv` of its sections with the node chart ring,
and `AlgebraicGeometry.tateInvNodeChartQuotientIdeal` with its `IsAdicRing` structure — but
stopped at the ring: nothing carried the identification across `Spf`. This file does that, and
restates the reduction on the other side of it.

## What is here

* `AlgebraicGeometry.LocallyRingedSpace.exists_isOpenImmersion_of_iso`: an open immersion whose
  range contains a prescribed set transports along an isomorphism of its source. General.
* `AlgebraicGeometry.tateInvNodeChartQuotientIdeal_le_comap` and
  `AlgebraicGeometry.tateInvNodeChartAwayIdeal_le_comap_symm`: the two ideals correspond under
  `AlgebraicGeometry.tateInvNodeChartQuotientRingEquiv`.
* `AlgebraicGeometry.tateInvNodeChartQuotientSpfIso`: hence
  `Spf (Γ (T_inv/⟨σ⟩, tateInvNodeChartQuotientOpens …)) ≅ Spf (tateInvNodeChartAwaySubring …)`,
  by `FormalSpectrum.locallyRingedSpaceMapIso` (`FormalSchemes.SpfRingEquivIso`).
* `AlgebraicGeometry.ne_top_tateInvNodeChartQuotientIdeal` and
  `AlgebraicGeometry.nonempty_formalSpectrum_tateInvNodeChartQuotientIdeal`, with
  `AlgebraicGeometry.nonempty_formalSpectrum_tateInvNodeChartQuotientIdeal_powerSeriesInt` at
  `R = ℤ⟦X⟧`, `I = (X)`, `q = X`: the source of the required morphism has a point, in the
  quotient's own spelling. This is the companion of
  `AlgebraicGeometry.nonempty_formalSpectrum_tateInvNodeChartAwayIdeal`.
* the reduction with its hypothesis moved onto `Spf` of `Γ (T_inv/⟨σ⟩, ·)`, namely
  `AlgebraicGeometry.exists_formalScheme_of_openImmersion_spf_quotientIdeal_of_isLeftRegular_base`.
  (Its `TateInvNodeChartSpf` sibling is
  `AlgebraicGeometry.exists_formalScheme_of_exists_openImmersion_spf_of_isLeftRegular_base`.)

## What is *not* proved

**`hnode` is still undecided, and this file does not attempt it.** The residue is unchanged in
substance — one morphism — and only its spelling has moved. #452's survey stands and was not
re-walked: `glueHomOfGlobalSectionsHom` needs a `FormalScheme` source and points *into* a formal
spectrum, `locallyRingedSpaceMap` has a formal spectrum for its target, so nothing on this tree
produces a morphism out of a formal spectrum into a general locally ringed space and it will have
to be glued by hand.

Nothing here says `tateInvNodeChartQuotientOpens` is an affine formal chart, and `ht`/`hreg` are
still inherited from the principal-base results and still not shown necessary.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
* [Deligne–Rapoport, *Les schémas de modules de courbes elliptiques*], II.1 — the Néron 1-gon.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum TopologicalSpace
open Opposite

universe u

namespace AlgebraicGeometry

namespace LocallyRingedSpace

/-- **An open immersion whose range contains a prescribed set transports along an isomorphism of
its source.** If `T` sits inside the range of an open immersion out of `X` and `e : X ≅ Y`, then
`e.inv ≫ f` is an open immersion out of `Y` with the same range. General; the tree needs it
whenever a chart's source is available in two presentations of the same ring. -/
theorem exists_isOpenImmersion_of_iso {X Y Q : LocallyRingedSpace.{u}} (e : X ≅ Y) {T : Set Q}
    (hex : ∃ f : X ⟶ Q, LocallyRingedSpace.IsOpenImmersion f ∧ T ⊆ Set.range f.base) :
    ∃ f : Y ⟶ Q, LocallyRingedSpace.IsOpenImmersion f ∧ T ⊆ Set.range f.base := by
  obtain ⟨f, hf, hrange⟩ := hex
  haveI := hf
  refine ⟨e.inv ≫ f, inferInstance, hrange.trans ?_⟩
  rintro _ ⟨x, rfl⟩
  exact ⟨e.hom.base x, by simp⟩

end LocallyRingedSpace

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)

/-! ### The two ideals correspond under the identification of the two rings -/

/-- **The quotient's candidate ideal of definition lands inside the subring's**, along
`AlgebraicGeometry.tateInvNodeChartQuotientRingEquiv`. It is in fact carried onto it; only this
inclusion and the one below are needed, and each is one `simp` after
`Ideal.map_le_iff_le_comap`. -/
theorem tateInvNodeChartQuotientIdeal_le_comap :
    tateInvNodeChartQuotientIdeal R I q hq hI ≤
      (tateInvNodeChartAwayIdeal R I q hq hI).comap
        (tateInvNodeChartQuotientRingEquiv R I q hq hI :
          _ →+* tateInvNodeChartAwaySubring R I q hq hI) := by
  rw [tateInvNodeChartQuotientIdeal, Ideal.map_le_iff_le_comap]
  intro x hx
  simp only [Ideal.mem_comap, RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  exact hx

/-- **And the subring's lands inside the quotient's**, along the inverse. This is
`Ideal.le_comap_map` at the very map `AlgebraicGeometry.tateInvNodeChartQuotientIdeal` is defined
by. -/
theorem tateInvNodeChartAwayIdeal_le_comap_symm :
    tateInvNodeChartAwayIdeal R I q hq hI ≤
      (tateInvNodeChartQuotientIdeal R I q hq hI).comap
        ((tateInvNodeChartQuotientRingEquiv R I q hq hI).symm :
          tateInvNodeChartAwaySubring R I q hq hI →+* _) := by
  rw [tateInvNodeChartQuotientIdeal]
  exact Ideal.le_comap_map

/-! ### The two formal spectra are isomorphic -/

/-- **`Spf` of the quotient's sections over the node chart's open is `Spf` of the node chart
ring.** `FormalSpectrum.locallyRingedSpaceMapIso` at
`AlgebraicGeometry.tateInvNodeChartQuotientRingEquiv`, whose two continuity hypotheses are the two
inclusions above.

The left-hand side is the one a chart has to come out of — its ring is literally
`Γ (T_inv/⟨σ⟩, tateInvNodeChartQuotientOpens …)` — and the right-hand side is the one every
statement on this cluster is currently phrased at. -/
def tateInvNodeChartQuotientSpfIso
    [TopologicalSpace ((actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj
      (op (tateInvNodeChartQuotientOpens R I q hq hI)))]
    [IsAdicRing (tateInvNodeChartQuotientIdeal R I q hq hI)]
    [TopologicalSpace (tateInvNodeChartAwaySubring R I q hq hI)]
    [IsAdicRing (tateInvNodeChartAwayIdeal R I q hq hI)] :
    FormalSpectrum.locallyRingedSpaceObj (tateInvNodeChartQuotientIdeal R I q hq hI) ≅
      FormalSpectrum.locallyRingedSpaceObj (tateInvNodeChartAwayIdeal R I q hq hI) :=
  FormalSpectrum.locallyRingedSpaceMapIso _ _ (tateInvNodeChartQuotientRingEquiv R I q hq hI)
    (tateInvNodeChartQuotientIdeal_le_comap R I q hq hI)
    (tateInvNodeChartAwayIdeal_le_comap_symm R I q hq hI)

/-! ### The source of the required chart is not empty -/

/-- **The quotient's candidate ideal of definition is proper**, for `I ≠ ⊤`. It sits inside the
node chart ring's along `AlgebraicGeometry.tateInvNodeChartQuotientRingEquiv`, and `1` goes to
`1`, so `AlgebraicGeometry.ne_top_tateInvNodeChartAwayIdeal`
(`FormalSchemes.TateInvNodeChartSpfNonempty`) transfers. -/
theorem ne_top_tateInvNodeChartQuotientIdeal (hItop : I ≠ ⊤) :
    tateInvNodeChartQuotientIdeal R I q hq hI ≠ ⊤ := by
  intro htop
  refine ne_top_tateInvNodeChartAwayIdeal R I q hq hI hItop ?_
  rw [Ideal.eq_top_iff_one]
  have h1 : (1 : (actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj
      (op (tateInvNodeChartQuotientOpens R I q hq hI))) ∈
      tateInvNodeChartQuotientIdeal R I q hq hI := htop ▸ Submodule.mem_top
  simpa using tateInvNodeChartQuotientIdeal_le_comap R I q hq hI h1

/-- **So `Spf` of the quotient's sections over the node chart's open has a point**, for `I ≠ ⊤`.
This is the companion, in the quotient's own spelling, of
`AlgebraicGeometry.nonempty_formalSpectrum_tateInvNodeChartAwayIdeal`: the source of the morphism
the reduction below asks for is not empty, so that hypothesis is not refutable for a trivial
reason. -/
theorem nonempty_formalSpectrum_tateInvNodeChartQuotientIdeal (hItop : I ≠ ⊤) :
    Nonempty (FormalSpectrum (tateInvNodeChartQuotientIdeal R I q hq hI)) :=
  (FormalSpectrum.nonempty_iff_ne_top _).mpr
    (ne_top_tateInvNodeChartQuotientIdeal R I q hq hI hItop)

section Witness

/-- **At `R = ℤ⟦X⟧`, `I = (X)`, `q = X`, with no hypothesis at all.** `I ≠ ⊤` is
`PowerSeries.span_X_isPrime`'s `Ideal.IsPrime.ne_top`, as in
`AlgebraicGeometry.nonempty_formalSpectrum_tateInvNodeChartAwayIdeal_powerSeriesInt`. -/
theorem nonempty_formalSpectrum_tateInvNodeChartQuotientIdeal_powerSeriesInt :
    letI : TopologicalSpace (PowerSeries ℤ) :=
      (Ideal.span {(PowerSeries.X : PowerSeries ℤ)}).adicTopology
    haveI : IsAdicRing (Ideal.span {(PowerSeries.X : PowerSeries ℤ)}) := ⟨rfl⟩
    Nonempty (FormalSpectrum (tateInvNodeChartQuotientIdeal (PowerSeries ℤ)
      (Ideal.span {(PowerSeries.X : PowerSeries ℤ)}) PowerSeries.X
      (Ideal.mem_span_singleton_self _) (Submodule.fg_span_singleton _))) :=
  letI : TopologicalSpace (PowerSeries ℤ) :=
    (Ideal.span {(PowerSeries.X : PowerSeries ℤ)}).adicTopology
  haveI : IsAdicRing (Ideal.span {(PowerSeries.X : PowerSeries ℤ)}) := ⟨rfl⟩
  nonempty_formalSpectrum_tateInvNodeChartQuotientIdeal _ _ _
    (Ideal.mem_span_singleton_self _) (Submodule.fg_span_singleton _)
    (PowerSeries.span_X_isPrime (R := ℤ)).ne_top

end Witness
/-! ### The residue of `hnode`, at the quotient's own sections -/

/-- **`hnode`'s residue, restated at `Spf` of the quotient's own sections.** Over a principal base
ideal generated by a non-zero-divisor, `T_inv/⟨σ⟩` is a formal scheme as soon as there is an open
immersion into it out of `Spf` of `Γ (T_inv/⟨σ⟩, tateInvNodeChartQuotientOpens …)` — taken with
the adic topology of `AlgebraicGeometry.tateInvNodeChartQuotientIdeal`, at which
`AlgebraicGeometry.isAdicRing_tateInvNodeChartQuotientIdeal_of_isLeftRegular_base` supplies the
`IsAdicRing` instance — whose range contains
`Set.range (tateInvNodeChartAmbientHom …).base`.

This is
`AlgebraicGeometry.exists_formalScheme_of_exists_openImmersion_spf_of_isLeftRegular_base`
(`FormalSchemes.TateInvNodeChartSpf`) with its hypothesis moved across
`AlgebraicGeometry.tateInvNodeChartQuotientSpfIso`. What it buys is that the outstanding
hypothesis is no longer about a subring of `A{1/(x + y − 1)}` but about the section ring of the
quotient itself, over a named open of the quotient — which is where the source of a chart has to
live, and is the spelling in which the morphism will have to be built.

**It does not decide `hnode`.** Nothing here constructs the morphism, and
#452's survey stands: no construction on this tree produces a morphism *out of* a formal spectrum
into a general locally ringed space, so it will have to be glued by hand. -/
theorem exists_formalScheme_of_openImmersion_spf_quotientIdeal_of_isLeftRegular_base (t : R)
    (ht : I = Ideal.span {t}) (hreg : IsLeftRegular t)
    (hex :
      letI : TopologicalSpace ((actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj
          (op (tateInvNodeChartQuotientOpens R I q hq hI))) :=
        (tateInvNodeChartQuotientIdeal R I q hq hI).adicTopology
      haveI : IsAdicRing (tateInvNodeChartQuotientIdeal R I q hq hI) :=
        isAdicRing_tateInvNodeChartQuotientIdeal_of_isLeftRegular_base R I q hq hI t ht hreg
      ∃ f : FormalSpectrum.locallyRingedSpaceObj (tateInvNodeChartQuotientIdeal R I q hq hI) ⟶
          actionQuotient (tateInvPeriodAction R I q hq hI),
        LocallyRingedSpace.IsOpenImmersion f ∧
          Set.range (tateInvNodeChartAmbientHom R I q hq hI
              (π := actionQuotientπ (tateInvPeriodAction R I q hq hI))).base ⊆
            Set.range f.base) :
    ∃ X : FormalScheme.{u},
      X.toLocallyRingedSpace = actionQuotient (tateInvPeriodAction R I q hq hI) := by
  letI : TopologicalSpace ((actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj
      (op (tateInvNodeChartQuotientOpens R I q hq hI))) :=
    (tateInvNodeChartQuotientIdeal R I q hq hI).adicTopology
  haveI : IsAdicRing (tateInvNodeChartQuotientIdeal R I q hq hI) :=
    isAdicRing_tateInvNodeChartQuotientIdeal_of_isLeftRegular_base R I q hq hI t ht hreg
  letI : TopologicalSpace (tateInvNodeChartAwaySubring R I q hq hI) :=
    (tateInvNodeChartAwayIdeal R I q hq hI).adicTopology
  haveI : IsAdicRing (tateInvNodeChartAwayIdeal R I q hq hI) :=
    isAdicRing_tateInvNodeChartAwayIdeal_of_principal_of_isLeftRegular_base R I q hq hI t ht hreg
  exact exists_formalScheme_of_exists_openImmersion_spf_of_isLeftRegular_base R I q hq hI t ht hreg
    (isActionQuotient_actionQuotientπ _)
    (LocallyRingedSpace.exists_isOpenImmersion_of_iso
      (tateInvNodeChartQuotientSpfIso R I q hq hI) hex)

end AlgebraicGeometry
