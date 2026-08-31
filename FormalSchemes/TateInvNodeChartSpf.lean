import FormalSchemes.TateInvNodeChartPrincipalRegularBase

set_option linter.style.header false

/-!
# `Spf` of the node chart ring, and `hnode` as one open immersion

`FormalSchemes.TateInvNodeChartAmbient` cut the node chart's candidate ring out of
`A{1/(x + y − 1)}` as `AlgebraicGeometry.tateInvNodeChartAwaySubring`, with
`AlgebraicGeometry.tateInvNodeChartAwayIdeal` its candidate ideal of definition, and proved that
ideal Hausdorff. `FormalSchemes.TateInvNodeChartPrincipalRegularBase` proved it **complete** and
**finitely generated** over a base with `I = Ideal.span {t}` and `IsLeftRegular t`.

Those are the two halves of `IsAdicRing` other than the topology, and the topology is a choice.
This file makes it — the `tateInvNodeChartAwayIdeal`-adic one — and draws the consequence: over
such a base the chart ring **is an adic ring**, so `Spf` of it is an affine formal scheme and
`LocallyRingedSpace.HasAffineChartAt` can be fed with it.

## What is here

* **`AlgebraicGeometry.isAdicRing_tateInvNodeChartAwayIdeal_of_principal_of_isLeftRegular_base`**:
  with the `tateInvNodeChartAwayIdeal`-adic topology on the chart ring,
  `IsAdicRing (tateInvNodeChartAwayIdeal R I q hq hI)` — from
  `AlgebraicGeometry.isAdicComplete_tateInvNodeChartAwayIdeal_of_principal_of_isLeftRegular_base`
  and `isAdic := rfl`, which is what choosing the adic topology buys.
  `AlgebraicGeometry.isAdicRing_tateInvNodeChartAwayIdeal_powerSeriesInt` is that statement at
  `R = ℤ⟦X⟧`, `I = (X)`, `q = X`, with no hypothesis at all.
* **`AlgebraicGeometry.exists_formalScheme_of_exists_openImmersion_spf_of_isLeftRegular_base`**:
  over such a base, `T_inv/⟨σ⟩` is a formal scheme as soon as there is **one** open immersion out
  of `Spf` of the chart ring whose range contains the range of
  `AlgebraicGeometry.tateInvNodeChartAmbientHom`. The `IsAdicRing` instance the statement needs is
  supplied by the previous item rather than assumed.
* `AlgebraicGeometry.hasAffineChartAt_of_openImmersion_spf_tateInvNodeChart` and
  `AlgebraicGeometry.hasAffineChartAt_of_openImmersion_spf_tateInvNodeChart_of_range`: the two
  steps of that reduction, at an arbitrary topology and `IsAdicRing` instance on the chart ring.
  The first is an instantiation of the definition of
  `AlgebraicGeometry.LocallyRingedSpace.HasAffineChartAt` and nothing more; the content is that
  the ring it is instantiated at is now known to be adic.
  `AlgebraicGeometry.tateInvPeriodQuotientFormalSchemeOfSpfNodeChart` is the resulting
  `FormalScheme`, with `Q` as its underlying locally ringed space.
* **`AlgebraicGeometry.exists_isAdicComplete_sections_tateInvNodeChart_of_isLeftRegular_base`**:
  the same completeness and finite generation carried across
  `AlgebraicGeometry.exists_tateInvNodeChartAwayRingEquiv` to `Γ` of the **quotient** — there is an
  open `V` of `T_inv/⟨σ⟩` whose preimage is the node chart's domain and an ideal `K` of
  `Γ (T_inv/⟨σ⟩, V)` with `K.FG` and `IsAdicComplete K (Γ (T_inv/⟨σ⟩, V))`. `Ideal.FG` and
  `IsAdicComplete` move along a `RingEquiv` by `Ideal.fg_map_ringEquiv_symm` and
  `IsAdicComplete.map_ringEquiv_symm`, the two general lemmas at the top of this file; the second
  is Mathlib's `IsAdicComplete.congr_ringEquiv` with the equivalence turned around.

## What is *not* proved

**`hnode` is still undecided and nothing here is a chart.** What this file changes is the shape of
what is missing, not whether it is missing.

* **No morphism `Spf (chart ring) ⟶ T_inv/⟨σ⟩` is constructed**, and none is shown to exist. Every
  result above takes one as a hypothesis. Two routes that might look available are not:
  `AlgebraicGeometry.FormalScheme.OpenCover.glueHomOfGlobalSectionsHom`
  (`FormalSchemes.GlueHomToSpf`) builds a morphism whose **source** is a `FormalScheme` and whose
  **target** is a formal spectrum, so it points the wrong way and its source hypothesis is what is
  being sought; and `FormalSpectrum.locallyRingedSpaceMap` (`FormalSchemes.SpfMap`) has a formal
  spectrum for its target too.
* **Nothing here says the chart ring is nonzero.** `IsAdicComplete K S` and `IsAdicRing K` both
  hold for the zero ring, so every result above is as strong as
  `Nontrivial (tateInvNodeChartAwaySubring R I q hq hI)` and no stronger, and that is not proved on
  this tree at any base — it is issue 1223's goal 3. The same caveat applies to
  `exists_isAdicComplete_sections_tateInvNodeChart_of_isLeftRegular_base`, whose `K` lives in a
  section ring that is likewise not shown nontrivial.
* **`AlgebraicGeometry.tateInvNodeChartAmbientHom` is still not shown to be an open immersion**,
  and this file does not use it as one: it appears only inside `Set.range … ⊆ Set.range f.base`,
  as a way of naming the set a chart must cover, which is
  `AlgebraicGeometry.range_tateInvNodeChartAmbientHom`.
* Nothing here decides whether the hypothesis `IsLeftRegular t` or the principal base is needed;
  they are inherited from `FormalSchemes.TateInvNodeChartPrincipalRegularBase`.

Nothing here weakens `LocallyRingedSpace.IsProperlyDiscontinuousOn`,
`LocallyRingedSpace.IsFreeProperlyDiscontinuous` or
`LocallyRingedSpace.freeActionQuotientFormalScheme`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum TopologicalSpace
open Opposite TopCat.Presheaf

universe u

/-- **Finite generation moves backwards along a ring isomorphism.** `Ideal.FG.map` at
`(e.symm : B →+* A)`; stated separately because the coercion has to be the `RingHom` one for
`Ideal.FG.map` to apply without unfolding, and the version phrased at the `RingEquiv` itself
sends the elaborator into a `whnf` timeout at the section-ring types this file uses it on. -/
theorem Ideal.fg_map_ringEquiv_symm {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B)
    {J : Ideal B} (hfg : J.FG) : (J.map (e.symm : B →+* A)).FG :=
  hfg.map (e.symm : B →+* A)

/-- **Adic completeness moves backwards along a ring isomorphism**: if `B` is `J`-adically
complete and `e : A ≃+* B`, then `A` is complete for the ideal `J` is carried to. This is
Mathlib's `IsAdicComplete.congr_ringEquiv` at `e.symm`, restated at the `RingHom` coercion for the
reason given on `Ideal.fg_map_ringEquiv_symm`; the `rfl` bridges the two spellings of
`Ideal.map`. -/
theorem IsAdicComplete.map_ringEquiv_symm {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B)
    (J : Ideal B) (h : IsAdicComplete J B) : IsAdicComplete (J.map (e.symm : B →+* A)) A :=
  have hK : J.map (e.symm : B →+* A) = J.map e.symm := rfl
  hK ▸ (IsAdicComplete.congr_ringEquiv J e.symm).mpr h

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)

/-- **The node chart ring is an adic ring over a principal base ideal generated by a
non-zero-divisor** — the ring is `AlgebraicGeometry.tateInvNodeChartAwaySubring` and the ideal of
definition is `AlgebraicGeometry.tateInvNodeChartAwayIdeal`, carrying the topology that ideal
defines.

The two components come from elsewhere and nothing is re-proved here: `IsAdicComplete` is
`AlgebraicGeometry.isAdicComplete_tateInvNodeChartAwayIdeal_of_principal_of_isLeftRegular_base`
(`FormalSchemes.TateInvNodeChartPrincipalRegularBase`), and `isAdic` is `rfl` because the topology
supplied by the `letI` *is* `Ideal.adicTopology` of that ideal — the same one-line pattern as
`AdicCompletion.isAdicRing_map` (`FormalSchemes.RestrictedPowerSeries`).

What it buys is the object: `FormalSpectrum.locallyRingedSpaceObj` of this ideal is an affine
formal scheme, so it is a candidate for
`AlgebraicGeometry.LocallyRingedSpace.HasAffineChartAt`. It is **not** an instance, because the
topology is a choice this file makes and the hypotheses `ht` and `hreg` are not synthesizable.

`IsAdicComplete` holds for the zero ring, so this says nothing about the size of the chart ring;
see this file's module docstring. -/
theorem isAdicRing_tateInvNodeChartAwayIdeal_of_principal_of_isLeftRegular_base (t : R)
    (ht : I = Ideal.span {t}) (hreg : IsLeftRegular t) :
    letI : TopologicalSpace (tateInvNodeChartAwaySubring R I q hq hI) :=
      (tateInvNodeChartAwayIdeal R I q hq hI).adicTopology
    IsAdicRing (tateInvNodeChartAwayIdeal R I q hq hI) :=
  letI : TopologicalSpace (tateInvNodeChartAwaySubring R I q hq hI) :=
    (tateInvNodeChartAwayIdeal R I q hq hI).adicTopology
  haveI : IsAdicComplete (tateInvNodeChartAwayIdeal R I q hq hI)
      (tateInvNodeChartAwaySubring R I q hq hI) :=
    isAdicComplete_tateInvNodeChartAwayIdeal_of_principal_of_isLeftRegular_base R I q hq hI t ht
      hreg
  ⟨rfl⟩


section Quotient

variable {Q : LocallyRingedSpace.{u}}
variable {π : (tateChainInv R I q hq hI).toLocallyRingedSpace ⟶ Q}

/-- **One open immersion out of `Spf` of the node chart ring charts the whole candidate domain.**
Given any topology and `IsAdicRing` instance on the chart ring, an open immersion `f` from
`Spf (tateInvNodeChartAwayIdeal …)` into `Q` whose range contains
`π '' tateInvSaturate D(x + y − 1)` gives
`AlgebraicGeometry.LocallyRingedSpace.HasAffineChartAt Q z` at every `z` of that set.

This is an instantiation of the definition of `LocallyRingedSpace.HasAffineChartAt` — the same `f`
is handed back at every `z`, and the existential's ring, topology and `IsAdicRing` witness are the
ones in the binders. The reason to state it is the ring it is instantiated at: by
`AlgebraicGeometry.isAdicRing_tateInvNodeChartAwayIdeal_of_principal_of_isLeftRegular_base` that
`IsAdicRing` hypothesis is discharged over a principal base with a regular generator. -/
theorem hasAffineChartAt_of_openImmersion_spf_tateInvNodeChart
    [TopologicalSpace (tateInvNodeChartAwaySubring R I q hq hI)]
    [IsAdicRing (tateInvNodeChartAwayIdeal R I q hq hI)]
    (f : FormalSpectrum.locallyRingedSpaceObj (tateInvNodeChartAwayIdeal R I q hq hI) ⟶ Q)
    (hf : LocallyRingedSpace.IsOpenImmersion f)
    (hrange : ⇑π.base '' tateInvSaturate R I q hq hI (tateInvNodeChartLocus R I q) ⊆
      Set.range f.base) :
    ∀ z ∈ ⇑π.base '' tateInvSaturate R I q hq hI (tateInvNodeChartLocus R I q),
      LocallyRingedSpace.HasAffineChartAt Q z :=
  fun _ hz => ⟨_, _, _, _, ‹_›, f, hrange hz, hf⟩

/-- The previous theorem with the covering hypothesis phrased as containment of ranges,
`Set.range (tateInvNodeChartAmbientHom …).base ⊆ Set.range f.base`. The two are the same
hypothesis by `AlgebraicGeometry.range_tateInvNodeChartAmbientHom`, which computes the left-hand
range as `π '' tateInvSaturate D(x + y − 1)`; this form is the one a successor will meet, since
`tateInvNodeChartAmbientHom` is how that set is named on this tree. -/
theorem hasAffineChartAt_of_openImmersion_spf_tateInvNodeChart_of_range
    [TopologicalSpace (tateInvNodeChartAwaySubring R I q hq hI)]
    [IsAdicRing (tateInvNodeChartAwayIdeal R I q hq hI)]
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π)
    (f : FormalSpectrum.locallyRingedSpaceObj (tateInvNodeChartAwayIdeal R I q hq hI) ⟶ Q)
    (hf : LocallyRingedSpace.IsOpenImmersion f)
    (hrange : Set.range (tateInvNodeChartAmbientHom R I q hq hI (π := π)).base ⊆
      Set.range f.base) :
    ∀ z ∈ ⇑π.base '' tateInvSaturate R I q hq hI (tateInvNodeChartLocus R I q),
      LocallyRingedSpace.HasAffineChartAt Q z :=
  hasAffineChartAt_of_openImmersion_spf_tateInvNodeChart R I q hq hI f hf
    (by rwa [← range_tateInvNodeChartAmbientHom R I q hq hI h])

/-- **`T_inv/⟨σ⟩` as a formal scheme, out of one open immersion.**
`AlgebraicGeometry.tateInvPeriodQuotientFormalSchemeOfNodeChartLocus`
(`FormalSchemes.TateInvNodeChartDomain`) needs a chart at every point of
`π '' tateInvSaturate D(x + y − 1)`; the previous theorem supplies all of them from `f`. -/
def tateInvPeriodQuotientFormalSchemeOfSpfNodeChart
    [TopologicalSpace (tateInvNodeChartAwaySubring R I q hq hI)]
    [IsAdicRing (tateInvNodeChartAwayIdeal R I q hq hI)]
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π)
    (f : FormalSpectrum.locallyRingedSpaceObj (tateInvNodeChartAwayIdeal R I q hq hI) ⟶ Q)
    (hf : LocallyRingedSpace.IsOpenImmersion f)
    (hrange : Set.range (tateInvNodeChartAmbientHom R I q hq hI (π := π)).base ⊆
      Set.range f.base) :
    FormalScheme.{u} :=
  tateInvPeriodQuotientFormalSchemeOfNodeChartLocus R I q hq hI h
    (hasAffineChartAt_of_openImmersion_spf_tateInvNodeChart_of_range R I q hq hI h f hf hrange)

/-- The formal scheme produced has `Q` itself as its underlying locally ringed space. -/
@[simp]
theorem tateInvPeriodQuotientFormalSchemeOfSpfNodeChart_toLocallyRingedSpace
    [TopologicalSpace (tateInvNodeChartAwaySubring R I q hq hI)]
    [IsAdicRing (tateInvNodeChartAwayIdeal R I q hq hI)]
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π)
    (f : FormalSpectrum.locallyRingedSpaceObj (tateInvNodeChartAwayIdeal R I q hq hI) ⟶ Q)
    (hf : LocallyRingedSpace.IsOpenImmersion f)
    (hrange : Set.range (tateInvNodeChartAmbientHom R I q hq hI (π := π)).base ⊆
      Set.range f.base) :
    (tateInvPeriodQuotientFormalSchemeOfSpfNodeChart R I q hq hI h f hf
      hrange).toLocallyRingedSpace = Q := rfl

/-- **The residue of `hnode`, over a principal base ideal generated by a non-zero-divisor: one
open immersion.** If `I = Ideal.span {t}` with `IsLeftRegular t`, and there exists an open
immersion `f` from `Spf` of the node chart ring — taken with the adic topology of
`AlgebraicGeometry.tateInvNodeChartAwayIdeal`, at which
`isAdicRing_tateInvNodeChartAwayIdeal_of_principal_of_isLeftRegular_base` supplies the `IsAdicRing`
instance the statement needs — whose range contains
`Set.range (tateInvNodeChartAmbientHom …).base`, then `T_inv/⟨σ⟩` is a formal scheme.

Compared with `AlgebraicGeometry.tateInvPeriodQuotientFormalSchemeOfNodeChartLocus`, whose
hypothesis quantifies over the points of the candidate domain and lets the chart ring vary with
the point, this asks for a single morphism out of a single named ring. It is a stronger hypothesis
and a smaller one to state; whether it is satisfiable is exactly what is open. -/
theorem exists_formalScheme_of_exists_openImmersion_spf_of_isLeftRegular_base (t : R)
    (ht : I = Ideal.span {t}) (hreg : IsLeftRegular t)
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π)
    (hex :
      letI : TopologicalSpace (tateInvNodeChartAwaySubring R I q hq hI) :=
        (tateInvNodeChartAwayIdeal R I q hq hI).adicTopology
      haveI : IsAdicRing (tateInvNodeChartAwayIdeal R I q hq hI) :=
        isAdicRing_tateInvNodeChartAwayIdeal_of_principal_of_isLeftRegular_base R I q hq hI t ht
          hreg
      ∃ f : FormalSpectrum.locallyRingedSpaceObj (tateInvNodeChartAwayIdeal R I q hq hI) ⟶ Q,
        LocallyRingedSpace.IsOpenImmersion f ∧
          Set.range (tateInvNodeChartAmbientHom R I q hq hI (π := π)).base ⊆
            Set.range f.base) :
    ∃ X : FormalScheme.{u}, X.toLocallyRingedSpace = Q :=
  letI : TopologicalSpace (tateInvNodeChartAwaySubring R I q hq hI) :=
    (tateInvNodeChartAwayIdeal R I q hq hI).adicTopology
  haveI : IsAdicRing (tateInvNodeChartAwayIdeal R I q hq hI) :=
    isAdicRing_tateInvNodeChartAwayIdeal_of_principal_of_isLeftRegular_base R I q hq hI t ht hreg
  let ⟨f, hf, hrange⟩ := hex
  ⟨tateInvPeriodQuotientFormalSchemeOfSpfNodeChart R I q hq hI h f hf hrange, rfl⟩


end Quotient

section Sections

/-- **`Γ` of the quotient over the candidate node-chart domain carries a finitely generated
adically complete ideal**, over a principal base ideal generated by a non-zero-divisor. The open
`V` and the isomorphism onto `AlgebraicGeometry.tateInvNodeChartAwaySubring` are
`AlgebraicGeometry.exists_tateInvNodeChartAwayRingEquiv`'s; `K` is
`AlgebraicGeometry.tateInvNodeChartAwayIdeal` carried back along it, and the two transports are
`Ideal.fg_map_ringEquiv_symm` and `IsAdicComplete.map_ringEquiv_symm`.

This is the same content as the results it is built from, moved off the subring of
`A{1/(x + y − 1)}` and onto `T_inv/⟨σ⟩` itself. It does **not** say `V` is an affine formal
chart, and `IsAdicComplete` holds for the zero ring, so it does not say the section ring is
nonzero either. -/
theorem exists_isAdicComplete_sections_tateInvNodeChart_of_isLeftRegular_base (t : R)
    (ht : I = Ideal.span {t}) (hreg : IsLeftRegular t) :
    ∃ (V : Opens (actionQuotient (tateInvPeriodAction R I q hq hI)).toTopCat)
      (_ : (Opens.map (actionQuotientπ
        (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V =
          tateInvSaturateOpens hq hI (isOpen_tateInvNodeChartLocus R I q))
      (K : Ideal ((actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj (op V))),
      K.FG ∧ IsAdicComplete K
        ((actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj (op V)) := by
  obtain ⟨V, hV, ⟨e⟩⟩ := exists_tateInvNodeChartAwayRingEquiv R I q hq hI
  refine ⟨V, hV, _, Ideal.fg_map_ringEquiv_symm e
    (fg_tateInvNodeChartAwayIdeal_of_principal_of_isLeftRegular_base R I q hq hI t ht hreg),
    IsAdicComplete.map_ringEquiv_symm e _
      (isAdicComplete_tateInvNodeChartAwayIdeal_of_principal_of_isLeftRegular_base R I q hq hI t ht
        hreg)⟩

end Sections

section Witness

/-- **The node chart ring is an adic ring at `R = ℤ⟦X⟧`, `I = (X)`, `q = X`**, with no hypothesis
at all: the base generator `t = X` is a non-zero-divisor. This is
`isAdicRing_tateInvNodeChartAwayIdeal_of_principal_of_isLeftRegular_base` at the base of
`AlgebraicGeometry.isAdicComplete_tateInvNodeChartAwayIdeal_powerSeriesInt`, whose `letI` for the
`X`-adic topology on `ℤ⟦X⟧` it repeats. -/
theorem isAdicRing_tateInvNodeChartAwayIdeal_powerSeriesInt :
    letI : TopologicalSpace (PowerSeries ℤ) :=
      (Ideal.span {(PowerSeries.X : PowerSeries ℤ)}).adicTopology
    haveI : IsAdicRing (Ideal.span {(PowerSeries.X : PowerSeries ℤ)}) := ⟨rfl⟩
    letI : TopologicalSpace (tateInvNodeChartAwaySubring (PowerSeries ℤ)
        (Ideal.span {(PowerSeries.X : PowerSeries ℤ)}) PowerSeries.X
        (Ideal.mem_span_singleton_self _) (Submodule.fg_span_singleton _)) :=
      (tateInvNodeChartAwayIdeal (PowerSeries ℤ)
        (Ideal.span {(PowerSeries.X : PowerSeries ℤ)}) PowerSeries.X
        (Ideal.mem_span_singleton_self _) (Submodule.fg_span_singleton _)).adicTopology
    IsAdicRing (tateInvNodeChartAwayIdeal (PowerSeries ℤ)
      (Ideal.span {(PowerSeries.X : PowerSeries ℤ)}) PowerSeries.X
      (Ideal.mem_span_singleton_self _) (Submodule.fg_span_singleton _)) :=
  letI : TopologicalSpace (PowerSeries ℤ) :=
    (Ideal.span {(PowerSeries.X : PowerSeries ℤ)}).adicTopology
  haveI : IsAdicRing (Ideal.span {(PowerSeries.X : PowerSeries ℤ)}) := ⟨rfl⟩
  isAdicRing_tateInvNodeChartAwayIdeal_of_principal_of_isLeftRegular_base _ _ _
    (Ideal.mem_span_singleton_self _) (Submodule.fg_span_singleton _) PowerSeries.X rfl
    (IsRegular.of_ne_zero PowerSeries.X_ne_zero).left

end Witness

end AlgebraicGeometry
