import FormalSchemes.AdicOnOpenSections
import FormalSchemes.TateInvNodeChartDomain

set_option linter.style.header false

/-!
# The node chart's ambient ring is `A{1/(x + y − 1)}`

`FormalSchemes.TateInvNodeChartDomain` chose the node chart's domain on the model patch,
`S = D(x + y − 1) ⊆ Spf A` for `A = R{x, y}/(x·y − q)`, and proved it is its own saturation, so
that the chart ring's ambient open is `S` itself
(`AlgebraicGeometry.tateInvPatchSaturateOpens_tateInvNodeChartLocus`). The candidate chart ring
`AlgebraicGeometry.tateInvNodeChartSubring` is therefore a `Subring` of the sections of
`O_{Spf A}` over a **basic** open — and sections over a basic open are a ring this tree already
knows well.

This file makes that identification and draws the two consequences that are free once it is made.

## What is here

* **`AlgebraicGeometry.tateInvNodeChartAmbientEquiv`**: the ambient ring is
  `FormalSpectrum.awayCompletion (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)`,
  the completed localization `A{1/(x + y − 1)}`. It is
  `FormalSpectrum.sectionsBasicOpenEquiv` after the transport along
  `AlgebraicGeometry.tateInvNodeChartOpens_eq_basicOpen`.
* **`AlgebraicGeometry.tateInvNodeChartAwaySubring`**: the candidate chart ring, carried across
  that equivalence, as a `Subring` of `A{1/(x + y − 1)}` — with
  `AlgebraicGeometry.tateInvNodeChartSubringEquivAway` and
  `AlgebraicGeometry.exists_tateInvNodeChartAwayRingEquiv`, which is
  `AlgebraicGeometry.exists_tateInvNodeChartRingEquiv` restated at the explicit ring.
* **`AlgebraicGeometry.isAdicRing_tateInvNodeChartAmbient`**: the ambient ring is a complete adic
  ring, with `FormalSpectrum.awayCompletionIdeal` as ideal of definition. This is
  `FormalSpectrum.isAdicRing_awayCompletionIdeal` at the chosen coordinate, and it is the reason
  the identification is worth making: it is an adic structure on the ring the chart's ring sits
  inside, which the presheaf-section spelling does not display.
* **`AlgebraicGeometry.tateInvNodeChartAwayIdeal`**: the candidate ideal of definition on the
  chart ring — the contraction of `awayCompletionIdeal` along the inclusion, i.e. the subspace
  topology — together with
  **`AlgebraicGeometry.isHausdorff_tateInvNodeChartAwayIdeal`**: it is Hausdorff. The general
  lemma behind it, `AlgebraicGeometry.isHausdorff_comap_subtype`, is stated for an arbitrary
  subring of an arbitrary Hausdorff adic ring.
* **`AlgebraicGeometry.tateInvNodeChartAmbientHom`** and
  **`AlgebraicGeometry.range_tateInvNodeChartAmbientHom`**: the morphism
  `Spf A{1/(x + y − 1)} ⟶ Q` obtained by composing the basic-open chart with the patch inclusion
  `ι ⟨0⟩` and the quotient projection, and the computation that its range is **exactly** the
  candidate chart domain `π '' tateInvSaturate D(x + y − 1)`.
* **`FormalSpectrum.sectionsEquivOfEqBasicOpen_comp_sectionsOpenHom`** and its pointwise spelling
  **`FormalSpectrum.sectionsEquivOfEqBasicOpen_sectionsOpenHom`**: that equivalence carries the
  structural map of `Γ(U)` to the structural map of `R{1/f}`. Both used to be proved separately,
  in `FormalSchemes.TateInvNodeChartLegContinuous` and `FormalSchemes.TateInvChartBaseImage`,
  which are siblings that cannot cite each other; issue 1459 brought them here, beside the
  definition, where the pointwise one is `RingHom.congr_fun` of the composed one. Between them
  they serve **7** call sites in four modules. This is why the file imports
  `FormalSchemes.AdicOnOpenSections`, which is where `FormalSpectrum.sectionsOpenHom` and the
  transport lemma `FormalSpectrum.comp_eqToHom_sectionsOpenHom` live.

## What is *not* proved

**`hnode` is still undecided and nothing here is a chart.**

* **`tateInvNodeChartAwayIdeal` is not shown to be an ideal of *definition*.** Hausdorffness is
  proved; **completeness is not**, and neither is finite generation, and neither is the statement
  that the subring is closed in `A{1/(x + y − 1)}`. Those three are the residue of item (i) of
  this cluster's standing residue, and the reason they are not free is that a subring of a
  complete ring is complete only when it is closed.
* **`tateInvNodeChartAmbientHom` is not *shown* to be an open immersion, and must not be read as
  one.** Its range is the right set and nothing more: nothing here says the morphism factors
  through `Spf` of the subring, and no such factorisation is constructed. It is moreover
  **expected to fail injectivity**, which is why the chart must be built from the invariant
  subring rather than from this morphism — `π` should identify a point of `D(x)` in the model
  patch with its partner in `D(y)` under the `𝔾m`-inversion transition, both of which lie in
  `D(x + y − 1)` because
  `AlgebraicGeometry.preimage_transitionHom_comp_chartY_tateInvNodeChartLocus` and
  `AlgebraicGeometry.preimage_transitionInv_comp_chart_tateInvNodeChartLocus`
  (`FormalSchemes.TateInvNodeChartDomain`) say the transition matches the part of the domain the
  `x`-chart sees with the part the `y`-chart sees; that failure would be the Néron 1-gon's two
  glued points. **None of that is proved here**, and no two distinct points of the chain with the
  same image are exhibited. A successor who wants it should land it as a theorem from those two
  preimage lemmas rather than cite this paragraph.
* **Nothing here says the subring is nonzero, proper, or larger than the image of `R`.** This
  file adds no element of it. The image of the base ring is in it, at every open `S`
  (`AlgebraicGeometry.sectionsOpenHom_algebraMap_mem_tateInvChartAnnulusSubring`,
  `FormalSchemes.TateInvChartBaseImage`) and in this file's own spelling
  (`AlgebraicGeometry.algebraMap_mem_tateInvNodeChartAwaySubring`, same module) — but that is a
  lower bound and says nothing about the three questions above.

Nothing here weakens `LocallyRingedSpace.IsProperlyDiscontinuousOn`,
`LocallyRingedSpace.IsFreeProperlyDiscontinuous` or
`LocallyRingedSpace.freeActionQuotientFormalScheme`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1.4 — sections of
  `O_{Spf A}` on a basic open are the completed localization.
* [Deligne–Rapoport, *Les schémas de modules de courbes elliptiques*], II.1 — the Néron `n`-gon.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum TopologicalSpace
open Opposite TopCat.Presheaf

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **`R{1/f}` is Hausdorff** for `I` finitely generated: it is `AdicCompletion.isAdicRing_map` at
the localization, of which `IsHausdorff` is a component. Unlike
`FormalSpectrum.isAdicRing_awayCompletionIdeal` this needs no topology on `R{1/f}`. -/
theorem isHausdorff_awayCompletionIdeal (f : R) (hI : I.FG) :
    IsHausdorff (awayCompletionIdeal I f) (awayCompletion I f) :=
  (AdicCompletion.isAdicRing_map _ (hI.map _)).toIsAdicComplete.toIsHausdorff

/-- **Sections over an open that happens to be a basic open** are the completed localization:
`FormalSpectrum.sectionsBasicOpenEquiv` (EGA I, 10.1.4) after the transport along `hU`. The
`⊤`-analogue is `FormalSpectrum.sectionsEquivOfEqTop`. -/
def sectionsEquivOfEqBasicOpen {U : Opens (FormalSpectrum I)} {f : R} (hU : U = basicOpen I f) :
    ((locallyRingedSpaceObj I).presheaf.obj (op U) : Type u) ≃+* awayCompletion I f :=
  (((locallyRingedSpaceObj I).presheaf.mapIso
    (eqToIso (congrArg op hU))).commRingCatIsoToRingEquiv).trans (sectionsBasicOpenEquiv I f)

/-- **`FormalSpectrum.sectionsEquivOfEqBasicOpen` carries the structural map of `Γ(U)` to the
structural map of `R{1/f}`.** Both are restrictions from `⊤`, so this is
`FormalSpectrum.sectionsBasicOpenEquiv_comp_sectionsBasicOpenHom`
(`FormalSchemes.AdicOnBasicOpenSections`) after the transport along `hU` has been absorbed by
`FormalSpectrum.comp_eqToHom_sectionsOpenHom`. The pointwise spelling is
`FormalSpectrum.sectionsEquivOfEqBasicOpen_sectionsOpenHom`, which is derived from this one. -/
theorem sectionsEquivOfEqBasicOpen_comp_sectionsOpenHom {U : Opens (FormalSpectrum I)} {f : R}
    (hU : U = basicOpen I f) :
    (sectionsEquivOfEqBasicOpen I hU).toRingHom.comp (sectionsOpenHom I U) =
      awayCompletionHom I f := by
  rw [← sectionsBasicOpenEquiv_comp_sectionsBasicOpenHom I f, ← sectionsOpenHom_basicOpen I f,
    ← comp_eqToHom_sectionsOpenHom I hU, ← RingHom.comp_assoc]
  rfl

/-- **The pointwise spelling** of `FormalSpectrum.sectionsEquivOfEqBasicOpen_comp_sectionsOpenHom`,
which is the form the four legs of the chart condition are stated in
(`FormalSchemes.TateInvChartBaseImage`, `FormalSchemes.TateInvNodeChartLegGeneral`).

Stated at a general `I` on purpose: this is where the two spellings of the section ring meet, and
that reconciliation is cheap for the kernel only while `I`, `U` and `f` are variables. See
`FormalSchemes.AdicOnOpenSectionsPointwise`. -/
theorem sectionsEquivOfEqBasicOpen_sectionsOpenHom {U : Opens (FormalSpectrum I)} {f : R}
    (hU : U = basicOpen I f) (r : R) :
    sectionsEquivOfEqBasicOpen I hU (sectionsOpenHom I U r) = awayCompletionHom I f r :=
  RingHom.congr_fun (sectionsEquivOfEqBasicOpen_comp_sectionsOpenHom I hU) r

end FormalSpectrum

namespace AlgebraicGeometry

/-- **A subring of a Hausdorff adic ring is Hausdorff for the contracted ideal.** The contraction
`K.comap S.subtype` is the subspace topology's ideal, and `(K.comap S.subtype) ^ n` maps into
`K ^ n`, so an element of every power of the contraction has image in every power of `K`. No
completeness is involved and none is obtained: a subring of a complete ring is complete only when
it is closed. -/
theorem isHausdorff_comap_subtype {A : Type u} [CommRing A] (K : Ideal A) (S : Subring A)
    (hK : IsHausdorff K A) : IsHausdorff (K.comap S.subtype) S where
  haus' x hx := by
    have hval : ∀ n : ℕ, (x : A) ∈ K ^ n := by
      intro n
      have h1 : x ∈ (K.comap S.subtype) ^ n := by
        have h := hx n
        rwa [SModEq.zero, Ideal.mem_smul_top_self_iff] at h
      have hle : ((K.comap S.subtype) ^ n).map S.subtype ≤ K ^ n := by
        rw [Ideal.map_pow]
        exact pow_le_pow_left' Ideal.map_comap_le n
      exact hle (Ideal.mem_map_of_mem _ h1)
    exact Subtype.ext (hK.haus (x : A) fun n => by
      rw [SModEq.zero, Ideal.mem_smul_top_self_iff]; exact hval n)

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The node chart's ambient open is a basic open of the model patch.** The saturation theorem
`AlgebraicGeometry.tateInvPatchSaturateOpens_tateInvNodeChartLocus` says the ambient open is
`tateInvNodeChartLocus`, and that set is by definition the basic open of
`AlgebraicGeometry.annulusNodeChartCoord`. -/
theorem tateInvNodeChartOpens_eq_basicOpen :
    tateInvPatchSaturateOpens hq hI (isOpen_tateInvNodeChartLocus R I q) =
      basicOpen (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) :=
  (tateInvPatchSaturateOpens_tateInvNodeChartLocus R I q hq hI).trans (Opens.ext rfl)

/-- **The node chart's ambient ring is `A{1/(x + y − 1)}`.** The `Subring` that
`AlgebraicGeometry.tateInvNodeChartSubring` cuts out lives in the sections of `O_{Spf A}` over the
chosen domain; by `tateInvNodeChartOpens_eq_basicOpen` that domain is a basic open, so those
sections are the completed localization (EGA I, 10.1.4). -/
def tateInvNodeChartAmbientEquiv :
    ((FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q)).presheaf.obj
        (op (tateInvPatchSaturateOpens hq hI (isOpen_tateInvNodeChartLocus R I q))) : Type u) ≃+*
      awayCompletion (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q) :=
  haveI _hann : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  FormalSpectrum.sectionsEquivOfEqBasicOpen _ (tateInvNodeChartOpens_eq_basicOpen R I q hq hI)

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- **The ambient ring is a complete adic ring**, with `FormalSpectrum.awayCompletionIdeal` as
ideal of definition. This is what the identification buys: an adic structure on the ring the
chart's ring sits inside, which the presheaf-section spelling does not display. -/
theorem isAdicRing_tateInvNodeChartAmbient (hI : I.FG) :
    IsAdicRing (awayCompletionIdeal (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q)) :=
  FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI)

/-- **The candidate chart ring as a subring of `A{1/(x + y − 1)}`.** The image of
`AlgebraicGeometry.tateInvNodeChartSubring` under `tateInvNodeChartAmbientEquiv`. -/
def tateInvNodeChartAwaySubring : Subring
    (awayCompletion (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q)) :=
  Subring.map (tateInvNodeChartAmbientEquiv R I q hq hI).toRingHom
    (tateInvNodeChartSubring R I q hq hI)

/-- The two spellings of the candidate chart ring agree. -/
def tateInvNodeChartSubringEquivAway :
    tateInvNodeChartSubring R I q hq hI ≃+* tateInvNodeChartAwaySubring R I q hq hI :=
  RingEquiv.subringMap _

/-- **`Γ` of the candidate node chart is a subring of `A{1/(x + y − 1)}`.** This is
`AlgebraicGeometry.exists_tateInvNodeChartRingEquiv` restated at the explicit ring; the `V` and
its defining property are unchanged. -/
theorem exists_tateInvNodeChartAwayRingEquiv :
    ∃ (V : Opens (actionQuotient (tateInvPeriodAction R I q hq hI)).toTopCat)
      (_ : (Opens.map (actionQuotientπ
        (tateInvPeriodAction R I q hq hI)).toShHom.hom.base).obj V =
          tateInvSaturateOpens hq hI (isOpen_tateInvNodeChartLocus R I q)),
      Nonempty (((actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj (op V)) ≃+*
        tateInvNodeChartAwaySubring R I q hq hI) := by
  obtain ⟨V, hV, ⟨e⟩⟩ := exists_tateInvNodeChartRingEquiv R I q hq hI
  exact ⟨V, hV, ⟨e.trans (tateInvNodeChartSubringEquivAway R I q hq hI)⟩⟩

/-- **The candidate ideal of definition on the chart ring**: the contraction of the ambient ring's
ideal of definition along the inclusion — that is, the subspace topology.

`isHausdorff_tateInvNodeChartAwayIdeal` is what is proved about it. **It is not shown to be an
ideal of definition**: neither completeness nor finite generation is proved here. -/
def tateInvNodeChartAwayIdeal : Ideal (tateInvNodeChartAwaySubring R I q hq hI) :=
  (awayCompletionIdeal (annulusIdealOfDefinition R I q)
    (annulusNodeChartCoord R I q)).comap (tateInvNodeChartAwaySubring R I q hq hI).subtype

/-- **The candidate ideal of definition is Hausdorff.** `isHausdorff_comap_subtype` at the
ambient ring, which is Hausdorff by `FormalSpectrum.isHausdorff_awayCompletionIdeal`.

This is the separation half of "ideal of definition" and **not** the completeness half; see this
file's module docstring. -/
theorem isHausdorff_tateInvNodeChartAwayIdeal :
    IsHausdorff (tateInvNodeChartAwayIdeal R I q hq hI)
      (tateInvNodeChartAwaySubring R I q hq hI) :=
  isHausdorff_comap_subtype _ _
    (FormalSpectrum.isHausdorff_awayCompletionIdeal _ _ (annulusIdealOfDefinition_fg R I q hI))

section Quotient

variable {Q : LocallyRingedSpace.{u}}
variable {π : (tateChainInv R I q hq hI).toLocallyRingedSpace ⟶ Q}

/-- **The morphism `Spf A{1/(x + y − 1)} ⟶ Q`**: the basic-open chart of the chosen domain,
followed by the patch inclusion `ι ⟨0⟩` and the quotient projection.

**This is not shown to be an open immersion and must not be read as one** — its range is
computed and nothing else is; see `range_tateInvNodeChartAmbientHom` and this file's module
docstring. -/
def tateInvNodeChartAmbientHom :
    (FormalSpectrum.locallyRingedSpaceObj (awayCompletionIdeal
      (annulusIdealOfDefinition R I q) (annulusNodeChartCoord R I q))) ⟶ Q :=
  haveI _hann : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  FormalSpectrum.basicOpenChart _ _ ≫
    (tateChainInvFormalGlueData R I q hq hI).ι ⟨0⟩ ≫ π

/-- **Its range is exactly the candidate chart domain.** The basic-open chart's range is
`D(x + y − 1)` (`FormalSpectrum.range_basicOpenChart_base`), and the image of a saturation is the
image of a single patch's copy of the set
(`AlgebraicGeometry.image_base_tateInvSaturate_eq_image_base_ι`).

So the set a node chart has to cover is the range of one morphism out of an affine formal scheme.
It is **not** the claim that that morphism is a chart. -/
theorem range_tateInvNodeChartAmbientHom
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) :
    Set.range (tateInvNodeChartAmbientHom R I q hq hI (π := π)).base =
      ⇑π.base '' tateInvSaturate R I q hq hI (tateInvNodeChartLocus R I q) := by
  haveI _hann : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  rw [image_base_tateInvSaturate_eq_image_base_ι R I q hq hI h _ ⟨0⟩]
  have hcomp : ⇑(tateInvNodeChartAmbientHom R I q hq hI (π := π)).base =
      ⇑π.base ∘ ⇑((tateChainInvFormalGlueData R I q hq hI).ι ⟨0⟩).base ∘
        ⇑(FormalSpectrum.basicOpenChart (annulusIdealOfDefinition R I q)
          (annulusNodeChartCoord R I q)).base := rfl
  rw [hcomp, Set.range_comp, Set.range_comp]
  refine congrArg (Set.image _) (congrArg (Set.image _) ?_)
  exact range_basicOpenChart_base _ _ (annulusIdealOfDefinition_fg R I q hI)

end Quotient

end AlgebraicGeometry
