import FormalSchemes.FormalSpectrumPointExt
import FormalSchemes.InvariantSectionCongr
import FormalSchemes.PreimageBasicOpen
import FormalSchemes.TateInvNodeChartDescentBasicOpen

set_option linter.style.header false

/-!
# The preimage of `D(g)` along the node chart's base map, without a chart

Two reviews closed by naming the same frontier: the three undecided residues of hypothesis 4 of
`AlgebraicGeometry.exists_formalScheme_of_adicSections` — the space half
`IsIso (nodeChartQuotientHom …).base` and, per basic open `D(g)`, the injectivity and the
invariant-image clauses of `FormalSchemes.TateInvNodeChartDescentBasicOpen` — are all read over an
open that is a *preimage* along a base map whose only description on points is chart-by-chart,
with `AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.chart` a `Classical.choice`.

This file gives that open a name that contains no chart:

> `(nodeChartAdicHom …)⁻¹ D(g)` is the locus in the chain where the germ of
> `AlgebraicGeometry.nodeChartPsi g` is invertible

(`AlgebraicGeometry.preimage_basicOpen_nodeChartAdicHom_base` as opens,
`AlgebraicGeometry.mem_preimage_basicOpen_nodeChartAdicHom_iff` at a point). It is
`FormalSpectrum.preimage_basicOpen_eq` (`FormalSchemes.PreimageBasicOpen`) at
`AlgebraicGeometry.globalSectionsHom_nodeChartAdicHom`, which says the global-sections map of
`AlgebraicGeometry.nodeChartAdicHom` *is* `AlgebraicGeometry.nodeChartPsi`.

## What that buys, stated exactly

**The sheaf half is restated over the new open.**
`AlgebraicGeometry.isIso_desc_nodeChartAdicHom_iff_base_and_nonvanishing` is
`AlgebraicGeometry.isIso_desc_nodeChartAdicHom_iff_base_and_chain` with the preimage replaced by
the non-vanishing locus. The retyping of the section variable is **not** free — the two opens are
equal by `TopologicalSpace.Opens.ext` of a set-level argument, not by `rfl` — so it is paid for by
`AlgebraicGeometry.LocallyRingedSpace.injective_and_exists_congr`
(`FormalSchemes.InvariantSectionCongr`), and the family's members are composed with the presheaf's
`eqToHom` into `AlgebraicGeometry.nonvanishingSectionsHom`.

**The fibres of the space half's base map are described.**
`AlgebraicGeometry.restrictπ_comp_nodeChartQuotientHom` factors
`AlgebraicGeometry.nodeChartAdicHom` through the restricted projection, whose base map is
surjective (`AlgebraicGeometry.LocallyRingedSpace.base_surjective_restrictπ`), and points of a
formal spectrum are separated by basic opens
(`FormalSpectrum.eq_of_forall_mem_basicOpen_iff`, `FormalSchemes.FormalSpectrumPointExt`). So two
points of the chain have the same image exactly when they have the same germ-invertibility pattern
(`AlgebraicGeometry.base_nodeChartQuotientHom_restrictπ_eq_iff`), and

> `(nodeChartQuotientHom …).base` is **injective** ⟺ the family of non-vanishing loci separates
> the orbits

(`AlgebraicGeometry.injective_base_nodeChartQuotientHom_iff`). That is one of the two conditions in
`IsIso …base`, and it is now chart-free.

**Which basic opens meet the image is described.**
`AlgebraicGeometry.exists_mem_preimage_basicOpen_nodeChartQuotientHom_iff`: the image of the base
map meets `D(g)` exactly when `nodeChartPsi g` is invertible at *some* point of the chain. Together
with `FormalSpectrum.isBasis_basicOpen` this pins down the closure of the image.

**And the quotient-side preimage is an image.**
`AlgebraicGeometry.preimage_basicOpen_nodeChartQuotientHom_base_eq_image`:
`(nodeChartQuotientHom …)⁻¹ D(g)` is the image under the restricted projection of the same
non-vanishing locus. This is a set-level equality, obtained from `Set.image_preimage_eq` at the
surjectivity above.

## What is *not* proved here

**`hnode` is undecided in both directions, and nothing here moves it.** Everything below is a
restatement or a consequence of restatements; the module docstring of
`FormalSchemes.TateInvNodeChartDescentBasicOpen` records what the chain of reductions does and does
not say, and it is unchanged. In particular **refuting hypothesis 4 would not refute `hnode`**: the
hypothesis of `AlgebraicGeometry.exists_formalScheme_of_isIso_desc` is existential, while
hypothesis 4 is that condition at a *named* morphism, so it is a priori strictly stronger.

**Hypothesis 4 is still undecided in both directions.** No `g` is exhibited at which a clause
fails, and no argument that none exists is given.

**A description of a preimage is not a description of the base map on points.** Nothing below
produces a formula for `(nodeChartAdicHom …).base x` at a point of the chain, and nothing computes
which prime of the node chart's ring it is. What is produced is a name for the preimage of each
member of a basis of the target, plus the two consequences that a basis affords: the fibres
(`AlgebraicGeometry.base_nodeChartQuotientHom_restrictπ_eq_iff`) and which basic opens meet the
image (`AlgebraicGeometry.exists_mem_preimage_basicOpen_nodeChartQuotientHom_iff`).

**The space half is not decided, and only its injectivity clause is reached.** `IsIso …base` needs
the base map to be bijective *and* open. Preimages of a basis of the **target** determine fibres
and continuity; they do not determine the image and they say nothing about images of opens of the
source. So surjectivity and openness of `(nodeChartQuotientHom …).base` are untouched, and no Lean
statement below mentions either. That is the obstruction, and it is structural rather than a gap in
effort: the handle this file adds is a handle on preimages.

**No germ is computed.** Every statement below trades one undecided condition for another; each
right-hand side asks whether `AlgebraicGeometry.nodeChartPsi g` is invertible at a point of the
chain, and no such question is answered at any `g`. In particular no property of the node locus,
the annulus algebras or the `σ`-action is used or established.

**`AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.chart` is still a `Classical.choice`**, and
every other consumer of it is untouched. `AlgebraicGeometry.nodeChartAdicHom` is still built from
it; what became chart-free is one description of a preimage, not the morphism.
`Classical.choice` therefore still appears in `#print axioms` of everything below, and that is the
ambient one, not a new one.

**Nothing here bears on `AlgebraicGeometry.tateInvNodeChartAmbientHom`**, whose refutation as an
open immersion (`AlgebraicGeometry.not_isOpenImmersion_tateInvNodeChartAmbientHom_of_ne_top`) is
untouched.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4 (10.4.6), §10.6.
* [Deligne–Rapoport], II.1.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum TopologicalSpace
open AlgebraicGeometry.LocallyRingedSpace Opposite

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)
variable [TopologicalSpace ((actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj
  (op (tateInvNodeChartQuotientOpens R I q hq hI)))]
variable [IsAdicRing (tateInvNodeChartQuotientIdeal R I q hq hI)]
variable (hfgI : (tateInvNodeChartQuotientIdeal R I q hq hI).FG)
variable (hX : FormalScheme.AdicSectionsLocallyFG (tateInvNodeChartQuotientIdeal R I q hq hI)
  (nodeChartPsi R I q hq hI))

/-! ### The preimage, named -/

/-- **The preimage of `D(g)` along `AlgebraicGeometry.nodeChartAdicHom` is a non-vanishing locus.**
It is `AlgebraicGeometry.RingedSpace.basicOpen` of the global section
`AlgebraicGeometry.nodeChartPsi g` of the chain — an open of the chain's saturation named without
any chart.

`FormalSpectrum.preimage_basicOpen_eq` at
`AlgebraicGeometry.globalSectionsHom_nodeChartAdicHom`. The closing `rfl` is doing real work: it
identifies `.toLocallyRingedSpace.toRingedSpace` with `.toRingedSpace`, and without it the goal is
unsolved. -/
theorem preimage_basicOpen_nodeChartAdicHom_base (g) :
    (Opens.map (nodeChartAdicHom R I q hq hI hfgI hX).base).obj
        (basicOpen (tateInvNodeChartQuotientIdeal R I q hq hI) g) =
      (nodeChartSaturationFormalScheme R I q hq hI).toLocallyRingedSpace.toRingedSpace.basicOpen
        (nodeChartPsi R I q hq hI g) := by
  rw [FormalSpectrum.preimage_basicOpen_eq, globalSectionsHom_nodeChartAdicHom]
  rfl

/-- **The pointwise form.** A point of the chain is carried into `D(g)` exactly when the germ there
of `AlgebraicGeometry.nodeChartPsi g` is a unit. `FormalSpectrum.mem_preimage_basicOpen_iff` at the
same identification. -/
theorem mem_preimage_basicOpen_nodeChartAdicHom_iff (g)
    (x : (nodeChartSaturationFormalScheme R I q hq hI).toLocallyRingedSpace) :
    (nodeChartAdicHom R I q hq hI hfgI hX).base x ∈
        basicOpen (tateInvNodeChartQuotientIdeal R I q hq hI) g ↔
      IsUnit ((nodeChartSaturationFormalScheme R I q hq hI).presheaf.germ ⊤ x trivial
        (nodeChartPsi R I q hq hI g)) := by
  rw [FormalSpectrum.mem_preimage_basicOpen_iff (tateInvNodeChartQuotientIdeal R I q hq hI)
    (nodeChartSaturationFormalScheme R I q hq hI).toLocallyRingedSpace
    (nodeChartAdicHom R I q hq hI hfgI hX) g x,
    globalSectionsHom_nodeChartAdicHom R I q hq hI hfgI hX]
  exact Iff.rfl

/-- **The base map of `AlgebraicGeometry.nodeChartAdicHom` factors through the restricted
projection**, read at a point. `AlgebraicGeometry.restrictπ_comp_nodeChartQuotientHom` with the
underlying maps applied to `z`. -/
theorem base_nodeChartQuotientHom_restrictπ_base
    (z : (nodeChartSaturationFormalScheme R I q hq hI).toLocallyRingedSpace) :
    (nodeChartQuotientHom R I q hq hI hfgI hX).base
        ((LocallyRingedSpace.restrictπ (actionQuotientπ (tateInvPeriodAction R I q hq hI))
          (tateInvNodeChartQuotientOpens R I q hq hI)).base z) =
      (nodeChartAdicHom R I q hq hI hfgI hX).base z := by
  rw [← restrictπ_comp_nodeChartQuotientHom R I q hq hI hfgI hX]
  rfl

/-! ### The sheaf half over the non-vanishing locus -/

/-- **The member of the sheaf half's family at `g`, read over the non-vanishing locus.**
`FormalSpectrum.basicOpenSectionsHom` of `AlgebraicGeometry.nodeChartAdicHom` composed with the
presheaf's `eqToHom` along `AlgebraicGeometry.preimage_basicOpen_nodeChartAdicHom_base`. The source
is the completed localization `FormalSpectrum.awayCompletion` and the target is the sections of the
chain over the locus where the germ of `AlgebraicGeometry.nodeChartPsi g` is invertible; no
preimage occurs in either. -/
def nonvanishingSectionsHom (g) :
    awayCompletion (tateInvNodeChartQuotientIdeal R I q hq hI) g →+*
      (nodeChartSaturationFormalScheme R I q hq hI).presheaf.obj
        (op ((nodeChartSaturationFormalScheme R I q hq hI).toLocallyRingedSpace.toRingedSpace
          |>.basicOpen (nodeChartPsi R I q hq hI g))) :=
  ((nodeChartSaturationFormalScheme R I q hq hI).presheaf.map
      (eqToHom (congrArg op
        (preimage_basicOpen_nodeChartAdicHom_base R I q hq hI hfgI hX g)))).hom.comp
    (basicOpenSectionsHom (tateInvNodeChartQuotientIdeal R I q hq hI) _
      (nodeChartAdicHom R I q hq hI hfgI hX) g)

/-- **Hypothesis 4 with no preimage in the sheaf half.** The descent of
`AlgebraicGeometry.nodeChartAdicHom` is an isomorphism exactly when the base map of
`AlgebraicGeometry.nodeChartQuotientHom` is an isomorphism and, for every
`g : Γ (T_inv/⟨σ⟩, V₀)`, the ring homomorphism `AlgebraicGeometry.nonvanishingSectionsHom … g` is
injective with image the invariant sections.

`AlgebraicGeometry.isIso_desc_nodeChartAdicHom_iff_base_and_chain` with each member transported by
`AlgebraicGeometry.LocallyRingedSpace.injective_and_exists_congr`. The first conjunct is carried
through untouched and is not addressed anywhere below. -/
theorem isIso_desc_nodeChartAdicHom_iff_base_and_nonvanishing :
    IsIso ((isActionQuotient_actionQuotientπ (tateInvNodeChartRestrictedAction R I q hq hI)).desc
        (nodeChartAdicHom R I q hq hI hfgI hX)
        (isActionInvariant_nodeChartAdicHom R I q hq hI hfgI hX)) ↔
      IsIso (nodeChartQuotientHom R I q hq hI hfgI hX).base ∧
        ∀ g : (actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj
            (op (tateInvNodeChartQuotientOpens R I q hq hI)),
          Function.Injective (nonvanishingSectionsHom R I q hq hI hfgI hX g) ∧
            ∀ t, IsInvariantSection (tateInvNodeChartRestrictedAction R I q hq hI) t →
              ∃ r, nonvanishingSectionsHom R I q hq hI hfgI hX g r = t :=
  (isIso_desc_nodeChartAdicHom_iff_base_and_chain R I q hq hI hfgI hX).trans
    (and_congr_right fun _ => forall_congr' fun g =>
      (LocallyRingedSpace.injective_and_exists_congr _
        (preimage_basicOpen_nodeChartAdicHom_base R I q hq hI hfgI hX g) _).symm)

/-! ### The fibres of the space half's base map -/

/-- **Two points of the chain have the same image exactly when their germ-invertibility patterns
agree.** The forward direction is
`AlgebraicGeometry.mem_preimage_basicOpen_nodeChartAdicHom_iff` read at both points; the reverse is
that direction together with `FormalSpectrum.eq_of_forall_mem_basicOpen_iff`, which says a point of
a formal spectrum is determined by the basic opens containing it. -/
theorem base_nodeChartQuotientHom_restrictπ_eq_iff
    (x y : (nodeChartSaturationFormalScheme R I q hq hI).toLocallyRingedSpace) :
    (nodeChartQuotientHom R I q hq hI hfgI hX).base
        ((LocallyRingedSpace.restrictπ (actionQuotientπ (tateInvPeriodAction R I q hq hI))
          (tateInvNodeChartQuotientOpens R I q hq hI)).base x) =
      (nodeChartQuotientHom R I q hq hI hfgI hX).base
        ((LocallyRingedSpace.restrictπ (actionQuotientπ (tateInvPeriodAction R I q hq hI))
          (tateInvNodeChartQuotientOpens R I q hq hI)).base y) ↔
      ∀ g, IsUnit ((nodeChartSaturationFormalScheme R I q hq hI).presheaf.germ ⊤ x trivial
          (nodeChartPsi R I q hq hI g)) ↔
        IsUnit ((nodeChartSaturationFormalScheme R I q hq hI).presheaf.germ ⊤ y trivial
          (nodeChartPsi R I q hq hI g)) := by
  simp only [base_nodeChartQuotientHom_restrictπ_base]
  constructor
  · intro h g
    exact ((mem_preimage_basicOpen_nodeChartAdicHom_iff R I q hq hI hfgI hX g x).symm.trans
      (iff_of_eq (congrArg (· ∈ basicOpen (tateInvNodeChartQuotientIdeal R I q hq hI) g) h))).trans
      (mem_preimage_basicOpen_nodeChartAdicHom_iff R I q hq hI hfgI hX g y)
  · intro h
    exact FormalSpectrum.eq_of_forall_mem_basicOpen_iff
      (tateInvNodeChartQuotientIdeal R I q hq hI) fun f =>
      (mem_preimage_basicOpen_nodeChartAdicHom_iff R I q hq hI hfgI hX f x).trans
        ((h f).trans
          (mem_preimage_basicOpen_nodeChartAdicHom_iff R I q hq hI hfgI hX f y).symm)

/-- **The injectivity clause of the space half, with no chart in it.** The base map of
`AlgebraicGeometry.nodeChartQuotientHom` is injective exactly when two points of the chain with the
same germ-invertibility pattern already have the same image under the restricted projection — that
is, when the family of non-vanishing loci separates the orbits.

`AlgebraicGeometry.base_nodeChartQuotientHom_restrictπ_eq_iff` at every pair, transported across
the surjectivity of the restricted projection's base map
(`AlgebraicGeometry.LocallyRingedSpace.base_surjective_restrictπ`).

**This is one of the two conditions in `IsIso …base` and not both**: surjectivity and openness of
the base map are untouched; see the module docstring. -/
theorem injective_base_nodeChartQuotientHom_iff :
    Function.Injective (nodeChartQuotientHom R I q hq hI hfgI hX).base ↔
      ∀ x y : (nodeChartSaturationFormalScheme R I q hq hI).toLocallyRingedSpace,
        (∀ g, IsUnit ((nodeChartSaturationFormalScheme R I q hq hI).presheaf.germ ⊤ x trivial
            (nodeChartPsi R I q hq hI g)) ↔
          IsUnit ((nodeChartSaturationFormalScheme R I q hq hI).presheaf.germ ⊤ y trivial
            (nodeChartPsi R I q hq hI g))) →
        (LocallyRingedSpace.restrictπ (actionQuotientπ (tateInvPeriodAction R I q hq hI))
            (tateInvNodeChartQuotientOpens R I q hq hI)).base x =
          (LocallyRingedSpace.restrictπ (actionQuotientπ (tateInvPeriodAction R I q hq hI))
            (tateInvNodeChartQuotientOpens R I q hq hI)).base y := by
  have hsurj := LocallyRingedSpace.base_surjective_restrictπ
    (isActionQuotient_actionQuotientπ (tateInvPeriodAction R I q hq hI))
    (tateInvNodeChartQuotientOpens R I q hq hI)
  constructor
  · intro hinj x y hg
    exact hinj ((base_nodeChartQuotientHom_restrictπ_eq_iff R I q hq hI hfgI hX x y).mpr hg)
  · intro hall y₁ y₂ hy
    obtain ⟨x₁, rfl⟩ := hsurj y₁
    obtain ⟨x₂, rfl⟩ := hsurj y₂
    exact hall x₁ x₂ ((base_nodeChartQuotientHom_restrictπ_eq_iff R I q hq hI hfgI hX x₁ x₂).mp hy)

/-! ### The quotient-side preimage, and which basic opens meet the image -/

/-- **The preimage of `D(g)` on the quotient side is the image of the non-vanishing locus.** The
non-vanishing locus is the preimage along the restricted projection of the open in question
(`AlgebraicGeometry.preimage_basicOpen_nodeChartAdicHom_base` and
`AlgebraicGeometry.restrictπ_comp_nodeChartQuotientHom`), and that projection's base map is
surjective, so `Set.image_preimage_eq` returns the open itself.

A set-level equality: the right-hand side is an image and need not be recognised as an open by its
description, although it is one. -/
theorem preimage_basicOpen_nodeChartQuotientHom_base_eq_image (g) :
    ((Opens.map (nodeChartQuotientHom R I q hq hI hfgI hX).base).obj
        (basicOpen (tateInvNodeChartQuotientIdeal R I q hq hI) g) : Set _) =
      (LocallyRingedSpace.restrictπ (actionQuotientπ (tateInvPeriodAction R I q hq hI))
          (tateInvNodeChartQuotientOpens R I q hq hI)).base ''
        ((nodeChartSaturationFormalScheme R I q hq hI).toLocallyRingedSpace.toRingedSpace.basicOpen
          (nodeChartPsi R I q hq hI g)).carrier := by
  have hpre :
      ((nodeChartSaturationFormalScheme R I q hq hI).toLocallyRingedSpace.toRingedSpace.basicOpen
        (nodeChartPsi R I q hq hI g)).carrier =
      (LocallyRingedSpace.restrictπ (actionQuotientπ (tateInvPeriodAction R I q hq hI))
          (tateInvNodeChartQuotientOpens R I q hq hI)).base ⁻¹'
        ((Opens.map (nodeChartQuotientHom R I q hq hI hfgI hX).base).obj
          (basicOpen (tateInvNodeChartQuotientIdeal R I q hq hI) g) : Set _) := by
    rw [← preimage_basicOpen_nodeChartAdicHom_base R I q hq hI hfgI hX g,
      ← restrictπ_comp_nodeChartQuotientHom R I q hq hI hfgI hX]
    rfl
  rw [hpre, Set.image_preimage_eq _ (LocallyRingedSpace.base_surjective_restrictπ
    (isActionQuotient_actionQuotientπ (tateInvPeriodAction R I q hq hI))
    (tateInvNodeChartQuotientOpens R I q hq hI))]

/-- **Which basic opens meet the image of the base map.** The image of
`(nodeChartQuotientHom …).base` meets `D(g)` exactly when `AlgebraicGeometry.nodeChartPsi g` is
invertible at some point of the chain.

Since the basic opens are a basis (`FormalSpectrum.isBasis_basicOpen`), this determines the
*closure* of the image. It does **not** determine the image, and no statement here does. -/
theorem exists_mem_preimage_basicOpen_nodeChartQuotientHom_iff (g) :
    (∃ y, (nodeChartQuotientHom R I q hq hI hfgI hX).base y ∈
        basicOpen (tateInvNodeChartQuotientIdeal R I q hq hI) g) ↔
      ∃ x, IsUnit ((nodeChartSaturationFormalScheme R I q hq hI).presheaf.germ ⊤ x trivial
        (nodeChartPsi R I q hq hI g)) := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := LocallyRingedSpace.base_surjective_restrictπ
      (isActionQuotient_actionQuotientπ (tateInvPeriodAction R I q hq hI))
      (tateInvNodeChartQuotientOpens R I q hq hI) y
    rw [base_nodeChartQuotientHom_restrictπ_base] at hy
    exact ⟨x, (mem_preimage_basicOpen_nodeChartAdicHom_iff R I q hq hI hfgI hX g x).mp hy⟩
  · rintro ⟨x, hx⟩
    exact ⟨_, (base_nodeChartQuotientHom_restrictπ_base R I q hq hI hfgI hX x).symm ▸
      (mem_preimage_basicOpen_nodeChartAdicHom_iff R I q hq hI hfgI hX g x).mpr hx⟩

end AlgebraicGeometry

end
