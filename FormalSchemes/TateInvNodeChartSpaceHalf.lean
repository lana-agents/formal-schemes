import FormalSchemes.TateInvNodeChartBasicOpenPreimage
import FormalSchemes.TopCatIsoOpenMap

set_option linter.style.header false

/-!
# The space half of hypothesis 4 is a statement about the chain, in all three of its clauses

`AlgebraicGeometry.isIso_desc_nodeChartAdicHom_iff_base_and_c`
(`FormalSchemes.TateInvNodeChartDescentIso`) splits hypothesis 4 of
`AlgebraicGeometry.exists_formalScheme_of_adicSections` into a **space half**
`IsIso (nodeChartQuotientHom …).base` and a **sheaf half**. Two files worked the sheaf half down to
a family of ring maps over non-vanishing loci of the chain
(`FormalSchemes.TateInvNodeChartDescentBasicOpen`,
`FormalSchemes.TateInvNodeChartBasicOpenPreimage`). Of the space half, only the injectivity clause
had been reached — `AlgebraicGeometry.injective_base_nodeChartQuotientHom_iff`.

This file reaches the other two. It does **not** decide any of them.

## The one ingredient, and why it costs nothing

`AlgebraicGeometry.restrictπ_comp_nodeChartQuotientHom` factors
`AlgebraicGeometry.nodeChartAdicHom` — the morphism *out of the chain* — through the restricted
projection and `AlgebraicGeometry.nodeChartQuotientHom`. That projection's base map is
**surjective** (`AlgebraicGeometry.LocallyRingedSpace.base_surjective_restrictπ`) and **open**
(`AlgebraicGeometry.LocallyRingedSpace.isOpenMap_base_restrictπ`, added to
`FormalSchemes.ActionQuotientRestrictQuotient` for this file and carrying no hypothesis on the
action). Along an open surjection both remaining clauses transfer, in both directions:

* surjectivity, because the range of a map equals the range of its composite with a surjection;
* openness, by `IsOpenMap.comp` one way and `IsOpenMap.of_comp` the other, both from Mathlib.

So `AlgebraicGeometry.surjective_base_nodeChartQuotientHom_iff` and
`AlgebraicGeometry.isOpenMap_base_nodeChartQuotientHom_iff` put both clauses on
`AlgebraicGeometry.nodeChartAdicHom`, and `AlgebraicGeometry.isIso_base_nodeChartQuotientHom_iff`
assembles the space half out of the three, through
`TopCat.isIso_iff_bijective_and_isOpenMap`.

**What that is worth, stated exactly.** Not that any clause becomes easy — none is decided here.
What it buys is that `AlgebraicGeometry.isIso_desc_nodeChartAdicHom_iff_chain` now states
hypothesis 4 with every clause read on the chain: the quotient survives only as the codomain of
the projection in the orbit-separation clause and as the index ring of the sheaf half's family,
which is the ring hypothesis 4 is about and cannot be traded away. **The quotient is not the
obstruction in either half**, and a successor need not ask whether it is.

## The image, and what a basis of the target can and cannot say

`AlgebraicGeometry.exists_mem_preimage_basicOpen_nodeChartQuotientHom_iff` says which basic opens
meet the image, and its docstring says that this determines the *closure* of the image.
`AlgebraicGeometry.dense_range_base_nodeChartQuotientHom_iff` makes that a theorem: the image is
dense exactly when every basic open that is inhabited at all contains a point where the germ of
`AlgebraicGeometry.nodeChartPsi g` is invertible. It is
`TopologicalSpace.IsTopologicalBasis.dense_iff` at `FormalSpectrum.isTopologicalBasis_basicOpen`.

Density is strictly weaker than the surjectivity clause and is not a step towards it: a dense image
in a formal spectrum need not be all of it, and nothing below claims otherwise.

## Main results

* `AlgebraicGeometry.surjective_base_nodeChartQuotientHom_iff` and
  `AlgebraicGeometry.isOpenMap_base_nodeChartQuotientHom_iff`: the surjectivity and openness
  clauses of the space half, read on `AlgebraicGeometry.nodeChartAdicHom`.
* `AlgebraicGeometry.isIso_base_nodeChartQuotientHom_iff`: **the space half**, all three clauses
  read on the chain.
* `AlgebraicGeometry.isIso_desc_nodeChartAdicHom_iff_chain`: hypothesis 4 with its space half in
  that form.
* `AlgebraicGeometry.dense_range_base_nodeChartQuotientHom_iff`: the closure of the image, as a
  theorem rather than a sentence.

## What is *not* proved here

**`hnode` is undecided, in both directions, and nothing here moves it.** `hnode` is the hypothesis
of `AlgebraicGeometry.exists_formalScheme_of_adicSections`. Everything below is a restatement of
hypothesis 4 and inherits what `FormalSchemes.TateInvNodeChartDescentIso`'s
`## What is *not* proved here` records: in particular **refuting hypothesis 4 would not refute
`hnode`**, because the hypothesis of `AlgebraicGeometry.exists_formalScheme_of_isIso_desc` is
existential while hypothesis 4 is that condition at a *named* morphism, so it is a priori strictly
stronger; and the chain onward through
`AlgebraicGeometry.exists_formalScheme_of_iso_restrict_tateInvNodeChartQuotientOpens` is one-way as
well.

**No clause is decided.** No point of the chain is exhibited at which
`AlgebraicGeometry.nodeChartPsi g` is or is not invertible; no `g` is exhibited at which a sheaf
clause fails; and no argument that the base map is or is not surjective, injective or open is
given. Every statement below trades one undecided condition for another, and none uses a property
of the node locus, of the annulus algebras or of the `σ`-action.

**Nothing about the sheaf half.** Its two clauses are carried through
`AlgebraicGeometry.isIso_desc_nodeChartAdicHom_iff_chain` exactly as
`AlgebraicGeometry.isIso_desc_nodeChartAdicHom_iff_base_and_nonvanishing` states them, and
`AlgebraicGeometry.nonvanishingSectionsHom` is not touched.

**A description of a preimage is still not, on its own, a description of the base map on points.**
Nothing here produces a formula for the base map of `AlgebraicGeometry.nodeChartAdicHom` at a point
of the chain. One exists on the tree and it comes from evaluating the germ rather than from any
handle on preimages: `AlgebraicGeometry.eq_base_nodeChartAdicHom_nodeChartPatchChartLift`
(`FormalSchemes.TateInvNodeChartPatchChartGerm`) pins the image point at every point of every patch
chart. It decides no clause below.
`AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.chart` is still a `Classical.choice`,
so `Classical.choice` appears in `#print axioms` of everything below; that is the ambient one and
not a new one.

**Density is not surjectivity.** `AlgebraicGeometry.dense_range_base_nodeChartQuotientHom_iff`
decides neither clause of bijectivity, and the surjectivity clause is not reduced to it anywhere.

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

/-! ### Surjectivity and openness, moved onto the chain -/

/-- **The surjectivity clause of the space half, on the chain.** The base map of
`AlgebraicGeometry.nodeChartQuotientHom` is surjective exactly when that of
`AlgebraicGeometry.nodeChartAdicHom` is.

`AlgebraicGeometry.base_nodeChartQuotientHom_restrictπ_base` factors the second through the first,
and `AlgebraicGeometry.LocallyRingedSpace.base_surjective_restrictπ` makes the factor surjective,
so the two have the same range. No hypothesis is discharged and neither side is decided. -/
theorem surjective_base_nodeChartQuotientHom_iff :
    Function.Surjective (nodeChartQuotientHom R I q hq hI hfgI hX).base ↔
      Function.Surjective (nodeChartAdicHom R I q hq hI hfgI hX).base := by
  constructor
  · intro h z
    obtain ⟨y, hy⟩ := h z
    obtain ⟨x, rfl⟩ := LocallyRingedSpace.base_surjective_restrictπ
      (isActionQuotient_actionQuotientπ (tateInvPeriodAction R I q hq hI))
      (tateInvNodeChartQuotientOpens R I q hq hI) y
    exact ⟨x, (base_nodeChartQuotientHom_restrictπ_base R I q hq hI hfgI hX x).symm.trans hy⟩
  · intro h z
    obtain ⟨x, hx⟩ := h z
    exact ⟨_, (base_nodeChartQuotientHom_restrictπ_base R I q hq hI hfgI hX x).trans hx⟩

/-- **The openness clause of the space half, on the chain.** The base map of
`AlgebraicGeometry.nodeChartQuotientHom` is an open map exactly when that of
`AlgebraicGeometry.nodeChartAdicHom` is.

The restricted projection's base map is an **open surjection** —
`AlgebraicGeometry.LocallyRingedSpace.isOpenMap_base_restrictπ` and
`AlgebraicGeometry.LocallyRingedSpace.base_surjective_restrictπ` — so `IsOpenMap.comp` gives one
direction and `IsOpenMap.of_comp` the other.

Unlike the surjectivity clause this genuinely needs the projection to be open, which is why that
lemma had to be added; openness of a composite says nothing about a factor along a bare
surjection. -/
theorem isOpenMap_base_nodeChartQuotientHom_iff :
    IsOpenMap ⇑(ConcreteCategory.hom (nodeChartQuotientHom R I q hq hI hfgI hX).base) ↔
      IsOpenMap ⇑(ConcreteCategory.hom (nodeChartAdicHom R I q hq hI hfgI hX).base) := by
  have hfac : ⇑(ConcreteCategory.hom (nodeChartAdicHom R I q hq hI hfgI hX).base) =
      ⇑(ConcreteCategory.hom (nodeChartQuotientHom R I q hq hI hfgI hX).base) ∘
        ⇑(ConcreteCategory.hom (LocallyRingedSpace.restrictπ
          (actionQuotientπ (tateInvPeriodAction R I q hq hI))
          (tateInvNodeChartQuotientOpens R I q hq hI)).base) :=
    funext fun z => (base_nodeChartQuotientHom_restrictπ_base R I q hq hI hfgI hX z).symm
  have hopen := LocallyRingedSpace.isOpenMap_base_restrictπ
    (isActionQuotient_actionQuotientπ (tateInvPeriodAction R I q hq hI))
    (tateInvNodeChartQuotientOpens R I q hq hI)
  have hsurj := LocallyRingedSpace.base_surjective_restrictπ
    (isActionQuotient_actionQuotientπ (tateInvPeriodAction R I q hq hI))
    (tateInvNodeChartQuotientOpens R I q hq hI)
  constructor
  · intro h
    rw [hfac]
    exact h.comp hopen
  · intro h
    exact IsOpenMap.of_comp (by fun_prop) hsurj (hfac ▸ h)

/-! ### The space half, assembled -/

/-- **The space half of hypothesis 4, with every clause read on the chain.** The base map of
`AlgebraicGeometry.nodeChartQuotientHom` is an isomorphism exactly when the family of
non-vanishing loci separates the orbits, and the base map of
`AlgebraicGeometry.nodeChartAdicHom` is surjective, and that same map is open.

`TopCat.isIso_iff_bijective_and_isOpenMap` (`FormalSchemes.TopCatIsoOpenMap`) at
`AlgebraicGeometry.injective_base_nodeChartQuotientHom_iff`,
`AlgebraicGeometry.surjective_base_nodeChartQuotientHom_iff` and
`AlgebraicGeometry.isOpenMap_base_nodeChartQuotientHom_iff`. The injectivity clause is **not**
reproved: it is that theorem applied.

None of the three is decided. What is established is that none of them is a question about the
quotient. -/
theorem isIso_base_nodeChartQuotientHom_iff :
    IsIso (nodeChartQuotientHom R I q hq hI hfgI hX).base ↔
      (∀ x y : (nodeChartSaturationFormalScheme R I q hq hI).toLocallyRingedSpace,
          (∀ g, IsUnit ((nodeChartSaturationFormalScheme R I q hq hI).presheaf.germ ⊤ x trivial
              (nodeChartPsi R I q hq hI g)) ↔
            IsUnit ((nodeChartSaturationFormalScheme R I q hq hI).presheaf.germ ⊤ y trivial
              (nodeChartPsi R I q hq hI g))) →
          (LocallyRingedSpace.restrictπ (actionQuotientπ (tateInvPeriodAction R I q hq hI))
              (tateInvNodeChartQuotientOpens R I q hq hI)).base x =
            (LocallyRingedSpace.restrictπ (actionQuotientπ (tateInvPeriodAction R I q hq hI))
              (tateInvNodeChartQuotientOpens R I q hq hI)).base y) ∧
        Function.Surjective (nodeChartAdicHom R I q hq hI hfgI hX).base ∧
        IsOpenMap ⇑(ConcreteCategory.hom (nodeChartAdicHom R I q hq hI hfgI hX).base) := by
  rw [TopCat.isIso_iff_bijective_and_isOpenMap, Function.Bijective,
    injective_base_nodeChartQuotientHom_iff R I q hq hI hfgI hX,
    surjective_base_nodeChartQuotientHom_iff R I q hq hI hfgI hX,
    isOpenMap_base_nodeChartQuotientHom_iff R I q hq hI hfgI hX, and_assoc]

/-- **Hypothesis 4, with its space half on the chain.**
`AlgebraicGeometry.isIso_desc_nodeChartAdicHom_iff_base_and_nonvanishing` with its first conjunct
replaced by `AlgebraicGeometry.isIso_base_nodeChartQuotientHom_iff`.

Read the right-hand side: the quotient occurs as the codomain of the restricted projection in the
orbit-separation clause, and as the type of the index variable `g` of the sheaf half's family —
which is the ring hypothesis 4 is about and cannot be traded away. Every other occurrence is a
question about `AlgebraicGeometry.nodeChartAdicHom` and the chain. **That is the whole content of
this file**, and it decides nothing. -/
theorem isIso_desc_nodeChartAdicHom_iff_chain :
    IsIso ((isActionQuotient_actionQuotientπ (tateInvNodeChartRestrictedAction R I q hq hI)).desc
        (nodeChartAdicHom R I q hq hI hfgI hX)
        (isActionInvariant_nodeChartAdicHom R I q hq hI hfgI hX)) ↔
      ((∀ x y : (nodeChartSaturationFormalScheme R I q hq hI).toLocallyRingedSpace,
            (∀ g, IsUnit ((nodeChartSaturationFormalScheme R I q hq hI).presheaf.germ ⊤ x trivial
                (nodeChartPsi R I q hq hI g)) ↔
              IsUnit ((nodeChartSaturationFormalScheme R I q hq hI).presheaf.germ ⊤ y trivial
                (nodeChartPsi R I q hq hI g))) →
            (LocallyRingedSpace.restrictπ (actionQuotientπ (tateInvPeriodAction R I q hq hI))
                (tateInvNodeChartQuotientOpens R I q hq hI)).base x =
              (LocallyRingedSpace.restrictπ (actionQuotientπ (tateInvPeriodAction R I q hq hI))
                (tateInvNodeChartQuotientOpens R I q hq hI)).base y) ∧
          Function.Surjective (nodeChartAdicHom R I q hq hI hfgI hX).base ∧
          IsOpenMap ⇑(ConcreteCategory.hom (nodeChartAdicHom R I q hq hI hfgI hX).base)) ∧
        ∀ g : (actionQuotient (tateInvPeriodAction R I q hq hI)).presheaf.obj
            (op (tateInvNodeChartQuotientOpens R I q hq hI)),
          Function.Injective (nonvanishingSectionsHom R I q hq hI hfgI hX g) ∧
            ∀ t, IsInvariantSection (tateInvNodeChartRestrictedAction R I q hq hI) t →
              ∃ r, nonvanishingSectionsHom R I q hq hI hfgI hX g r = t :=
  (isIso_desc_nodeChartAdicHom_iff_base_and_nonvanishing R I q hq hI hfgI hX).trans
    (and_congr_left' (isIso_base_nodeChartQuotientHom_iff R I q hq hI hfgI hX))

/-! ### The closure of the image -/

/-- **The closure of the image, as a theorem.** The image of the base map of
`AlgebraicGeometry.nodeChartQuotientHom` is dense exactly when every basic open of the node chart's
formal spectrum that is inhabited at all contains a point where the germ of
`AlgebraicGeometry.nodeChartPsi g` is invertible somewhere on the chain.

`TopologicalSpace.IsTopologicalBasis.dense_iff` at `FormalSpectrum.isTopologicalBasis_basicOpen`,
fed by `AlgebraicGeometry.exists_mem_preimage_basicOpen_nodeChartQuotientHom_iff` — whose docstring
says in prose that a basis of the target determines the closure of the image. This is that
sentence.

**Density is not the surjectivity clause**, is strictly weaker than it, and nothing here reduces
one to the other. -/
theorem dense_range_base_nodeChartQuotientHom_iff :
    Dense (Set.range ⇑(ConcreteCategory.hom
        (nodeChartQuotientHom R I q hq hI hfgI hX).base)) ↔
      ∀ g, (∃ p, p ∈ basicOpen (tateInvNodeChartQuotientIdeal R I q hq hI) g) →
        ∃ x, IsUnit ((nodeChartSaturationFormalScheme R I q hq hI).presheaf.germ ⊤ x trivial
          (nodeChartPsi R I q hq hI g)) := by
  have hb := (FormalSpectrum.isTopologicalBasis_basicOpen
    (tateInvNodeChartQuotientIdeal R I q hq hI)).dense_iff
    (s := Set.range ⇑(ConcreteCategory.hom (nodeChartQuotientHom R I q hq hI hfgI hX).base))
  constructor
  · intro h g hg
    obtain ⟨y, hy, z, hz⟩ := hb.mp h _ ⟨g, rfl⟩ hg
    exact (exists_mem_preimage_basicOpen_nodeChartQuotientHom_iff R I q hq hI hfgI hX g).mp
      ⟨z, hz ▸ hy⟩
  · intro h
    refine hb.mpr ?_
    rintro _ ⟨g, rfl⟩ hg
    obtain ⟨y, hy⟩ := (exists_mem_preimage_basicOpen_nodeChartQuotientHom_iff
      R I q hq hI hfgI hX g).mpr (h g hg)
    exact ⟨_, hy, y, rfl⟩

end AlgebraicGeometry

end
