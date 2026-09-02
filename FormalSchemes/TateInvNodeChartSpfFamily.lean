import FormalSchemes.SpfHomFamilyChart
import FormalSchemes.TateInvNodeChartAmbient

set_option linter.style.header false

/-!
# The EGA I 10.6.10 route to the node chart is circular, and the circularity is not in the capstone

Issue 1197 asks for an open immersion out of a formal spectrum into `T_inv/⟨σ⟩` whose range covers
`π '' tateInvSaturate D(x + y − 1)` — the one set of points of the quotient that no chart on this
tree reaches. Every survey of the mapping-out machinery has stopped at the same place:
`FormalSpectrum.existsUnique_hom_thickeningMap` (and, after issue 62m, its formal-affine variant
`FormalSpectrum.existsUnique_hom_thickeningMap_spfCover`) needs the *target* covered by affine
opens, and `T_inv/⟨σ⟩`'s affine cover is missing exactly the chart being built.

Issue 1197's status section sharpens that into an open question and calls it the sharpest one on
the row:

> the circularity is in the **capstone**: `FormalSpectrum.spfHomOfFamily` itself needs only an
> affine open of the target **containing the image of each basic open of the source**, not a cover
> of the target. Whether that weaker input can be met at a node is unexamined.

**It cannot, and the reason has nothing to do with nodes.** `FormalSchemes.SpfHomFamilyChart`
proves, for an arbitrary target, that every point the glued morphism reaches lies in one of the
`U i` — the covering hypothesis the weaker input drops is about the *target as a whole*, not about
the points the morphism actually hits. So a `U i` containing a node image is an affine open of
`T_inv/⟨σ⟩` containing a node image, which is what `hnode` asks for.

This file states that at the node, in the two forms a successor will meet it.

## What is here

* `AlgebraicGeometry.hasAffineChartAt_tateInvNodeChartLocus_of_spfChartFamily`: from a formal-affine
  chart datum on `T_inv/⟨σ⟩` and a morphism out of *any* `Spf` whose image covers
  `Set.range (tateInvNodeChartAmbientHom …).base`, a chart at every point of
  `π '' tateInvSaturate D(x + y − 1)`.
* `AlgebraicGeometry.exists_formalScheme_of_spfChartFamily_tateInvNodeChart`: hence `T_inv/⟨σ⟩` is
  a formal scheme — **with no hypothesis on `I`**. Compare
  `AlgebraicGeometry.exists_formalScheme_of_exists_openImmersion_spf_of_isLeftRegular_base`
  (`FormalSchemes.TateInvNodeChartSpf`), which needs `I = (t)` with `IsLeftRegular t` because it has
  to put an `IsAdicRing` structure on the node chart ring. Nothing of the kind is needed here, and
  that is the point: the hypothesis is not a weaker one that happens to be checkable, it is a
  stronger one that already contains the answer.

## What this does *not* prove

* **It is not a refutation of `hnode`.** It says one route cannot be the *first* source of the
  chart; the chart may still exist and be produced some other way, and issue 1197 remains open.
* **It says nothing about the general colimit-target form.**
  `FormalSpectrum.ColimitTarget.spfHomOfFamily` asks only for
  `FormalSpectrum.IsThickeningColimitTarget (Y i)`, and the conclusion there is that the node image
  lies in an open with that *property* — not in a chart. See `FormalSchemes.SpfHomFamilyChart`'s
  module docstring; that is the question this row leaves behind.
* Nothing here weakens `LocallyRingedSpace.IsProperlyDiscontinuousOn`,
  `LocallyRingedSpace.IsFreeProperlyDiscontinuous` or
  `LocallyRingedSpace.freeActionQuotientFormalScheme`, and no `Tate*` statement is restated.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6 (10.6.10).
* [Deligne–Rapoport, *Les schémas de modules de courbes elliptiques*], II.1 — the Néron 1-gon.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)
variable {Q : LocallyRingedSpace.{u}}
variable {π : (tateChainInv R I q hq hI).toLocallyRingedSpace ⟶ Q}

section ChartFamily

variable {S : Type u} [CommRing S] [TopologicalSpace S] {J : Ideal S} [IsAdicRing J]
    (hJ : J.FG)
    (F : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (S ⧸ J ^ (n + 1))) ⟶ Q)
    (hF : ∀ n : ℕ, Spec.locallyRingedSpaceMap (stepRingHom J n) ≫ F (n + 1) = F n)
    {ι : Type u} (s : ι → S) [∀ i, IsAdicRing (awayCompletionIdeal J (s i))]
    (hcov : (⨆ i, basicOpen J (s i)) = ⊤)
    (V : ι → Opens Q.toTopCat)
    (hV : ∀ i, basicOpen J (s i) ≤ (Opens.map (commonBase J F)).obj (V i))
    {C : ι → Type u} [∀ i, CommRing (C i)] [∀ i, TopologicalSpace (C i)]
    (L : ∀ i, Ideal (C i)) [∀ i, IsAdicRing (L i)] (hL : ∀ i, (L i).FG)
    (eV : ∀ i, Q.restrict (V i).isOpenEmbedding ≅ locallyRingedSpaceObj (L i))
    (g : locallyRingedSpaceObj J ⟶ Q) (hg : ∀ n : ℕ, thickeningMap J n ≫ g = F n)

include hq hI hF hJ hcov hV hL eV hg in
/-- **A formal-affine chart datum on `T_inv/⟨σ⟩` charts the node domain, as soon as EGA I 10.6.10's
morphism reaches it.**

The hypotheses are exactly the input of `FormalSpectrum.ColimitTarget.spfHomOfFamily` at a
`Spf`-shaped chart datum — a compatible family out of the thickenings of *some* adic ring `(S, J)`,
a basic-open cover of `|Spf S|`, and for each piece an open `V i` of the quotient receiving its
image and identified with a formal spectrum — plus the range condition this row's residue is stated
with. **No covering hypothesis on `Q` is assumed**, which is the weaker input issue 1197 flagged as
unexamined.

The conclusion is `hnode`'s content on the uncharted set. So the route cannot produce the node
chart from anything weaker than a node chart: the `V i` are affine opens of the quotient, and one
of them contains each node image. -/
theorem hasAffineChartAt_tateInvNodeChartLocus_of_spfChartFamily
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π)
    (hrange : Set.range (tateInvNodeChartAmbientHom R I q hq hI (π := π)).base ⊆
      Set.range g.base) :
    ∀ z ∈ ⇑π.base '' tateInvSaturate R I q hq hI (tateInvNodeChartLocus R I q),
      LocallyRingedSpace.HasAffineChartAt Q z := by
  intro z hz
  refine hasAffineChartAt_of_spfChartFamily J F hF hJ s hcov V hV g hg L hL eV ?_
  exact hrange (by rwa [range_tateInvNodeChartAmbientHom R I q hq hI h])

include hq hI hF hJ hcov hV hL eV hg in
/-- **…hence `T_inv/⟨σ⟩` is a formal scheme, with no hypothesis on `I`.**

`AlgebraicGeometry.tateInvPeriodQuotientFormalSchemeOfNodeChartLocus` needs a chart at every point
of `π '' tateInvSaturate D(x + y − 1)`, and the previous theorem supplies all of them.

Read this against
`AlgebraicGeometry.exists_formalScheme_of_exists_openImmersion_spf_of_isLeftRegular_base`. That one
asks for a single open immersion out of `Spf` of one named ring and pays for it with `I = (t)` and
`IsLeftRegular t`, because the `IsAdicRing` structure on the node chart ring is only available
there. This one asks for the EGA I 10.6.10 datum and needs no hypothesis on `I` at all — not
because it is weaker, but because the datum it takes already contains a chart at every point in
question. -/
theorem exists_formalScheme_of_spfChartFamily_tateInvNodeChart
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π)
    (hrange : Set.range (tateInvNodeChartAmbientHom R I q hq hI (π := π)).base ⊆
      Set.range g.base) :
    ∃ X : FormalScheme.{u}, X.toLocallyRingedSpace = Q :=
  ⟨tateInvPeriodQuotientFormalSchemeOfNodeChartLocus R I q hq hI h
    (hasAffineChartAt_tateInvNodeChartLocus_of_spfChartFamily R I q hq hI hJ F hF s hcov V hV L hL
      eV g hg h hrange),
    rfl⟩

end ChartFamily

end AlgebraicGeometry
