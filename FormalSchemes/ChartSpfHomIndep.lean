import FormalSchemes.ThickeningChartSpfHom
import FormalSchemes.ThickeningHomExt

set_option linter.style.header false

/-!
# The chart morphism does not depend on the affine chart it was built from

`FormalSchemes/ThickeningChartSpfHom.lean` builds, from a compatible family
`f n : Spec (R ⧸ Iⁿ⁺¹) ⟶ X`, an open `U ⊆ X` identified with `Spec B`, and a basic open
`D(r) ⊆ |Spf R|` lying over `U`, a morphism `chartSpfHomAmbient : Spf R{1/r} ⟶ X`, and proves the
restriction rule

```lean
thickeningMap (awayCompletionIdeal I r) n ≫ chartSpfHomAmbient I f hf U r hr hI B e =
  (chartIsoLRS I r hI n).inv ≫ (Spec _).ofRestrict (chartOpen I r n).isOpenEmbedding ≫ f n
```

whose right-hand side mentions **neither `U` nor `e`**. That module says of this that "two charts
producing morphisms with this property agree wherever both are defined" — which is the right
reading, but it is an inference, and the input it needs was missing: two morphisms into a general
locally ringed space that agree on every thickening are equal. `FormalSchemes/ThickeningHomExt.lean`
supplies that (`hom_ext_thickeningMap_lrs`), and this file draws the conclusion, so that it is a
theorem rather than a remark.

## What is proved

`chartSpfHomAmbient_congr`: for a **fixed** `r`, the morphism `Spf R{1/r} ⟶ X` is the same
whichever affine chart `(U, B, e)` of `X` was used to build it. So the assignment
`r ↦ (Spf R{1/r} ⟶ X)` is well defined on the data the gluing step actually holds — a basic open
of `|Spf R|` together with *some* affine chart it lies over — and the choice of chart, which is
made by `exists_basicOpen_le_map_commonBase` and is not canonical, cannot be observed.

`chartSpfHomAmbient_uniq` is the same statement in the form a construction cites: anything
restricting correctly on the thickenings *is* `chartSpfHomAmbient`.

## What is not proved, and is the next row

Charts over **different** `r`. Comparing the morphisms attached to `r` and `r'` means comparing
morphisms out of two different formal spectra, `Spf R{1/r}` and `Spf R{1/r'}`, on the overlap
`D(r · r')` — which needs the restriction morphisms `Spf R{1/rr'} ⟶ Spf R{1/r}` that the tree does
not yet have. That, plus descent for morphisms of locally ringed spaces along an open cover, is
the gluing row. This file removes the part of that comparison which is *not* about overlaps.

## Main results

* `FormalSpectrum.chartSpfHomAmbient_congr`: independence of the affine chart.
* `FormalSpectrum.chartSpfHomAmbient_uniq`: the restriction rule characterises the morphism.
* `FormalSpectrum.hom_ext_thickeningMap_formalLine`: the general `hom_ext` at a witness whose
  target is not the `Spec` of a ring.
* `FormalSpectrum.chartSpfHomAmbient_congr_formalLine`: `chartSpfHomAmbient_congr` at the two
  affine charts of `Spec ℤ` that `ThickeningChartSpfHom.lean` carries over `r = 2`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6 (10.6.10).
* [The Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable {X : LocallyRingedSpace.{u}}
variable (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X)
    (hf : ∀ n : ℕ, Spec.locallyRingedSpaceMap (stepRingHom I n) ≫ f (n + 1) = f n)
    (r : R) (hI : I.FG) [IsAdicRing (awayCompletionIdeal I r)]

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The morphism `Spf R{1/r} ⟶ X` does not depend on the affine chart it was built from.** Both
sides restrict on the `n`-th thickening to `f n` read along the chart `D(r)`
(`thickeningMap_comp_chartSpfHomAmbient`), a statement in which the affine chart does not appear,
so `hom_ext_thickeningMap_lrs` identifies them.

This is what makes `chartSpfHomAmbient` a function of `r` alone, which is what the gluing step
needs: the affine chart is produced by `exists_basicOpen_le_map_commonBase` and is in no way
canonical. -/
theorem chartSpfHomAmbient_congr
    (U : Opens X.toTopCat) (hr : basicOpen I r ≤ (Opens.map (commonBase I f)).obj U)
    (B : Type u) [CommRing B]
    (e : X.restrict U.isOpenEmbedding ≅ Spec.locallyRingedSpaceObj (CommRingCat.of B))
    (U' : Opens X.toTopCat) (hr' : basicOpen I r ≤ (Opens.map (commonBase I f)).obj U')
    (B' : Type u) [CommRing B']
    (e' : X.restrict U'.isOpenEmbedding ≅ Spec.locallyRingedSpaceObj (CommRingCat.of B')) :
    chartSpfHomAmbient I f hf U r hr hI B e = chartSpfHomAmbient I f hf U' r hr' hI B' e' :=
  hom_ext_thickeningMap_lrs _ _ fun n => by
    rw [thickeningMap_comp_chartSpfHomAmbient, thickeningMap_comp_chartSpfHomAmbient]

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The restriction rule characterises the morphism.** Cite this to recognise a morphism built
by hand as `chartSpfHomAmbient`; note that the hypothesis, like the conclusion of
`thickeningMap_comp_chartSpfHomAmbient`, mentions neither the affine open nor the identification
of it with a `Spec`. -/
theorem chartSpfHomAmbient_uniq
    (U : Opens X.toTopCat) (hr : basicOpen I r ≤ (Opens.map (commonBase I f)).obj U)
    (B : Type u) [CommRing B]
    (e : X.restrict U.isOpenEmbedding ≅ Spec.locallyRingedSpaceObj (CommRingCat.of B))
    (g : locallyRingedSpaceObj (awayCompletionIdeal I r) ⟶ X)
    (hg : ∀ n : ℕ, thickeningMap (awayCompletionIdeal I r) n ≫ g =
      (chartIsoLRS I r hI n).inv ≫
        (Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1)))).ofRestrict
          (chartOpen I r n).isOpenEmbedding ≫ f n) :
    g = chartSpfHomAmbient I f hf U r hr hI B e :=
  hom_ext_thickeningMap_lrs _ _ fun n => by
    rw [hg, thickeningMap_comp_chartSpfHomAmbient]

section Witness

/-! ### The generality is real: a target that is not the `Spec` of a ring

`hom_ext_thickeningMap` (`IndSchemeThickening.lean`) already covers affine targets, so the only
thing to check about `hom_ext_thickeningMap_lrs` is that it says more. It does: the witness below
takes the target to be `Spf ℤ⟦X⟧` itself, which is not spelled as `Spec` of a ring anywhere on this
tree — the `fail_if_success` in the proof records that the affine lemma does not apply to it, so
the demonstration is checked rather than asserted.

The source is `Spf ℤ⟦X⟧{1/2}`, the away completion at `r = 2` of `FormalLineWitness.lean`'s formal
affine line. That is the ring for which `ThickeningChartAffine.lean` proves the chart `D(2)` is
neither `⊥` nor `⊤` at every level of the tower (`chartOpen_formalLine_ne_bot`,
`chartOpen_formalLine_ne_top`), so the tower of thickenings being quantified over is not the
constant one. Those two lemmas say nonempty and proper, and that is all they are cited for here;
`|Spf ℤ⟦X⟧{1/2}|` is in fact `D(2) ⊆ Spec ℤ` and so has infinitely many points, but nothing on the
tree states that and this section does not need it. The `2`-adic witness of `TwoAdicWitness.lean`
would prove nothing here: `|Spf ℤ^|` is a one-point space (`TwoAdicDegeneracy.lean`).

`chartSpfHomAmbient_congr` needs more than satisfiable hypotheses to be exercised: it needs *two
different* affine charts over one `r`, or it compares a morphism with itself.
`ThickeningChartSpfHom.lean` carries exactly such a pair, over `X = Spec ℤ` with the one family
and the one `r = 2` — `U = ⊤` with `B = ℤ`, and `U = D(2)` with `B = ℤ[1/2]`.
`chartSpfHomAmbient_congr_formalLine` identifies the two morphisms they produce. Nothing in that
identification is definitional: the two are built from a proper open and an improper one, from
two non-isomorphic rings, and from isomorphisms assembled in different ways
(`LocallyRingedSpace.restrictTopIso` against `basicOpenIsoSpecAway` pushed through
`Scheme.forgetToLocallyRingedSpace`).

What remains genuinely out of reach is a **non-affine** `X` carrying a compatible family, which is
the gap `ThickeningChartSpfHom.lean` documents. It does not bear on non-vacuity of anything proved
here — the construction never looks at `X` outside `U` — but it does mean no witness on this tree
exhibits the *covering* situation the gluing row will face, where the charts come from different
affine opens of an `X` that is not itself affine.
-/

open Polynomial

attribute [local instance] isAdicRing_formalLineIdeal

-- `ThickeningChartSpfHom.lean` names this; it is `local` there, so it has to be re-activated
-- rather than re-derived.
attribute [local instance] isAdicRing_awayCompletionIdeal_formalLine

/-- **The general `hom_ext` at a non-affine target.** Morphisms `Spf ℤ⟦X⟧{1/2} ⟶ Spf ℤ⟦X⟧` are
determined by their restrictions to the infinitesimal thickenings of `ℤ⟦X⟧{1/2}`. -/
theorem hom_ext_thickeningMap_formalLine
    (g₁ g₂ : locallyRingedSpaceObj (awayCompletionIdeal formalLineIdeal 2) ⟶
      locallyRingedSpaceObj formalLineIdeal)
    (h : ∀ n : ℕ, thickeningMap (awayCompletionIdeal formalLineIdeal 2) n ≫ g₁ =
      thickeningMap (awayCompletionIdeal formalLineIdeal 2) n ≫ g₂) :
    g₁ = g₂ := by
  -- the affine-target lemma cannot be applied: the target is not of the form `Spec B`
  fail_if_success exact hom_ext_thickeningMap _ _ g₁ g₂ h
  exact hom_ext_thickeningMap_lrs g₁ g₂ h

/-- **`chartSpfHomAmbient_congr` at two genuinely different charts.** The morphism
`Spf ℤ⟦X⟧{1/2} ⟶ Spec ℤ` built over the affine open `⊤ = Spec ℤ` and the one built over the proper
affine open `D(2) = Spec ℤ[1/2]` are the same morphism.

The two sides share only the family and `r = 2`: the opens are `⊤` and a proper one
(`openTwo_ne_top`), the rings are `ℤ` and `ℤ[1/2]`, and the affine identifications are
`LocallyRingedSpace.restrictTopIso` and `basicOpenIsoSpecAway` read through
`Scheme.forgetToLocallyRingedSpace`. So this is not `rfl`, and the equality is the theorem's. -/
theorem chartSpfHomAmbient_congr_formalLine :
    chartSpfHomAmbient formalLineIdeal witnessFamily.1 witnessFamily.2 ⊤ 2 witness_hr
        (polyXIdeal_fg.map _) ℤ witnessTarget.restrictTopIso =
      chartSpfHomAmbient formalLineIdeal witnessFamily.1 witnessFamily.2 openTwo 2
        witness_hr_two (polyXIdeal_fg.map _) (Localization.Away (2 : ℤ)) openTwoIsoSpecLRS :=
  chartSpfHomAmbient_congr _ _ _ 2 (polyXIdeal_fg.map _) _ _ _ _ _ _ _ _

end Witness

end FormalSpectrum

end
