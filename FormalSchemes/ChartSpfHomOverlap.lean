import FormalSchemes.ThickeningChartSpfHom
import FormalSchemes.ThickeningHomExt
import FormalSchemes.ThickeningMapNatural
import FormalSchemes.BasicOpenChartOverlapLegs

set_option linter.style.header false

/-!
# The chart morphisms agree on the overlap `D(r·s)` (EGA I, 10.6.10)

Umbrella 59 runs *cover `X` by affines → pull the cover back to `|Spf R|` → refine by basic opens
`D(r)` → run the affine case on each chart → **glue**.
`FormalSchemes/ThickeningChartSpfHom.lean` (issue 1062) is the fourth step: from a compatible family
`f n : Spec (R ⧸ Iⁿ⁺¹) ⟶ X` and a chart `D(r)` lying over an affine open of `X` it builds
`chartSpfHomAmbient : Spf R{1/r} ⟶ X`. `FormalSchemes/ChartSpfHomIndep.lean` (issue 1064) removed
the dependence on the *affine chart* `(U, B, e)`, so that morphism is a function of `r` alone.

This file supplies the comparison that is actually about **overlaps**, and it is the last one before
descent: the morphisms attached to `r` and to `s` agree on `D(r·s)`.

```
Spf R{1/(r·s)} ⟶ Spf R{1/r} ⟶ X   =   Spf R{1/(r·s)} ⟶ Spf R{1/s} ⟶ X
```

## What had to be built

The two restriction morphisms already exist: `basicOpenChartFurtherLeft` and
`basicOpenChartFurtherRight` (`BasicOpenChartOverlapLegs.lean`) are `Spf` of the further
localizations `A{1/r} →+* A{1/(r·s)}` and `A{1/s} →+* A{1/(r·s)}`. What was missing is that
`chartSpfHomAmbient` is characterised by its restrictions to *thickenings*, while the legs are `Spf`
of *ring maps*, and nothing related the two. Two bridges close the gap:

* `FormalSchemes/ThickeningMapNatural.lean`: `thickeningMap` is natural in the adic ring, so
  restricting a leg to a thickening is `Spec` of the induced map of thickenings followed by a
  thickening morphism.
* `chartRingMap_eq_levelRingHom` (`ThickeningChartAffine.lean`): the ring map
  `R ⧸ Iⁿ⁺¹ ⟶ R{1/r} ⧸ (I·R{1/r})ⁿ⁺¹` through which that file reads the chart inclusion **is** the
  level-`n` descent of the structural map `R → R{1/r}`. That is the ring-theoretic core of this
  file's argument, and everything else about the three localizations `r`, `s`, `r·s` follows from
  it by `levelRingHom_comp` plus `awayCompletionMulHomLeft_comp_awayCompletionHom`, which is
  already on the tree.

With those, the proof is three rewrites: `hom_ext_thickeningMap_lrs` reduces to the thickenings,
naturality moves each leg across, `thickeningMap_comp_chartSpfHomAmbient` deletes the affine chart,
and what is left is `chartIsoLRS_inv_comp_ofRestrict_further_left`/`_right` — the statement that the
chart of `D(r·s)` sits inside the chart of `D(r)` and of `D(s)` compatibly with their embeddings
into `Spec (R ⧸ Iⁿ⁺¹)`. Both sides become the *same* morphism, `f n` read along the chart of
`D(r·s)`, so no `chartIsoLRS` at three different elements ever has to be reconciled by hand.

## What is still missing for the gluing

Only descent: a family of morphisms out of an open cover of `|Spf R|` agreeing on overlaps comes
from a unique morphism out of `Spf R`. That needs the cover statement of
`ThickeningBasicOpenRefinement.lean` and gluing for morphisms of locally ringed spaces, and it is a
separate row. Pairwise agreement — this file — is what such a descent argument consumes; no cocycle
condition on triple overlaps is needed for gluing *morphisms*, as opposed to gluing spaces.

## Main results

* `FormalSpectrum.chartRingMap_comp_levelRingHom_left` and `…_right`: the chart ring maps at `r`
  and at `s` differ from the one at `r·s` by the corresponding leg.
* `FormalSpectrum.chartIsoLRS_inv_comp_ofRestrict_further_left` and `…_right`: the chart of
  `D(r·s)` maps to the charts of `D(r)` and `D(s)` over `Spec (R ⧸ Iⁿ⁺¹)`.
* `FormalSpectrum.chartSpfHomAmbient_overlap`: **the theorem.**
* `FormalSpectrum.chartSpfHomAmbient_overlap_formalLine`: the witness, at `ℤ⟦X⟧` with `r = 2`,
  `s = 3` — the two elements whose basic opens `FormalLineWitness.lean` proves *cover* `|Spf ℤ⟦X⟧|`
  (`iSup_twoChart`), each proper (`twoChart_ne_top`). See the witness section for what remains
  degenerate.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6 (10.6.10), §10.8.
* [The Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace FormalSpectrum

/-!
### The chart ring maps at `r`, `s` and `r·s`

`chartRingMap I r hI n` is built in `ThickeningChartAffine.lean` as the structure map of a
localization followed by the inverse of issue 1043's identification, which is not a shape any
functoriality lemma can be applied to. That same file's `chartRingMap_eq_levelRingHom` says it is
`levelRingHom` of the structural map `R → R{1/r}`, and once that is known the three-element
bookkeeping below is `levelRingHom_comp`.
-/

section ChartRingMap

variable {R : Type u} [CommRing R] (I : Ideal R) (r s : R)

/-- **The chart ring maps at `r` and at `r·s` differ by the left leg**, on the `n`-th thickenings.
Both sides are the level-`n` descent of `R → R{1/(r·s)}`, because
`awayCompletionMulHomLeft_comp_awayCompletionHom` says the two structural maps compose to it. -/
theorem chartRingMap_comp_levelRingHom_left (hI : I.FG) (n : ℕ) :
    chartRingMap I r hI n ≫ CommRingCat.ofHom (levelRingHom (awayCompletionIdeal I r)
        (awayCompletionIdeal I (r * s)) (awayCompletionMulHomLeft I r s hI)
        (le_comap_awayCompletionMulHomLeft I r s hI) n) =
      chartRingMap I (r * s) hI n := by
  rw [chartRingMap_eq_levelRingHom, chartRingMap_eq_levelRingHom, ← CommRingCat.ofHom_comp,
    ← levelRingHom_comp I (awayCompletionIdeal I r) (awayCompletionIdeal I (r * s))
      (awayCompletionHom I r) (awayCompletionMulHomLeft I r s hI)
      (le_comap_awayCompletionHom I r) (le_comap_awayCompletionMulHomLeft I r s hI)
      (le_comap_comp _ _ (le_comap_awayCompletionHom I r)
        (le_comap_awayCompletionMulHomLeft I r s hI)) n]
  exact congrArg _
    (levelRingHom_congr I (awayCompletionIdeal I (r * s)) _ _ _ _
      (awayCompletionMulHomLeft_comp_awayCompletionHom I r s hI) n)

/-- **The chart ring maps at `s` and at `r·s` differ by the right leg.** -/
theorem chartRingMap_comp_levelRingHom_right (hI : I.FG) (n : ℕ) :
    chartRingMap I s hI n ≫ CommRingCat.ofHom (levelRingHom (awayCompletionIdeal I s)
        (awayCompletionIdeal I (r * s)) (awayCompletionMulHomRight I r s hI)
        (le_comap_awayCompletionMulHomRight I r s hI) n) =
      chartRingMap I (r * s) hI n := by
  rw [chartRingMap_eq_levelRingHom, chartRingMap_eq_levelRingHom, ← CommRingCat.ofHom_comp,
    ← levelRingHom_comp I (awayCompletionIdeal I s) (awayCompletionIdeal I (r * s))
      (awayCompletionHom I s) (awayCompletionMulHomRight I r s hI)
      (le_comap_awayCompletionHom I s) (le_comap_awayCompletionMulHomRight I r s hI)
      (le_comap_comp _ _ (le_comap_awayCompletionHom I s)
        (le_comap_awayCompletionMulHomRight I r s hI)) n]
  exact congrArg _
    (levelRingHom_congr I (awayCompletionIdeal I (r * s)) _ _ _ _
      (awayCompletionMulHomRight_comp_awayCompletionHom I r s hI) n)

/-!
### The chart embeddings into the `n`-th thickening

`thickeningMap_comp_chartSpfHomAmbient` states its right-hand side as
`(chartIsoLRS I r hI n).inv ≫ (Spec _).ofRestrict (chartOpen I r n).isOpenEmbedding ≫ f n`, so that
composite — the chart of `D(r)`, identified with the `n`-th thickening of `R{1/r}` and embedded into
the `n`-th thickening of `R` — is what the overlap comparison has to move around. It is `Spec` of
`chartRingMap`, by `chartIsoLRS_inv_comp_ofRestrict` (`ThickeningChartAffine.lean`), which is the
whole reason the previous section exists.
-/

/-- **The left leg on the `n`-th thickening**: the chart of `D(r·s)`, pushed into the chart of
`D(r)` by `Spec` of the map of thickenings induced by `A{1/r} → A{1/(r·s)}`, embeds into
`Spec (R ⧸ Iⁿ⁺¹)` as the chart of `D(r·s)` does. So the affine chart at `r` is invisible after the
comparison, which is what makes the overlap theorem two rewrites. -/
@[reassoc]
theorem chartIsoLRS_inv_comp_ofRestrict_further_left (hI : I.FG) (n : ℕ) :
    Spec.locallyRingedSpaceMap (CommRingCat.ofHom (levelRingHom (awayCompletionIdeal I r)
          (awayCompletionIdeal I (r * s)) (awayCompletionMulHomLeft I r s hI)
          (le_comap_awayCompletionMulHomLeft I r s hI) n)) ≫
        (chartIsoLRS I r hI n).inv ≫
          (Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1)))).ofRestrict
            (chartOpen I r n).isOpenEmbedding =
      (chartIsoLRS I (r * s) hI n).inv ≫
        (Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1)))).ofRestrict
          (chartOpen I (r * s) n).isOpenEmbedding := by
  rw [chartIsoLRS_inv_comp_ofRestrict, chartIsoLRS_inv_comp_ofRestrict,
    ← Spec.locallyRingedSpaceMap_comp, chartRingMap_comp_levelRingHom_left]

/-- **The right leg on the `n`-th thickening**, the companion of
`chartIsoLRS_inv_comp_ofRestrict_further_left`. -/
@[reassoc]
theorem chartIsoLRS_inv_comp_ofRestrict_further_right (hI : I.FG) (n : ℕ) :
    Spec.locallyRingedSpaceMap (CommRingCat.ofHom (levelRingHom (awayCompletionIdeal I s)
          (awayCompletionIdeal I (r * s)) (awayCompletionMulHomRight I r s hI)
          (le_comap_awayCompletionMulHomRight I r s hI) n)) ≫
        (chartIsoLRS I s hI n).inv ≫
          (Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1)))).ofRestrict
            (chartOpen I s n).isOpenEmbedding =
      (chartIsoLRS I (r * s) hI n).inv ≫
        (Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1)))).ofRestrict
          (chartOpen I (r * s) n).isOpenEmbedding := by
  rw [chartIsoLRS_inv_comp_ofRestrict, chartIsoLRS_inv_comp_ofRestrict,
    ← Spec.locallyRingedSpaceMap_comp, chartRingMap_comp_levelRingHom_right]

end ChartRingMap

/-!
### The overlap agreement
-/

section Overlap

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable {X : LocallyRingedSpace.{u}}
variable (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X)
    (hf : ∀ n : ℕ, Spec.locallyRingedSpaceMap (stepRingHom I n) ≫ f (n + 1) = f n)
    (r s : R) (hI : I.FG)
    [IsAdicRing (awayCompletionIdeal I r)] [IsAdicRing (awayCompletionIdeal I s)]
    (U : Opens X.toTopCat) (hr : basicOpen I r ≤ (Opens.map (commonBase I f)).obj U)
    (B : Type u) [CommRing B]
    (e : X.restrict U.isOpenEmbedding ≅ Spec.locallyRingedSpaceObj (CommRingCat.of B))
    (U' : Opens X.toTopCat) (hr' : basicOpen I s ≤ (Opens.map (commonBase I f)).obj U')
    (B' : Type u) [CommRing B']
    (e' : X.restrict U'.isOpenEmbedding ≅ Spec.locallyRingedSpaceObj (CommRingCat.of B'))

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The chart morphisms agree on the overlap** (EGA I, 10.6.10): the morphism `Spf R{1/r} ⟶ X`
and the morphism `Spf R{1/s} ⟶ X` built from the same compatible family become equal after
restriction along the two legs of `D(r·s) = D(r) ∩ D(s)`.

Neither the affine charts `(U, B, e)` and `(U', B', e')` nor even the opens `U`, `U'` are assumed
related: they are eliminated before the comparison begins, by
`thickeningMap_comp_chartSpfHomAmbient`. What is compared is the input family `f` read along the
charts of `D(r)` and of `D(s)`, and both readings restrict to the chart of `D(r·s)`.

This is the pairwise agreement a descent argument consumes; the descent itself, which needs a cover
of `|Spf R|` by the `D(r)`, is the remaining step of umbrella 59. -/
theorem chartSpfHomAmbient_overlap :
    basicOpenChartFurtherLeft I r s hI ≫ chartSpfHomAmbient I f hf U r hr hI B e =
      basicOpenChartFurtherRight I r s hI ≫ chartSpfHomAmbient I f hf U' s hr' hI B' e' := by
  refine hom_ext_thickeningMap_lrs _ _ fun n => ?_
  rw [basicOpenChartFurtherLeft, basicOpenChartFurtherRight,
    thickeningMap_comp_locallyRingedSpaceMap_assoc,
    thickeningMap_comp_locallyRingedSpaceMap_assoc,
    thickeningMap_comp_chartSpfHomAmbient, thickeningMap_comp_chartSpfHomAmbient,
    chartIsoLRS_inv_comp_ofRestrict_further_left_assoc,
    chartIsoLRS_inv_comp_ofRestrict_further_right_assoc]

end Overlap

/-!
### Non-vacuity

Four degeneracies could make the theorem above say nothing, and this section removes all four.

* `I = ⊥`, where every thickening is `Spec R` and the tower is constant. Excluded by taking
  `FormalLineWitness.lean`'s formal affine line `ℤ⟦X⟧`, whose `|Spf|` is `Spec ℤ`.
* `r = s`, where the two legs coincide and the statement compares a morphism with itself. Excluded
  by `r = 2`, `s = 3`; and these are not merely distinct, they are the two elements
  `FormalLineWitness.lean` proves *cover* `|Spf ℤ⟦X⟧|` (`iSup_twoChart`), so this witness exercises
  the theorem in the situation the gluing row will actually face.
* A degenerate chart. `D(2)`, `D(3)` and their overlap `D(2·3)` are each neither `⊥` nor `⊤` — and
  so are the corresponding charts of *every* thickening, which is what the theorem quantifies over
  (`chartOpen_formalLine_three_ne_top` and the four companions below, joined by the landed
  `chartOpen_formalLine_ne_top`/`_ne_bot` at `r = 2`). In particular the source
  `Spf ℤ⟦X⟧{1/(2·3)}` is not the empty formal scheme.
* `U = U' = ⊤`, where the affineness hypothesis becomes a hypothesis on all of `X` and
  `chartRestrict` restricts nothing. Excluded on **both** sides: `U = D(2)` and `U' = D(3)` are
  proper nonempty affine opens of `Spec ℤ`, with different coordinate rings `ℤ[1/2]` and `ℤ[1/3]`.
  This is the one `ThickeningChartSpfHom.lean` could only remove on one side, because until this
  file there was no second `r` in play.

What is **not** removed, and remains the one genuinely open gap of this cluster: `X` is still
affine. No non-affine `X` carrying a compatible family exists on the tree. It does not affect
non-vacuity of anything proved here — the construction never looks at `X` outside `U ∪ U'` — but a
witness in which the two affine opens come from an `X` that is not itself affine is still absent,
and that is what a full gluing witness will need.
-/

section Witness

open Polynomial

attribute [local instance] isAdicRing_formalLineIdeal
attribute [local instance] isAdicRing_awayCompletionIdeal_formalLine

/-- `ℤ⟦X⟧{1/3}` is a complete adic ring. The companion of the landed
`isAdicRing_awayCompletionIdeal_formalLine` at the second element; local for the same reason, that
`I.FG` is not synthesizable in general. -/
theorem isAdicRing_awayCompletionIdeal_formalLine_three :
    IsAdicRing (awayCompletionIdeal formalLineIdeal 3) :=
  isAdicRing_awayCompletionIdeal _ _ (polyXIdeal_fg.map _)

attribute [local instance] isAdicRing_awayCompletionIdeal_formalLine_three

/-! #### The second chart of `|Spf ℤ⟦X⟧|`, and the overlap, are non-degenerate -/

/-- `D(3) ⊆ |Spf ℤ⟦X⟧|` is a **proper** open. This is `twoChart_ne_top` at the second chart; it is
the statement `|Spf ℤ^|` cannot supply, since that space is a point. -/
theorem basicOpen_formalLine_three_ne_top : basicOpen formalLineIdeal 3 ≠ ⊤ := by
  have h := twoChart_ne_top false
  rwa [twoChart, if_neg (by simp)] at h

/-- …and a **nonempty** one: the generic point of `Spec ℤ` is in it. -/
theorem basicOpen_formalLine_three_ne_bot : basicOpen formalLineIdeal 3 ≠ ⊥ := by
  intro h
  have hmem : ofPrimeInt ⟨⊥, Ideal.isPrime_bot⟩ ∈ basicOpen formalLineIdeal 3 := by
    rw [mem_basicOpen_ofPrimeInt, map_ofNat, map_ofNat]
    simp
  rw [h] at hmem
  exact hmem.elim

/-- **The overlap `D(2·3) ⊆ |Spf ℤ⟦X⟧|` is a proper open**: it is contained in `D(3)`, by
`basicOpen_mul`. So the source of the two morphisms being compared is not all of `Spf ℤ⟦X⟧`. -/
theorem basicOpen_formalLine_overlap_ne_top :
    basicOpen formalLineIdeal ((2 : AdicCompletion polyXIdeal ℤ[X]) * 3) ≠ ⊤ := by
  rw [basicOpen_mul]
  intro h
  exact basicOpen_formalLine_three_ne_top (eq_top_iff.mpr (h.ge.trans inf_le_right))

/-- **…and a nonempty one**: the generic point lies in both `D(2)` and `D(3)`. So the two charts
genuinely overlap and the agreement is not an agreement over the empty formal scheme. -/
theorem basicOpen_formalLine_overlap_ne_bot :
    basicOpen formalLineIdeal ((2 : AdicCompletion polyXIdeal ℤ[X]) * 3) ≠ ⊥ := by
  intro h
  have hmem : ofPrimeInt ⟨⊥, Ideal.isPrime_bot⟩ ∈
      basicOpen formalLineIdeal ((2 : AdicCompletion polyXIdeal ℤ[X]) * 3) := by
    rw [mem_basicOpen_ofPrimeInt, map_mul, map_mul, map_ofNat, map_ofNat, map_ofNat, map_ofNat]
    simp
  rw [h] at hmem
  exact hmem.elim

/-- **The chart of every thickening over `D(3)` is a proper open**, the companion at the second
element of the landed `chartOpen_formalLine_ne_top`. -/
theorem chartOpen_formalLine_three_ne_top (n : ℕ) : chartOpen formalLineIdeal 3 n ≠ ⊤ :=
  chartOpen_ne_top _ _ n basicOpen_formalLine_three_ne_top

/-- …and a nonempty one. -/
theorem chartOpen_formalLine_three_ne_bot (n : ℕ) : chartOpen formalLineIdeal 3 n ≠ ⊥ :=
  chartOpen_ne_bot _ _ n basicOpen_formalLine_three_ne_bot

/-- **The chart of every thickening over the overlap `D(2·3)` is a proper open.** This is the one
that matters for the theorem below: it is the chart of the *source* of both morphisms being
compared, at every level of the tower being quantified over. -/
theorem chartOpen_formalLine_overlap_ne_top (n : ℕ) :
    chartOpen formalLineIdeal ((2 : AdicCompletion polyXIdeal ℤ[X]) * 3) n ≠ ⊤ :=
  chartOpen_ne_top _ _ n basicOpen_formalLine_overlap_ne_top

/-- …and a nonempty one. -/
theorem chartOpen_formalLine_overlap_ne_bot (n : ℕ) :
    chartOpen formalLineIdeal ((2 : AdicCompletion polyXIdeal ℤ[X]) * 3) n ≠ ⊥ :=
  chartOpen_ne_bot _ _ n basicOpen_formalLine_overlap_ne_bot

/-! #### A second proper affine open of the target

`ThickeningChartSpfHom.lean` supplies `openTwo = D(2) ⊆ Spec ℤ` with its affine identification, for
the chart at `r = 2`. The chart at `s = 3` needs its own, and it is the same construction one
element over. -/

/-- `D(3) ⊆ Spec ℤ`. The `(Spec _).Opens` ascription is the one `openTwo` carries and for the same
reason: without it `basicOpenIsoSpecAway` has nothing to coerce to a `Scheme`. -/
abbrev openThree : (Spec (CommRingCat.of ℤ)).Opens := PrimeSpectrum.basicOpen (3 : ℤ)

/-- `D(3) ⊆ Spec ℤ` is a **proper** open: any prime containing `3` misses it, and
`exists_prime_mem` produces one. -/
theorem openThree_ne_top : openThree ≠ ⊤ := by
  intro h
  obtain ⟨p, hp⟩ := exists_prime_mem 3 (by rw [Int.isUnit_iff]; decide)
  have hmem : p ∈ openThree := by rw [h]; trivial
  exact hmem hp

/-- …and a **nonempty** one: the generic point is in it. -/
theorem openThree_ne_bot : openThree ≠ ⊥ := by
  intro h
  have hmem : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℤ) ∈ openThree := by
    change (3 : ℤ) ∉ (⊥ : Ideal ℤ)
    simp
  rw [h] at hmem
  exact hmem.elim

/-- The level-`0` containment behind the refinement hypothesis at `s = 3`: the chart `D(3̄)` of the
level-`0` thickening lands in `(f 0) ⁻¹ D(3)`, because `f 0` is `Spec` of a ring map carrying `3`
to `3`. The companion of `ThickeningChartSpfHom.lean`'s `chartOpen_le_thickeningChart_two`. -/
private theorem chartOpen_le_thickeningChart_three :
    chartOpen formalLineIdeal 3 0 ≤ thickeningChart formalLineIdeal witnessFamily.1 openThree 0 :=
  fun y hy => by
    have hy' : Ideal.Quotient.mk (formalLineIdeal ^ (0 + 1))
        (3 : AdicCompletion polyXIdeal ℤ[X]) ∉
      (y : PrimeSpectrum (AdicCompletion polyXIdeal ℤ[X] ⧸ formalLineIdeal ^ (0 + 1))).asIdeal := hy
    change ((Ideal.Quotient.mk (formalLineIdeal ^ (0 + 1))).comp
        (Int.castRingHom (AdicCompletion polyXIdeal ℤ[X]))) 3 ∉
      (y : PrimeSpectrum (AdicCompletion polyXIdeal ℤ[X] ⧸ formalLineIdeal ^ (0 + 1))).asIdeal
    rwa [RingHom.comp_apply, map_ofNat]

/-- **The refinement hypothesis at `s = 3`**: `D(3) ⊆ |Spf ℤ⟦X⟧|` lands inside the preimage of
`D(3) ⊆ Spec ℤ` under the common base map. The companion of `witness_hr_two`. -/
theorem witness_hr_three :
    basicOpen formalLineIdeal 3 ≤
      (Opens.map (commonBase formalLineIdeal witnessFamily.1)).obj openThree := by
  rw [map_commonBase_obj_eq_thickeningChart formalLineIdeal witnessFamily.1
    witnessFamily.2 0 openThree]
  intro x hx
  have h0 : (thickeningTopIso formalLineIdeal 0).hom x ∈
      thickeningOpen formalLineIdeal 0 (basicOpen formalLineIdeal 3) := by
    change (thickeningTopIso formalLineIdeal 0).inv
      ((thickeningTopIso formalLineIdeal 0).hom x) ∈ basicOpen formalLineIdeal 3
    rwa [inv_hom_apply]
  rw [thickeningOpen_basicOpen] at h0
  exact chartOpen_le_thickeningChart_three h0

/-- `D(3) ⊆ Spec ℤ` is affine, namely `Spec ℤ[1/3]`. -/
private def openThreeIsoSpec :
    openThree.toScheme ≅ Spec (CommRingCat.of (Localization.Away (3 : ℤ))) :=
  basicOpenIsoSpecAway _

/-- …and the same isomorphism in `LocallyRingedSpace`, which is the shape the affine data `e` is
taken in. -/
def openThreeIsoSpecLRS :
    witnessTarget.restrict openThree.isOpenEmbedding ≅
      Spec.locallyRingedSpaceObj (CommRingCat.of (Localization.Away (3 : ℤ))) :=
  Scheme.forgetToLocallyRingedSpace.mapIso openThreeIsoSpec

/-- **The overlap agreement, at two genuinely different charts over two genuinely different
elements.** The morphism `Spf ℤ⟦X⟧{1/2} ⟶ Spec ℤ` built over the affine open `D(2) = Spec ℤ[1/2]`
and the morphism `Spf ℤ⟦X⟧{1/3} ⟶ Spec ℤ` built over `D(3) = Spec ℤ[1/3]` agree after restriction
to `Spf ℤ⟦X⟧{1/(2·3)}`.

Nothing here is shared between the two sides except the family: the elements are `2` and `3`, the
opens of the source are `D(2)` and `D(3)` (which *cover* `|Spf ℤ⟦X⟧|`, `iSup_twoChart`, and are
each proper, `twoChart_ne_top`), the opens of the target are `D(2)` and `D(3)` in `Spec ℤ` (each
proper and nonempty, `openTwo_ne_top`/`openThree_ne_top` and their `_ne_bot` companions), and the
coordinate rings are `ℤ[1/2]` and `ℤ[1/3]`. The source `Spf ℤ⟦X⟧{1/(2·3)}` is itself
non-degenerate at every level (`chartOpen_formalLine_overlap_ne_bot`,
`chartOpen_formalLine_overlap_ne_top`). -/
theorem chartSpfHomAmbient_overlap_formalLine :
    basicOpenChartFurtherLeft formalLineIdeal 2 3 (polyXIdeal_fg.map _) ≫
        chartSpfHomAmbient formalLineIdeal witnessFamily.1 witnessFamily.2 openTwo 2
          witness_hr_two (polyXIdeal_fg.map _) (Localization.Away (2 : ℤ)) openTwoIsoSpecLRS =
      basicOpenChartFurtherRight formalLineIdeal 2 3 (polyXIdeal_fg.map _) ≫
        chartSpfHomAmbient formalLineIdeal witnessFamily.1 witnessFamily.2 openThree 3
          witness_hr_three (polyXIdeal_fg.map _) (Localization.Away (3 : ℤ))
          openThreeIsoSpecLRS :=
  chartSpfHomAmbient_overlap _ _ _ 2 3 _ _ _ _ _ _ _ _ _

end Witness

end FormalSpectrum
