import FormalSchemes.AdicExtend
import FormalSchemes.AwayCompletionRestrict
import FormalSchemes.BasicOpenChartOverlapLegs
import FormalSchemes.BasicOpenRestriction

set_option linter.style.header false

/-!
# `R{1/f} →+* R{1/g}` is determined by its square over `R`, once it is continuous

`FormalSpectrum.awayCompletionRestrict` (`FormalSchemes.AwayCompletionRestrict`) is the canonical
`R{1/f} →+* R{1/g}` attached to an inclusion of basic opens `D(g) ⊆ D(f)` of `Spf (R, I)`. That file
proves it commutes with the structure maps from `R` and carries the ideal of definition of `R{1/f}`
onto that of `R{1/g}`, and then says that those two facts do not *determine* it:

> Two ring maps `R{1/f} → R{1/g}` agreeing on the image of `R` agree on the image of
> `Localization.Away f` … but that image is only *dense*, so uniqueness needs a continuity
> hypothesis that nothing here supplies.

The first clause is right and the second is not. The continuity hypothesis is supplied by
`AdicCompletion.hom_ext_of_continuous` (`FormalSchemes.AdicExtend`), which says that two ring maps
out of an adic completion into a complete target that both carry the filtration into the filtration
and that agree on the dense subring are equal; and the filtration condition it asks for is, for
`awayCompletionRestrict`, exactly `FormalSpectrum.le_comap_awayCompletionRestrict`, which that file
proves. So the map *is* determined, and this file records that.

The consequences are the two follow-ups that file listed as out of scope. Neither needs a
computation through `RingSplit.adicAwayUnitEquiv'`:

* restriction along `D(f) ≤ D(f)` is the identity, and restriction composes along a chain
  `D(h) ≤ D(g) ≤ D(f)`;
* every `AdicCompletion.mapCompletion` of a map of localizations **under `R`** *is* the canonical
  restriction — in particular `FormalSpectrum.awayCompletionMulHomLeft`
  (`FormalSchemes.BasicOpenChartOverlapLegs`) is, at the nested inclusion `D(f * g) ≤ D(f)`.

## Main results

* `FormalSpectrum.awayCompletion_hom_ext`: **the rigidity principle.** For `I` finitely generated,
  two ring maps `R{1/f} →+* R{1/g}` that each carry `awayCompletionIdeal I f` into
  `awayCompletionIdeal I g` and that agree after `FormalSpectrum.awayCompletionHom I f` are equal.
* `FormalSpectrum.awayCompletionRestrict_unique`: `awayCompletionRestrict` is the unique such map.
* `FormalSpectrum.awayCompletionRestrict_self`, `FormalSpectrum.awayCompletionRestrict_comp`: the
  identity and the chain law.
* `FormalSpectrum.awayCompletionRestrict_eq_mapCompletion`: a completed localization map under `R`
  is the canonical restriction.
* `FormalSpectrum.awayCompletionRestrict_eq_awayCompletionMulHomLeft`: the nested instance.
* `FormalSpectrum.basicOpenRes_eq_awayCompletionRestrict_of_le_comap`: **conditional.** If the
  structure-sheaf restriction is continuous in the same sense, it is `awayCompletionRestrict`. The
  hypothesis is discharged, and the identification stated unconditionally, in
  `FormalSchemes.BasicOpenRestrictionIdentification`.

## What is *not* proved here

**The hypothesis of the last item is not discharged here — but it is not an obstruction, and an
earlier version of this paragraph said it was.** It said that discharging it "is a statement about
the sections identification rather than about these two ring maps". That is false. The ideal of
definition of `R{1/f}` is the extension of `I` along `FormalSpectrum.awayCompletionHom I f`
(`FormalSpectrum.map_awayCompletionHom`, `FormalSchemes.BasicOpenChart`), so *any* ring map
`R{1/f} →+* R{1/g}` under `R` carries it onto the ideal of definition of `R{1/g}` by `Ideal.map_map`
alone — nothing about `FormalSpectrum.sectionsBasicOpenEquiv` enters. Downstream,
`FormalSpectrum.le_comap_basicOpenRes` (`FormalSchemes.BasicOpenRestrictionIdentification`)
discharges the hypothesis in two lines and
`FormalSpectrum.basicOpenRes_eq_awayCompletionRestrict` states the unconditional identification
that two threads on this tree were asking for.

So `FormalSpectrum.awayCompletionRestrict_unique`'s ideal hypothesis is **redundant**: its other
hypothesis implies it. The two-hypothesis form is kept because it is the direct instance of
`FormalSpectrum.awayCompletion_hom_ext`, whose own two hypotheses are *not* redundant — that
statement assumes only that `F` and `G` agree after `awayCompletionHom I f`, and from agreement
alone neither map is known to be continuous. The square-only form is
`FormalSpectrum.eq_awayCompletionRestrict_of_comp_awayCompletionHom`, downstream.

Nothing here says anything about `FormalSpectrum.IsStalkLimit`, stalks, germs or colimits.

## Implementation notes

`AdicCompletion.hom_ext_of_continuous` asks for agreement on `AdicCompletion.of K B` for every
`b : B`, i.e. on all of `Localization.Away f` and not merely on the image of `R`. That gap is closed
by `IsLocalization.ringHom_ext` at `Submonoid.powers f`: a ring map out of `Localization.Away f` is
determined by its restriction along `algebraMap R (Localization.Away f)`. The two forms of the
structure map are matched by `AssociatedGraded.algebraMap_eq_of`
(`FormalSchemes.AssociatedGradedCompletion`).

It also asks for its filtration condition in the module form `K ^ m • ⊤`, one condition per level;
`AdicCompletion.mem_idealOfDefinition_pow_iff` (`FormalSchemes.Completion`) converts that to
`awayCompletionIdeal I f ^ m`, and the level-`m` condition then follows from the level-`1` one by
`Ideal.map_pow` and `Ideal.pow_right_mono`. So every statement below takes its continuity hypothesis
in the single form `awayCompletionIdeal I f ≤ (awayCompletionIdeal I g).comap _`, which is the shape
`FormalSpectrum.locallyRingedSpaceMap` (`FormalSchemes.SpfMap`) consumes.

`Ideal.FG` is needed throughout, for two reasons at once: `AdicCompletion.hom_ext_of_continuous`
needs it to identify `K ^ m • ⊤` with the kernel of the level-`m` evaluation, and
`awayCompletionRestrict` needs it to exist at all.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. 0, §7.6 and Ch. I, §10.1.
* [The Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
-/

noncomputable section

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (I : Ideal R) (f g : R)

/-!
### The rigidity principle
-/

/-- **A map `R{1/f} →+* R{1/g}` is determined by its square over `R`, once it is continuous.** Two
ring maps that each carry the ideal of definition of `R{1/f}` into that of `R{1/g}` and that agree
after `FormalSpectrum.awayCompletionHom I f` are equal.

This is `AdicCompletion.hom_ext_of_continuous` (`FormalSchemes.AdicExtend`) instantiated at
`R{1/f}` and `R{1/g}`, with two adjustments. Its filtration hypothesis is one condition per level,
in the module form `K ^ m • ⊤`, and is recovered from the single ideal bound below through
`AdicCompletion.mem_idealOfDefinition_pow_iff` (`FormalSchemes.Completion`). Its agreement
hypothesis is on all of `Localization.Away f`, and is recovered from agreement on the image of `R`
by `IsLocalization.ringHom_ext` at `Submonoid.powers f`.

The continuity hypothesis is exactly what `FormalSpectrum.le_comap_awayCompletionRestrict` proves,
so `awayCompletionRestrict` satisfies it; that is `awayCompletionRestrict_unique` below. -/
theorem awayCompletion_hom_ext (hI : I.FG) {F G : awayCompletion I f →+* awayCompletion I g}
    (hF : awayCompletionIdeal I f ≤ (awayCompletionIdeal I g).comap F)
    (hG : awayCompletionIdeal I f ≤ (awayCompletionIdeal I g).comap G)
    (h : F.comp (awayCompletionHom I f) = G.comp (awayCompletionHom I f)) : F = G := by
  haveI : IsAdicComplete (awayCompletionIdeal I g) (awayCompletion I g) :=
    (AdicCompletion.isAdicRing_map _ (hI.map _)).toIsAdicComplete
  have pow : ∀ (Φ : awayCompletion I f →+* awayCompletion I g),
      awayCompletionIdeal I f ≤ (awayCompletionIdeal I g).comap Φ →
      ∀ (m : ℕ), ∀ x ∈ ((I.map (algebraMap R (Localization.Away f))) ^ m • ⊤ :
        Submodule (Localization.Away f) (awayCompletion I f)),
        Φ x ∈ (awayCompletionIdeal I g) ^ m := by
    intro Φ hΦ m x hx
    rw [← AdicCompletion.mem_idealOfDefinition_pow_iff] at hx
    have hmap : (awayCompletionIdeal I f ^ m).map Φ ≤ awayCompletionIdeal I g ^ m := by
      rw [Ideal.map_pow]
      exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hΦ) m
    exact hmap (Ideal.mem_map_of_mem _ hx)
  refine AdicCompletion.hom_ext_of_continuous _ _ (hI.map _) (pow F hF) (pow G hG) ?_
  have key : (F.comp (algebraMap (Localization.Away f) (awayCompletion I f))).comp
      (algebraMap R (Localization.Away f)) =
      (G.comp (algebraMap (Localization.Away f) (awayCompletion I f))).comp
      (algebraMap R (Localization.Away f)) := by
    rw [RingHom.comp_assoc, RingHom.comp_assoc]
    exact h
  have hloc := IsLocalization.ringHom_ext (M := Submonoid.powers f) (S := Localization.Away f) key
  intro b
  simpa [AssociatedGraded.algebraMap_eq_of] using RingHom.congr_fun hloc b

/-- **`FormalSpectrum.awayCompletionRestrict` is the unique continuous map under `R`.** Any ring map
`R{1/f} →+* R{1/g}` carrying the ideal of definition across and restricting to
`FormalSpectrum.awayCompletionHom I g` on the image of `R` is it. -/
theorem awayCompletionRestrict_unique (hI : I.FG) (hle : basicOpen I g ≤ basicOpen I f)
    {F : awayCompletion I f →+* awayCompletion I g}
    (hFideal : awayCompletionIdeal I f ≤ (awayCompletionIdeal I g).comap F)
    (hFsq : F.comp (awayCompletionHom I f) = awayCompletionHom I g) :
    F = awayCompletionRestrict I f g hI hle :=
  awayCompletion_hom_ext I f g hI hFideal (le_comap_awayCompletionRestrict I f g hI hle)
    (by rw [hFsq, awayCompletionRestrict_comp_awayCompletionHom])

/-!
### The functoriality laws, as corollaries of uniqueness
-/

/-- **Restriction along `D(f) ≤ D(f)` is the identity.** The identity satisfies both hypotheses of
`FormalSpectrum.awayCompletionRestrict_unique` for trivial reasons. -/
theorem awayCompletionRestrict_self (hI : I.FG) :
    awayCompletionRestrict I f f hI le_rfl = RingHom.id (awayCompletion I f) :=
  (awayCompletionRestrict_unique I f f hI le_rfl
    (by simp [Ideal.comap_id]) (by ext r; simp)).symm

/-- **The chain law.** For `D(h) ≤ D(g) ≤ D(f)`, restricting to `D(g)` and then to `D(h)` is
restricting to `D(h)`. `FormalSchemes.AwayCompletionRestrict` describes this as "a direct
computation through two `RingSplit.adicAwayUnitEquiv'`s"; with uniqueness available it is not — the
composite's square is the two squares in sequence and its ideal bound is the two bounds in
sequence. -/
theorem awayCompletionRestrict_comp {h : R} (hI : I.FG)
    (hgf : basicOpen I g ≤ basicOpen I f) (hhg : basicOpen I h ≤ basicOpen I g) :
    (awayCompletionRestrict I g h hI hhg).comp (awayCompletionRestrict I f g hI hgf) =
      awayCompletionRestrict I f h hI (hhg.trans hgf) :=
  awayCompletionRestrict_unique I f h hI (hhg.trans hgf)
    (fun x hx => le_comap_awayCompletionRestrict I g h hI hhg
      (le_comap_awayCompletionRestrict I f g hI hgf hx))
    (by rw [RingHom.comp_assoc, awayCompletionRestrict_comp_awayCompletionHom,
        awayCompletionRestrict_comp_awayCompletionHom])

/-!
### Completed localization maps under `R` are the restriction
-/

/-- **A completed map of localizations under `R` is the canonical restriction.** When a ring map
`φ : Localization.Away f →+* Localization.Away g` under `R` happens to exist — which for a general
basic inclusion of `Spf R` it does not, as `FormalSchemes.AwayCompletionRestrict` explains — its
completion is `FormalSpectrum.awayCompletionRestrict`. Its ideal bound is
`AdicCompletion.idealOfDefinition_map_le` and its square is
`AdicCompletion.mapCompletion_algebraMap`. -/
theorem awayCompletionRestrict_eq_mapCompletion (hI : I.FG)
    (hle : basicOpen I g ≤ basicOpen I f) (φ : Localization.Away f →+* Localization.Away g)
    (hφ : (I.map (algebraMap R (Localization.Away f))).map φ ≤
      I.map (algebraMap R (Localization.Away g)))
    (hcomp : φ.comp (algebraMap R (Localization.Away f)) = algebraMap R (Localization.Away g)) :
    AdicCompletion.mapCompletion φ hφ (hI.map _) = awayCompletionRestrict I f g hI hle :=
  awayCompletionRestrict_unique I f g hI hle
    (Ideal.map_le_iff_le_comap.mp (AdicCompletion.idealOfDefinition_map_le φ hφ (hI.map _)))
    (RingHom.ext fun r => by
      have hr : φ ((algebraMap R (Localization.Away f)) r) =
          (algebraMap R (Localization.Away g)) r := RingHom.congr_fun hcomp r
      simp only [RingHom.comp_apply, awayCompletionHom,
        AdicCompletion.mapCompletion_algebraMap, hr])

/-- **The nested leg is the canonical restriction.** `FormalSpectrum.awayCompletionMulHomLeft`
(`FormalSchemes.BasicOpenChartOverlapLegs`) is the completion of the further-localization map at
`D(f * g) ≤ D(f)`, and both of its hypotheses are landed there:
`FormalSpectrum.le_comap_awayCompletionMulHomLeft` and
`FormalSpectrum.awayCompletionMulHomLeft_comp_awayCompletionHom`.

This settles the caution recorded on the thread of the identification row — that
`awayCompletionRestrict` and `awayCompletionMulHomLeft` "are not known to agree" at the nested
inclusion, so the two nested statements are not interchangeable. They do agree, and are. -/
theorem awayCompletionRestrict_eq_awayCompletionMulHomLeft (hI : I.FG)
    (hle : basicOpen I (f * g) ≤ basicOpen I f) :
    awayCompletionMulHomLeft I f g hI = awayCompletionRestrict I f (f * g) hI hle :=
  awayCompletionRestrict_unique I f (f * g) hI hle
    (le_comap_awayCompletionMulHomLeft I f g hI)
    (awayCompletionMulHomLeft_comp_awayCompletionHom I f g hI)

/-!
### The identification with the structure-sheaf restriction, reduced to one bound
-/

variable [TopologicalSpace R] [IsAdicRing I]

/-- **The identification of the structure-sheaf restriction with
`FormalSpectrum.awayCompletionRestrict` follows from a single continuity bound.**
`FormalSpectrum.basicOpenRes` (`FormalSchemes.BasicOpenRestriction`) is the restriction
`Γ(D(f)) ⟶ Γ(D(g))` conjugated by `FormalSpectrum.sectionsBasicOpenEquiv`, and it already satisfies
the square over `R`, by `FormalSpectrum.basicOpenRes_comp_awayCompletionHom`. So the only thing
between it and `awayCompletionRestrict` is that it carry the ideal of definition across.

**The hypothesis is not discharged anywhere in this file**, and what is claimed here is only that
it is *sufficient* — so the identification needs no level-by-level comparison of the two maps, only
this bound. It is discharged in two lines downstream, by
`FormalSpectrum.le_comap_basicOpenRes` (`FormalSchemes.BasicOpenRestrictionIdentification`), which
observes that every map under `R` carries the ideal of definition across; the unconditional
identification is `FormalSpectrum.basicOpenRes_eq_awayCompletionRestrict` there. -/
theorem basicOpenRes_eq_awayCompletionRestrict_of_le_comap (hI : I.FG)
    (hle : basicOpen I g ≤ basicOpen I f)
    (hcont : awayCompletionIdeal I f ≤
      (awayCompletionIdeal I g).comap (basicOpenRes I hle)) :
    basicOpenRes I hle = awayCompletionRestrict I f g hI hle :=
  awayCompletionRestrict_unique I f g hI hle hcont (basicOpenRes_comp_awayCompletionHom I hle)

end FormalSpectrum
