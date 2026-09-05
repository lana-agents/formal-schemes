import FormalSchemes.StructureSheafStalkLevels
import FormalSchemes.BasicOpenChartComponent
import FormalSchemes.StructureSheafStalkBasicOpen
import FormalSchemes.BasicOpenRestriction

set_option linter.style.header false

/-!
# The stalk comparison on a germ from a basic open

`FormalSchemes.StructureSheafStalkLevels` builds the comparison map
`FormalSpectrum.stalkToAdicCompletion I x : O_{Spf R, x} →+* AdicCompletion (I · R_p) R_p`, whose
bijectivity is `FormalSpectrum.IsStalkLimit` — the stalk half of EGA I 10.8, *the stalk of the
completion is the completion of the stalk*. `FormalSchemes.StructureSheafStalkBasicOpen` describes
the **source** of that map: every germ at `x` comes from a section over a basic open `D(f)`, i.e.
from an element of `FormalSpectrum.awayCompletion I f`, and two such with the same germ already
agree over a smaller basic open.

The two descriptions have never been connected: **the comparison map has not been evaluated on a
single germ.** This file evaluates it. The answer is the one the shape of the problem predicts and
nothing on the tree had checked: on the germ of a section over `D(f)`, the comparison is
`AdicCompletion.mapCompletion` of the localization map `R_f →+* R_p`.

The consequence is `FormalSpectrum.isStalkLimit_iff_awayCompletion`: `FormalSpectrum.IsStalkLimit`
holds exactly when two explicit statements about completed localizations hold. No stalk, germ,
colimit or category occurs in either of them. **One sheaf-theoretic object does survive**, in the
injectivity half only, and it is named below: `FormalSpectrum.basicOpenRes`.

## How the computation goes

Level by level. `AdicCompletion.evalₐ_towerLimitRingEquiv` and `AdicCompletion.towerProj_apply`
turn `AdicCompletion.evalₐ` of the comparison into `FormalSpectrum.stalkTowerLevelEquiv` of
`FormalSpectrum.stalkProj` (`FormalSpectrum.evalₐ_stalkToAdicCompletion`), and
`TopCat.Presheaf.stalkFunctor_map_germ_apply` computes `FormalSpectrum.stalkProj` on a germ as the
germ of the level-`n` component (`FormalSpectrum.stalkProj_germ`).

What is left is the level-`n` statement `FormalSpectrum.stalkTowerLevelEquiv_germ_basicOpen`: the
germ map `Γ(D(f), O_{X_n}) ⟶ O_{X_n, x}` is, under `FormalSpectrum.basicOpenLevelEquiv` and
`FormalSpectrum.stalkTowerLevelEquiv`, the map of quotients induced by `R_f →+* R_p`. Both sides
are ring maps out of a localization of `R ⧸ I ^ (n + 1)` away from `f`
(`FormalSpectrum.isLocalization_away_basicOpen_sections`), so `IsLocalization.ringHom_ext` and
`Ideal.Quotient.ringHom_ext` reduce it to the constant section attached to an element of `R`, where
`FormalSpectrum.stalkTowerLevelEquiv_germ_mk` and `FormalSpectrum.basicOpenLevelEquiv_algebraMap_mk`
compute both sides. That is the same skeleton as `FormalSpectrum.stalkTowerLevelEquiv_step`.

Assembling the levels is `AdicCompletion.ext_evalₐ`, with level `0` a `Subsingleton` because
`J ^ 0 = ⊤`.

## Main definitions and results

* `FormalSpectrum.evalₐ_stalkToAdicCompletion`, `FormalSpectrum.stalkProj_germ`: the comparison map
  level by level, and the level-`n` projection on a germ.
* `FormalSpectrum.awayToAtPrime`: the localization map `R_f →+* R_p` available because
  `x ∈ D(f)` says exactly `f ∉ p` (`FormalSpectrum.notMem_pointPrime_of_mem_basicOpen`). It is a map
  under `R` (`FormalSpectrum.awayToAtPrime_algebraMap`) and carries `I · R_f` **onto**
  `FormalSpectrum.pointIdeal I x` (`FormalSpectrum.map_awayToAtPrime`), an equality and not merely
  a containment.
* `FormalSpectrum.awayToAtPrimeLevel`, `FormalSpectrum.awayToAtPrimeCompletion`: that map on the
  level-`n` quotients, and on the completions.
* `FormalSpectrum.stalkTowerLevelEquiv_germ_basicOpen`: the level-`n` comparison at a basic open.
* `FormalSpectrum.stalkToAdicCompletion_germ_basicOpen`: **the comparison map on a germ from a basic
  open is the completed localization map.**
* `FormalSpectrum.surjective_stalkToAdicCompletion_iff`,
  `FormalSpectrum.injective_stalkToAdicCompletion_iff` and
  `FormalSpectrum.isStalkLimit_iff_awayCompletion`: the two halves and their conjunction. The
  surjectivity half is sheaf-free outright; the injectivity half names
  `FormalSpectrum.basicOpenRes`, and the paragraph below says what that costs.

## What is *not* proved here

**Whether `FormalSpectrum.IsStalkLimit` holds.** It is undecided on this tree in both directions and
this file decides neither half of it. Every statement below is either a computation of a map or an
`Iff` whose two sides are both undecided; in particular
`FormalSpectrum.isStalkLimit_iff_awayCompletion` is a reformulation and not an answer, and nothing
here should be read as evidence in either direction.

**Nothing under a Noetherian hypothesis.** No finiteness assumption beyond `Ideal.FG` of the ideal
of definition appears below, and that one is present only because `AdicCompletion.mapCompletion`
requires its target ideal to be finitely generated.

**The obstruction, stated so that it is not rediscovered.** The localization
`Localization.AtPrime (pointPrime I x)` is the filtered colimit of the localizations away from
`f * g` over `g ∉ p`, so an element of `FormalSpectrum.awayCompletion I f` killed by
`FormalSpectrum.awayToAtPrimeCompletion` is killed *at each level `n` separately*, by a `g` that may
depend on `n`. The injectivity half of `FormalSpectrum.isStalkLimit_iff_awayCompletion` asks for one
`g` that works at every level. **That non-uniformity in `n` is the whole difficulty of the stalk
half of EGA I 10.8**, and no argument below addresses it. The surjectivity half has the same shape:
an element of the completion of that localization is a compatible system of level data, each of
which descends to a localization away from some `f * g`, with no reason for a single `g` to serve
all of them.

**That the injectivity half is free of the structure sheaf.** It is not, and the claim should not
be made. `FormalSpectrum.basicOpenRes` (`FormalSchemes.BasicOpenRestriction`) is *defined* as the
restriction `Γ(D(f)) ⟶ Γ(D(e))` of `O_{Spf R}` conjugated by
`FormalSpectrum.sectionsBasicOpenEquiv` on both sides, and inside this file's import closure nothing
pins it further than the image of `R` (`FormalSpectrum.basicOpenRes_comp_awayCompletionHom`); its
own module says so. The genuinely sheaf-free form is one rewrite away and is **not free**:
`FormalSpectrum.basicOpenRes_eq_awayCompletionRestrict`
(`FormalSchemes.BasicOpenRestrictionIdentification`) replaces it by the purely algebraic
`FormalSpectrum.awayCompletionRestrict` (`FormalSchemes.AwayCompletionRestrict`) for `I` finitely
generated, which this file already assumes, but that lemma carries `[TopologicalSpace R]` and
`IsAdicRing I` — two hypotheses nothing else here needs — and importing it adds **ten** modules to a
closure of 35. The variant was elaborated to check that it exists; taking the trade is a separate
row and is not taken here.

**A colimit, as a categorical statement.** This file does not build one, and
`FormalSchemes.StructureSheafStalkBasicOpen`'s recorded negative search result about
`CategoryTheory.Functor.Final` on `TopologicalSpace.OpenNhds` stands unchanged.

## Implementation notes

`AdicCompletion.evalₐ_mapCompletion` (`FormalSchemes.BasicOpenImmersion`) and
`AdicCompletion.ext_evalₐ` (Mathlib) are both used below and both were written from scratch before
being found; the second needs no finiteness hypothesis at all. The existing
`AdicCompletion.evalₐ_mapCompletion` takes a finite generation hypothesis on the *source* ideal and
an explicit continuity bound, neither of which its conclusion needs — but its module has reverse
closure 355, so weakening its signature is a separate measured decision and is not taken here.

The membership `x ∈ FormalSpectrum.basicOpen I f` and the non-membership
`f ∉ FormalSpectrum.pointPrime I x` are definitionally the same statement, since
`FormalSpectrum.pointPrime` is the contraction along `Ideal.Quotient.mk I` of the prime
`PrimeSpectrum.asIdeal` of the point, so
`FormalSpectrum.notMem_pointPrime_of_mem_basicOpen` needs no bridging lemma beyond
`FormalSpectrum.mem_basicOpen`.

Nothing below needs a topology on `R` or `IsAdicRing I`: the comparison map, the tower and the
sections identifications are all available without them.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (I : Ideal R) (x : FormalSpectrum I)

/-! ### The comparison map, level by level -/

/-- **The comparison map read at level `n`.** `AdicCompletion.evalₐ` of
`FormalSpectrum.stalkToAdicCompletion` is `FormalSpectrum.stalkTowerLevelEquiv` of the level-`n`
projection `FormalSpectrum.stalkProj`.

This is `AdicCompletion.evalₐ_towerLimitRingEquiv` and `AdicCompletion.towerProj_apply` at the
tower of stalks, with `FormalSpectrum.stalkToLimit_comp_π` recognising the limit projection of the
comparison as `FormalSpectrum.stalkProj`. It is the stalk analogue of
`FormalSpectrum.eval_sectionsBasicOpenEquiv`, whose proof has the same three steps. -/
theorem evalₐ_stalkToAdicCompletion (n : ℕ) (t : (structureSheaf I).presheaf.stalk x) :
    AdicCompletion.evalₐ (pointIdeal I x) (n + 1) (stalkToAdicCompletion I x t) =
      stalkTowerLevelEquiv I x n ((stalkProj I x n).hom t) := by
  change AdicCompletion.evalₐ _ (n + 1)
    (stalkTowerLimitEquiv I x ((stalkToLimit I x).hom t)) = _
  rw [stalkTowerLimitEquiv, AdicCompletion.evalₐ_towerLimitRingEquiv,
    AdicCompletion.towerProj_apply]
  congr 1
  exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (stalkToLimit_comp_π I x n)) t

/-- **The level-`n` projection on a germ is the germ of the level-`n` component.**
`FormalSpectrum.stalkProj` is the stalk functor applied to `CategoryTheory.Limits.limit.π`, so this
is `TopCat.Presheaf.stalkFunctor_map_germ_apply` at that morphism.

The `n = 0` case of this rewrite is currently written inline in **four** proofs, each inside a
`rw [show … from …]`: `FormalSpectrum.isUnit_stalk_of_isUnit_zero` (`FormalSchemes.Spf`),
`FormalSpectrum.isUnit_germ_top_iff` (`FormalSchemes.SpfGammaBase`),
`FormalSpectrum.isLocalHom_stalkMap` (`FormalSchemes.SpfMap`, twice) and
`FormalSpectrum.isUnit_germ_iff_isUnit_sectionsPi_zero` (`FormalSchemes.AdicOpennessHalf`, in the
`symm` direction). Rerouting them onto this lemma is a separate row and a *move*, not a call: three
of the four sit below this file and `FormalSchemes.AdicOpennessHalf` is incomparable with it, but
all four have `FormalSchemes.Spf` in their import closure, so the shared statement would have to
live at or under `FormalSchemes.Spf`. It is not attempted here. -/
theorem stalkProj_germ (n : ℕ) (U : Opens (FormalSpectrum I)) (hx : x ∈ U)
    (s : (structureSheaf I).presheaf.obj (op U)) :
    (stalkProj I x n).hom (((structureSheaf I).presheaf.germ U x hx).hom s) =
      ((thickeningSheaf I n).presheaf.germ U x hx).hom
        (((limit.π (structureSheafFunctor I) ⟨n⟩).hom.app (op U)).hom s) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
    (limit.π (structureSheafFunctor I) ⟨n⟩).hom s

/-! ### The localization map `R_f →+* R_p` -/

/-- **A point of a basic open avoids `f` in the prime below it.** `FormalSpectrum.pointPrime I x` is
the contraction along `Ideal.Quotient.mk I` of the prime `PrimeSpectrum.asIdeal` of the point, so
this is
`FormalSpectrum.mem_basicOpen` with no further bridging. -/
theorem notMem_pointPrime_of_mem_basicOpen {f : R} (hf : x ∈ basicOpen I f) :
    f ∉ pointPrime I x := by
  rw [mem_basicOpen] at hf
  intro hmem
  exact hf hmem

/-- `f` becomes a unit in the localization of `R` at the prime under a point of `D(f)`. -/
theorem isUnit_algebraMap_atPrime_of_mem_basicOpen {f : R} (hf : x ∈ basicOpen I f) :
    IsUnit (algebraMap R (Localization.AtPrime (pointPrime I x)) f) :=
  IsLocalization.map_units (Localization.AtPrime (pointPrime I x))
    (⟨f, notMem_pointPrime_of_mem_basicOpen I x hf⟩ : (pointPrime I x).primeCompl)

/-- **The localization map `R_f →+* R_p`** for a point `x ∈ D(f)`, obtained from the universal
property of the localization away from `f` at the unit
`FormalSpectrum.isUnit_algebraMap_atPrime_of_mem_basicOpen`.

This is the ring map the whole file is about: the germ of a section over `D(f)` is computed by
completing it (`FormalSpectrum.stalkToAdicCompletion_germ_basicOpen`). -/
def awayToAtPrime {f : R} (hf : x ∈ basicOpen I f) :
    Localization.Away f →+* Localization.AtPrime (pointPrime I x) :=
  IsLocalization.Away.lift f (isUnit_algebraMap_atPrime_of_mem_basicOpen I x hf)

/-- `FormalSpectrum.awayToAtPrime` is a map under `R`. -/
theorem awayToAtPrime_algebraMap {f : R} (hf : x ∈ basicOpen I f) (r : R) :
    awayToAtPrime I x hf (algebraMap R (Localization.Away f) r) =
      algebraMap R (Localization.AtPrime (pointPrime I x)) r :=
  IsLocalization.Away.lift_eq f (isUnit_algebraMap_atPrime_of_mem_basicOpen I x hf) r

/-- **`FormalSpectrum.awayToAtPrime` carries the ideal of definition onto the ideal of definition**:
the extension of `I` to `Localization.Away f` maps onto `FormalSpectrum.pointIdeal I x`. It is an
equality rather than a containment because both ideals are the extension of `I` along a map under
`R`, so `Ideal.map_map` and `FormalSpectrum.awayToAtPrime_algebraMap` identify them outright. -/
theorem map_awayToAtPrime {f : R} (hf : x ∈ basicOpen I f) :
    (I.map (algebraMap R (Localization.Away f))).map (awayToAtPrime I x hf) = pointIdeal I x := by
  rw [Ideal.map_map, pointIdeal]
  congr 1
  exact RingHom.ext (awayToAtPrime_algebraMap I x hf)

/-- The continuity bound `FormalSpectrum.awayToAtPrimeLevel` and
`AdicCompletion.evalₐ_mapCompletion` consume, which for this map is forced by
`FormalSpectrum.map_awayToAtPrime`. -/
theorem pow_le_comap_awayToAtPrime {f : R} (hf : x ∈ basicOpen I f) (n : ℕ) :
    (I.map (algebraMap R (Localization.Away f))) ^ (n + 1) ≤
      ((pointIdeal I x) ^ (n + 1)).comap (awayToAtPrime I x hf) := by
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow, map_awayToAtPrime]

/-- `FormalSpectrum.awayToAtPrime` on the level-`n` quotients:
`R_f ⧸ (I · R_f) ^ (n + 1) →+* R_p ⧸ (I · R_p) ^ (n + 1)`. -/
def awayToAtPrimeLevel {f : R} (hf : x ∈ basicOpen I f) (n : ℕ) :
    Localization.Away f ⧸ (I.map (algebraMap R (Localization.Away f))) ^ (n + 1) →+*
      Localization.AtPrime (pointPrime I x) ⧸ (pointIdeal I x) ^ (n + 1) :=
  Ideal.quotientMap _ (awayToAtPrime I x hf) (pow_le_comap_awayToAtPrime I x hf n)

/-- **`FormalSpectrum.awayToAtPrime` on the completions**, i.e.
`R{1/f} →+* AdicCompletion (I · R_p) R_p`.
The finite generation hypothesis is `AdicCompletion.mapCompletion`'s, on the target ideal, and
`FormalSpectrum.map_awayToAtPrime` supplies the containment it needs as an equality. -/
def awayToAtPrimeCompletion (hI : I.FG) {f : R} (hf : x ∈ basicOpen I f) :
    awayCompletion I f →+*
      AdicCompletion (pointIdeal I x) (Localization.AtPrime (pointPrime I x)) :=
  AdicCompletion.mapCompletion (awayToAtPrime I x hf) (le_of_eq (map_awayToAtPrime I x hf))
    (hI.map _)

/-! ### The comparison at a basic open -/

/-- **The level-`n` comparison at a basic open.** The germ map of the level-`n` thickening sheaf at
`D(f)` is, read through `FormalSpectrum.basicOpenLevelEquiv` on the source and
`FormalSpectrum.stalkTowerLevelEquiv` on the target, the map of quotients induced by
`FormalSpectrum.awayToAtPrime`.

Both sides are ring maps out of `Γ(D(f), thickeningSheaf I n)`, which is a localization of
`R ⧸ I ^ (n + 1)` away from `f mod I ^ (n + 1)`
(`FormalSpectrum.isLocalization_away_basicOpen_sections`), so `IsLocalization.ringHom_ext` followed
by `Ideal.Quotient.ringHom_ext` reduces the claim to the constant sections attached to elements of
`R`, where `FormalSpectrum.stalkTowerLevelEquiv_germ_mk` and
`FormalSpectrum.basicOpenLevelEquiv_algebraMap_mk` compute the two sides to the same class. This is
the skeleton of `FormalSpectrum.stalkTowerLevelEquiv_step` with the tower's transition map replaced
by the germ map. -/
theorem stalkTowerLevelEquiv_germ_basicOpen (n : ℕ) {f : R} (hf : x ∈ basicOpen I f)
    (t : (thickeningSheaf I n).presheaf.obj (op (basicOpen I f))) :
    stalkTowerLevelEquiv I x n
        (((thickeningSheaf I n).presheaf.germ (basicOpen I f) x hf).hom t) =
      awayToAtPrimeLevel I x hf n (basicOpenLevelEquiv I f n t) := by
  have key : (stalkTowerLevelEquiv I x n).toRingHom.comp
        ((thickeningSheaf I n).presheaf.germ (basicOpen I f) x hf).hom =
      (awayToAtPrimeLevel I x hf n).comp (basicOpenLevelEquiv I f n).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (Ideal.Quotient.mk (I ^ (n + 1)) f))
    apply Ideal.Quotient.ringHom_ext
    refine RingHom.ext fun y => ?_
    -- both sides, with every coercion written the way the two computation rules state it
    change stalkTowerLevelEquiv I x n
        (((thickeningSheaf I n).presheaf.germ (basicOpen I f) x hf).hom
          (algebraMap (R ⧸ I ^ (n + 1))
            ((thickeningSheaf I n).presheaf.obj (op (basicOpen I f)))
            (Ideal.Quotient.mk (I ^ (n + 1)) y))) =
      awayToAtPrimeLevel I x hf n
        (basicOpenLevelEquiv I f n
          (algebraMap (R ⧸ I ^ (n + 1))
            ((thickeningSheaf I n).presheaf.obj (op (basicOpen I f)))
            (Ideal.Quotient.mk (I ^ (n + 1)) y)))
    rw [stalkTowerLevelEquiv_germ_mk I x n (basicOpen I f) hf y,
      basicOpenLevelEquiv_algebraMap_mk I f n y, awayToAtPrimeLevel,
      Ideal.quotientMap_mk, awayToAtPrime_algebraMap]
  exact DFunLike.congr_fun key t

/-- **The comparison map on a germ from a basic open.** The germ at `x` of a section over `D(f)`,
pushed through `FormalSpectrum.stalkToAdicCompletion`, is the completed localization map
`FormalSpectrum.awayToAtPrimeCompletion` applied to the section read as an element of
`FormalSpectrum.awayCompletion I f`.

Both sides are elements of `AdicCompletion (I · R_p) R_p`, so `AdicCompletion.ext_evalₐ` reduces
this to every level. Level `0` is trivial because `(I · R_p) ^ 0 = ⊤` makes the quotient a
`Subsingleton`; level `n + 1` is `FormalSpectrum.evalₐ_stalkToAdicCompletion`,
`FormalSpectrum.stalkProj_germ` and `FormalSpectrum.stalkTowerLevelEquiv_germ_basicOpen` on the left
against `AdicCompletion.evalₐ_mapCompletion` and `FormalSpectrum.eval_sectionsBasicOpenEquiv` on the
right, landing on the same `Ideal.quotientMap`.

This is the statement that connects the description of the stalk as a filtered colimit of the
`FormalSpectrum.awayCompletion I f` (`FormalSchemes.StructureSheafStalkBasicOpen`) with the
description of the target as `AdicCompletion (I · R_p) R_p`
(`FormalSchemes.StructureSheafStalkLevels`). It says nothing about whether the comparison is
bijective. -/
theorem stalkToAdicCompletion_germ_basicOpen (hI : I.FG) {f : R} (hf : x ∈ basicOpen I f)
    (s : (structureSheaf I).presheaf.obj (op (basicOpen I f))) :
    stalkToAdicCompletion I x
        (((structureSheaf I).presheaf.germ (basicOpen I f) x hf).hom s) =
      awayToAtPrimeCompletion I x hI hf (sectionsBasicOpenEquiv I f s) := by
  refine AdicCompletion.ext_evalₐ fun m => ?_
  cases m with
  | zero =>
    haveI : Subsingleton (Localization.AtPrime (pointPrime I x) ⧸ (pointIdeal I x) ^ 0) :=
      (Ideal.Quotient.subsingleton_iff).mpr (by rw [pow_zero]; exact Ideal.one_eq_top)
    exact Subsingleton.elim _ _
  | succ n =>
    rw [evalₐ_stalkToAdicCompletion, stalkProj_germ, stalkTowerLevelEquiv_germ_basicOpen,
      awayToAtPrimeCompletion,
      AdicCompletion.evalₐ_mapCompletion (awayToAtPrime I x hf)
        (le_of_eq (map_awayToAtPrime I x hf)) (hI.map _) (hI.map _) (n + 1)
        (pow_le_comap_awayToAtPrime I x hf n),
      eval_sectionsBasicOpenEquiv]
    rfl

/-! ### `IsStalkLimit` as a statement about completed localizations -/

/-- **The surjectivity half of `FormalSpectrum.IsStalkLimit`, as a statement about completed
localizations.** The comparison map is surjective exactly when every element of
`AdicCompletion (I · R_p) R_p` is the image of an element of some `R{1/f}` with `x ∈ D(f)`.

Forwards this is `FormalSpectrum.exists_adicCompletion_germ_eq` — every germ comes from a basic
open — followed by `FormalSpectrum.stalkToAdicCompletion_germ_basicOpen`; backwards it is that
computation alone, applied to the germ of the section the hypothesis produces.

Both sides are undecided. -/
theorem surjective_stalkToAdicCompletion_iff (hI : I.FG) :
    Function.Surjective (stalkToAdicCompletion I x) ↔
      ∀ b : AdicCompletion (pointIdeal I x) (Localization.AtPrime (pointPrime I x)),
        ∃ (f : R) (hf : x ∈ basicOpen I f) (a : awayCompletion I f),
          awayToAtPrimeCompletion I x hI hf a = b := by
  constructor
  · intro hsurj b
    obtain ⟨t, ht⟩ := hsurj b
    obtain ⟨f, hf, a, ha⟩ := exists_adicCompletion_germ_eq I x t
    refine ⟨f, hf, a, ?_⟩
    rw [← ht, ← ha, stalkToAdicCompletion_germ_basicOpen I x hI hf, RingEquiv.apply_symm_apply]
  · intro h b
    obtain ⟨f, hf, a, ha⟩ := h b
    refine ⟨((structureSheaf I).presheaf.germ (basicOpen I f) x hf).hom
      ((sectionsBasicOpenEquiv I f).symm a), ?_⟩
    rw [stalkToAdicCompletion_germ_basicOpen I x hI hf, RingEquiv.apply_symm_apply, ha]

/-- **The injectivity half of `FormalSpectrum.IsStalkLimit`**, in terms of completed localizations
and the structure-sheaf restriction between two basic opens. The comparison map is injective exactly
when an element of `R{1/f}` killed by
`FormalSpectrum.awayToAtPrimeCompletion` is already killed by restriction
(`FormalSpectrum.basicOpenRes`) to some smaller basic open through `x`.

The bridge between "the germ vanishes" and "some restriction vanishes" is
`FormalSpectrum.exists_basicOpen_res_eq` at the second section `0` over
`FormalSpectrum.basicOpen I 1 = ⊤` in one direction and `TopCat.Presheaf.germ_res_apply` in the
other.

Both sides are undecided; see the module docstring for why the `e` this asks for is hard to
produce. -/
theorem injective_stalkToAdicCompletion_iff (hI : I.FG) :
    Function.Injective (stalkToAdicCompletion I x) ↔
      ∀ (f : R) (hf : x ∈ basicOpen I f) (a : awayCompletion I f),
        awayToAtPrimeCompletion I x hI hf a = 0 →
          ∃ (e : R) (_ : x ∈ basicOpen I e) (hle : basicOpen I e ≤ basicOpen I f),
            basicOpenRes I hle a = 0 := by
  rw [injective_iff_map_eq_zero]
  constructor
  · intro hinj f hf a ha
    have hzero : ((structureSheaf I).presheaf.germ (basicOpen I f) x hf).hom
        ((sectionsBasicOpenEquiv I f).symm a) = 0 := by
      refine hinj _ ?_
      rw [stalkToAdicCompletion_germ_basicOpen I x hI hf, RingEquiv.apply_symm_apply, ha]
    have hone : x ∈ basicOpen I (1 : R) := by rw [basicOpen_one]; trivial
    obtain ⟨e, hxe, hef, he1, heq⟩ := exists_basicOpen_res_eq I x hf hone
      ((sectionsBasicOpenEquiv I f).symm a) 0 (by rw [hzero, map_zero])
    refine ⟨e, hxe, hef, ?_⟩
    rw [basicOpenRes]
    simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
    rw [heq, map_zero, map_zero]
  · intro h t ht
    obtain ⟨f, hf, s, hs⟩ := exists_basicOpen_germ_eq I x t
    have ha : awayToAtPrimeCompletion I x hI hf (sectionsBasicOpenEquiv I f s) = 0 := by
      rw [← stalkToAdicCompletion_germ_basicOpen I x hI hf, hs, ht]
    obtain ⟨e, hxe, hle, hres⟩ := h f hf (sectionsBasicOpenEquiv I f s) ha
    have hs0 : ((structureSheaf I).presheaf.map (homOfLE hle).op).hom s = 0 := by
      rw [basicOpenRes] at hres
      simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe,
        Function.comp_apply, RingEquiv.symm_apply_apply] at hres
      exact (map_eq_zero_iff _ (sectionsBasicOpenEquiv I e).injective).mp hres
    rw [← hs, ← TopCat.Presheaf.germ_res_apply (structureSheaf I).presheaf (homOfLE hle) x hxe s,
      hs0, map_zero]

/-- **`FormalSpectrum.IsStalkLimit` as two statements about completed localizations.** The stalk
half of EGA I 10.8 at `x` holds exactly when the two explicit statements of
`FormalSpectrum.injective_stalkToAdicCompletion_iff` and
`FormalSpectrum.surjective_stalkToAdicCompletion_iff` both hold. No stalk, germ, colimit or category
occurs on the right-hand side, and no sheaf occurs in the surjectivity half. The injectivity half
still names `FormalSpectrum.basicOpenRes`, which is the structure-sheaf restriction by definition;
the module docstring records what replacing it by `FormalSpectrum.awayCompletionRestrict` would
cost.

**This is a reformulation and not an answer.** The two sides of the `Iff` are both undecided on this
tree, in both directions, and the module docstring records the obstruction — the `g` produced at
each level need not be independent of the level — that any attempt at either half has to face. -/
theorem isStalkLimit_iff_awayCompletion (hI : I.FG) :
    IsStalkLimit I x ↔
      (∀ (f : R) (hf : x ∈ basicOpen I f) (a : awayCompletion I f),
          awayToAtPrimeCompletion I x hI hf a = 0 →
            ∃ (e : R) (_ : x ∈ basicOpen I e) (hle : basicOpen I e ≤ basicOpen I f),
              basicOpenRes I hle a = 0) ∧
        ∀ b : AdicCompletion (pointIdeal I x) (Localization.AtPrime (pointPrime I x)),
          ∃ (f : R) (hf : x ∈ basicOpen I f) (a : awayCompletion I f),
            awayToAtPrimeCompletion I x hI hf a = b := by
  rw [isStalkLimit_iff_bijective_stalkToAdicCompletion, Function.Bijective,
    injective_stalkToAdicCompletion_iff I x hI, surjective_stalkToAdicCompletion_iff I x hI]

end FormalSpectrum
