import FormalSchemes.StructureSheafStalks
import FormalSchemes.LocalizationQuotientPrime

set_option linter.style.header false

/-!
# The stalk-level comparison, read as a map into an adic completion

`FormalSchemes.StructureSheafStalks` builds, at a point `x ∈ Spf R`, the tower
`FormalSpectrum.stalkTower I x` of stalks of the thickening sheaves, the comparison map
`FormalSpectrum.stalkToLimit` from the stalk of `O_{Spf R}` into its limit, and the question
`FormalSpectrum.IsStalkLimit` of whether that comparison is an isomorphism. It leaves level `n` of
the tower as `Localization.AtPrime` of `R ⧸ I ^ (n + 1)` — a prime of a *different ring* for each
`n` — and says in as many words that identifying the limit with an adic completion is not done
there.

This file does that identification. The limit of the tower is
`AdicCompletion (I · R_p) R_p`, writing `R_p = Localization.AtPrime (pointPrime I x)` for the
localization of `R` at the prime under `x`, which is the stalk of `O_{Spec R}` there
(`AlgebraicGeometry.StructureSheaf.stalkIso`). So
`FormalSpectrum.IsStalkLimit I x` becomes the statement that an **explicit** ring map
`O_{Spf R, x} ⟶ AdicCompletion (I · R_p) R_p` is bijective: *the stalk of the completion is the
completion of the stalk*.

**The question is still not answered.** Nothing here decides `FormalSpectrum.IsStalkLimit`, in
either direction; what changes is that the two sides of the comparison are now both named in terms
of `R`, so a proof or a counterexample has something concrete to be about.

## How the identification goes

The step that makes a *tower* out of the levels is that they all sit over **one** prime of `R`.
`FormalSpectrum.levelPrime I x n` lives in `R ⧸ I ^ (n + 1)`, but every one of them contracts to
`FormalSpectrum.pointPrime I x` along `Ideal.Quotient.mk` — that is
`FormalSpectrum.comap_mk_toThickening`, the compatibility of the thickening homeomorphisms with the
closed embeddings into `Spec R`, and it is recorded here as
`FormalSpectrum.levelPrime_comap`. `Localization.atPrimeQuotientEquiv`
(`FormalSchemes.LocalizationQuotientPrime`) is phrased to take exactly that hypothesis, and turns
level `n` into `R_p ⧸ (I · R_p) ^ (n + 1)`.

`AdicCompletion.towerLimitRingEquiv` then needs those level identifications to intertwine the
tower's transition maps with `Ideal.Quotient.factorPow`. That is
`FormalSpectrum.stalkTowerLevelEquiv_step`, and it is where the work is. Its proof runs on germs:
`FormalSpectrum.stalkTower_map_germ` computes the tower's transition map on a germ as the germ of
the section map, and `FormalSpectrum.thickeningStalkLocalizationEquiv_germ_algebraMap` computes the
level identification on the germ of a constant section. Both sides are then determined by their
values on the image of `R`, because the source is a localization of `R ⧸ I ^ (n + 2)`
(`IsLocalization.ringHom_ext`) — the same shape as
`FormalSpectrum.basicOpenLevelEquiv_step` for the tower of sections over a basic open.

## Main definitions and results

* `FormalSpectrum.pointPrime`, `FormalSpectrum.le_pointPrime`: the prime of `R` under a point of
  `Spf R`, and the fact that it contains the ideal of definition.
* `FormalSpectrum.levelPrime_comap`: every level's prime contracts to it.
* `FormalSpectrum.pointIdeal`, `FormalSpectrum.stalkTowerLevelEquiv`: the extension `I · R_p`, and
  the identification of level `n` of the tower with `R_p ⧸ (I · R_p) ^ (n + 1)`.
* `FormalSpectrum.stalkTowerLevelEquiv_step`: those identifications intertwine the tower's
  transition maps with `Ideal.Quotient.factorPow`.
* `FormalSpectrum.stalkTowerLimitEquiv`: **the limit of the stalk tower is
  `AdicCompletion (I · R_p) R_p`.**
* `FormalSpectrum.stalkToAdicCompletion` and
  `FormalSpectrum.isStalkLimit_iff_bijective_stalkToAdicCompletion`: the comparison map read into
  that completion, and `FormalSpectrum.IsStalkLimit` as the statement that it is bijective.

## What is *not* proved here

**Whether `FormalSpectrum.stalkToAdicCompletion` is bijective**, equivalently whether
`FormalSpectrum.IsStalkLimit` holds. It is undecided on this tree in both directions and this file
does not touch it. Every statement below is an identification of the *target* of the comparison, not
a statement about the comparison itself, with the single exception of
`FormalSpectrum.isStalkLimit_iff_bijective_stalkToAdicCompletion`, which is an `Iff` between two
undecided statements.

**That `R_p = Localization.AtPrime (pointPrime I x)` is the stalk of `O_{Spec R}` at the image of
`x`.** That is Mathlib's
`AlgebraicGeometry.StructureSheaf.stalkIso` and it is used inside
`FormalSpectrum.thickeningStalkLocalizationEquiv` at each level, but no declaration here states it
for `R` itself; the reading of the headline as "the stalk of the completion is the completion of the
stalk" rests on it and is prose, not a theorem below.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]

omit [TopologicalSpace R] [IsAdicRing I]

variable (x : FormalSpectrum I)

/-! ### The prime of `R` under a point of `Spf R` -/

/-- The prime of `R` under a point `x ∈ Spf R`: the underlying ideal of
`FormalSpectrum.toPrimeSpectrum`, which realises `Spf R` as the closed subspace of `Spec R` cut out
by the ideal of definition. -/
def pointPrime : Ideal R := (toPrimeSpectrum I x).asIdeal

instance : (pointPrime I x).IsPrime := (toPrimeSpectrum I x).isPrime

/-- The ideal of definition is contained in the prime under any point of `Spf R`: the points of
`Spf R` are exactly the primes containing it (`FormalSpectrum.range_toPrimeSpectrum`). -/
theorem le_pointPrime : I ≤ pointPrime I x := by
  have h : toPrimeSpectrum I x ∈ Set.range (toPrimeSpectrum I) := ⟨x, rfl⟩
  rw [range_toPrimeSpectrum] at h
  exact h

/-- **Every level's prime lies over the same prime of `R`.** The prime
`FormalSpectrum.levelPrime I x n` of `R ⧸ I ^ (n + 1)` contracts to `FormalSpectrum.pointPrime I x`,
uniformly in `n`.

This is `FormalSpectrum.comap_mk_toThickening` read on underlying ideals, and it is what makes the
levels of `FormalSpectrum.stalkTower` a tower over a single ring: without it, each level would be a
localization of a different ring at an unrelated prime. -/
theorem levelPrime_comap (n : ℕ) :
    (levelPrime I x n).asIdeal.comap (Ideal.Quotient.mk (I ^ (n + 1))) = pointPrime I x :=
  congrArg PrimeSpectrum.asIdeal (comap_mk_toThickening I (n + 1) n.succ_ne_zero x)

/-! ### The levels of the stalk tower -/

/-- The extension `I · R_p` of the ideal of definition to the localization of `R` at the prime under
`x`. The limit of `FormalSpectrum.stalkTower I x` is the adic completion of that localization for
this ideal; see `FormalSpectrum.stalkTowerLimitEquiv`. -/
def pointIdeal : Ideal (Localization.AtPrime (pointPrime I x)) :=
  I.map (algebraMap R (Localization.AtPrime (pointPrime I x)))

/-- **Level `n` of the stalk tower is `R_p ⧸ (I · R_p) ^ (n + 1)`**, where `p` is the prime of `R`
under `x`.

Three steps: `FormalSpectrum.thickeningStalkLocalizationEquiv` presents the level as
`Localization.AtPrime` of `R ⧸ I ^ (n + 1)`; `Localization.atPrimeQuotientEquiv` turns that into a
quotient of `Localization.AtPrime (pointPrime I x)`, using `FormalSpectrum.levelPrime_comap` to
supply the prime below; and `Ideal.map_pow` rewrites the extension of `I ^ (n + 1)` as the
`(n + 1)`-st power of the extension of `I`. -/
def stalkTowerLevelEquiv (n : ℕ) :
    ((stalkTower I x).obj ⟨n⟩ : Type u) ≃+*
      Localization.AtPrime (pointPrime I x) ⧸ pointIdeal I x ^ (n + 1) :=
  (thickeningStalkLocalizationEquiv I x n).trans
    ((Localization.atPrimeQuotientEquiv (I ^ (n + 1)) (levelPrime I x n).asIdeal
        (pointPrime I x) (levelPrime_comap I x n)).trans
      (Ideal.quotEquivOfEq (by rw [pointIdeal, Ideal.map_pow])))

/-! ### The level identifications on germs -/

/-- `FormalSpectrum.thickeningStalkLocalizationEquiv` sends the germ at `x` of the constant section
attached to `a : R ⧸ I ^ (n + 1)` to the image of `a` in the localization.

This is the germ-level naturality the compatibility with the tower's transition maps runs on:
`FormalSpectrum.thickeningStalkIso_hom_germ` moves the germ to the thickening's spectrum,
`AlgebraicGeometry.StructureSheaf.algebraMap_germ` recognises it as
`AlgebraicGeometry.StructureSheaf.toStalk`, and
`AlgebraicGeometry.StructureSheaf.stalkIso` is a map of `R ⧸ I ^ (n + 1)`-algebras. -/
theorem thickeningStalkLocalizationEquiv_germ_algebraMap (n : ℕ) (U : Opens (FormalSpectrum I))
    (hx : x ∈ U) (a : R ⧸ I ^ (n + 1)) :
    thickeningStalkLocalizationEquiv I x n
        (((thickeningSheaf I n).presheaf.germ U x hx).hom
          (algebraMap (R ⧸ I ^ (n + 1)) ((thickeningSheaf I n).presheaf.obj (op U)) a)) =
      algebraMap (R ⧸ I ^ (n + 1)) (Localization.AtPrime (levelPrime I x n).asIdeal) a := by
  have h1 := thickeningStalkIso_hom_germ I n x U hx
      (algebraMap (R ⧸ I ^ (n + 1)) ((thickeningSheaf I n).presheaf.obj (op U)) a)
  have h2 : ((Spec.structureSheaf (R ⧸ I ^ (n + 1))).presheaf.germ (thickeningOpen I n U)
        ((thickeningTopIso I n).hom x) (hom_mem_thickeningOpen I n x hx)).hom
        (algebraMap (R ⧸ I ^ (n + 1)) ((thickeningSheaf I n).presheaf.obj (op U)) a) =
      StructureSheaf.toStalk (R ⧸ I ^ (n + 1)) (levelPrime I x n) a :=
    StructureSheaf.algebraMap_germ_apply _ _ _ a
  rw [thickeningStalkLocalizationEquiv]
  simp only [RingEquiv.trans_apply]
  rw [show (thickeningStalkIso I n x).commRingCatIsoToRingEquiv _ = _ from h1, h2]
  exact (StructureSheaf.stalkIso (R ⧸ I ^ (n + 1)) (levelPrime I x n)).symm_apply_eq.mpr
    ((StructureSheaf.stalkIso (R ⧸ I ^ (n + 1)) (levelPrime I x n)).commutes a).symm

/-- The inverse form of `FormalSpectrum.thickeningStalkLocalizationEquiv_germ_algebraMap`, over the
whole space: the image of `a` in the localization comes from the germ at `x` of the constant
section attached to `a`. -/
theorem thickeningStalkLocalizationEquiv_symm_algebraMap (n : ℕ) (a : R ⧸ I ^ (n + 1)) :
    (thickeningStalkLocalizationEquiv I x n).symm
        (algebraMap (R ⧸ I ^ (n + 1)) (Localization.AtPrime (levelPrime I x n).asIdeal) a) =
      ((thickeningSheaf I n).presheaf.germ ⊤ x trivial).hom
        (algebraMap (R ⧸ I ^ (n + 1)) ((thickeningSheaf I n).presheaf.obj (op ⊤)) a) :=
  (thickeningStalkLocalizationEquiv I x n).symm_apply_eq.mpr
    (thickeningStalkLocalizationEquiv_germ_algebraMap I x n ⊤ trivial a).symm

/-- `FormalSpectrum.stalkTowerLevelEquiv` on the germ of the constant section attached to `y : R`:
the answer is the image of `y` in `R_p ⧸ (I · R_p) ^ (n + 1)`. This is the stalk analogue of
`FormalSpectrum.basicOpenLevelEquiv_algebraMap_mk`. -/
theorem stalkTowerLevelEquiv_germ_mk (n : ℕ) (U : Opens (FormalSpectrum I)) (hx : x ∈ U) (y : R) :
    stalkTowerLevelEquiv I x n
        (((thickeningSheaf I n).presheaf.germ U x hx).hom
          (algebraMap (R ⧸ I ^ (n + 1)) ((thickeningSheaf I n).presheaf.obj (op U))
            (Ideal.Quotient.mk (I ^ (n + 1)) y))) =
      Ideal.Quotient.mk (pointIdeal I x ^ (n + 1))
        (algebraMap R (Localization.AtPrime (pointPrime I x)) y) := by
  have key : ∀ z : ((stalkTower I x).obj ⟨n⟩ : Type u), stalkTowerLevelEquiv I x n z =
      Ideal.quotEquivOfEq (show (I ^ (n + 1)).map
            (algebraMap R (Localization.AtPrime (pointPrime I x))) = pointIdeal I x ^ (n + 1) by
          rw [pointIdeal, Ideal.map_pow])
        (Localization.atPrimeQuotientEquiv (I ^ (n + 1)) (levelPrime I x n).asIdeal
          (pointPrime I x) (levelPrime_comap I x n)
          (thickeningStalkLocalizationEquiv I x n z)) := fun _ => rfl
  rw [key, show thickeningStalkLocalizationEquiv I x n _ = _ from
      thickeningStalkLocalizationEquiv_germ_algebraMap I x n U hx _,
    Localization.atPrimeQuotientEquiv_algebraMap]
  have h2 : (algebraMap (R ⧸ I ^ (n + 1))
      (Localization.AtPrime (pointPrime I x) ⧸
        (I ^ (n + 1)).map (algebraMap R (Localization.AtPrime (pointPrime I x)))))
        (Ideal.Quotient.mk (I ^ (n + 1)) y) =
      Ideal.Quotient.mk ((I ^ (n + 1)).map (algebraMap R (Localization.AtPrime (pointPrime I x))))
        (algebraMap R (Localization.AtPrime (pointPrime I x)) y) :=
    rfl
  rw [h2, Ideal.quotEquivOfEq_mk]

/-- The transition map of `FormalSpectrum.stalkTower` on a germ is the germ of the transition map on
sections: the tower's map is the stalk functor applied to `FormalSpectrum.stepSheafHom`. -/
theorem stalkTower_map_germ (n : ℕ) (U : Opens (FormalSpectrum I)) (hx : x ∈ U)
    (t : (thickeningSheaf I (n + 1)).presheaf.obj (op U)) :
    ((stalkTower I x).map (homOfLE (Nat.le_add_right n 1)).op).hom
        (((thickeningSheaf I (n + 1)).presheaf.germ U x hx).hom t) =
      ((thickeningSheaf I n).presheaf.germ U x hx).hom
        (((stepSheafHom I n).hom.app (op U)).hom t) := by
  have h : (structureSheafFunctor I).map (homOfLE (Nat.le_add_right n 1)).op =
      stepSheafHom I n := by
    simp only [structureSheafFunctor]
    exact Functor.ofOpSequence_map_homOfLE_succ _ n
  change ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
    ((structureSheafFunctor I).map (homOfLE (Nat.le_add_right n 1)).op).hom).hom _ = _
  rw [h]
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx ((stepSheafHom I n).hom) t

/-! ### The limit of the tower is an adic completion -/

/-- **The level identifications intertwine the tower's transition maps with the quotient factor
maps.** This is the input `AdicCompletion.towerLimitRingEquiv` needs beyond the levels themselves,
and it is the stalk analogue of `FormalSpectrum.basicOpenLevelEquiv_step`.

Both sides are ring maps out of a localization of `R ⧸ I ^ (n + 2)` — that is what
`FormalSpectrum.thickeningStalkLocalizationEquiv` says — so `IsLocalization.ringHom_ext` and
`Ideal.Quotient.ringHom_ext` reduce the claim to the constant sections attached to elements of `R`,
where `FormalSpectrum.stalkTower_map_germ`, `FormalSpectrum.comap_step_algebraMap` and
`FormalSpectrum.stalkTowerLevelEquiv_germ_mk` compute both sides. -/
theorem stalkTowerLevelEquiv_step (n : ℕ) :
    (stalkTowerLevelEquiv I x n).toRingHom.comp
        ((stalkTower I x).map (homOfLE (Nat.le_add_right n 1)).op).hom =
      (Ideal.Quotient.factorPow (pointIdeal I x) (Nat.le_succ (n + 1))).comp
        (stalkTowerLevelEquiv I x (n + 1)).toRingHom := by
  have hcomp : ((stalkTowerLevelEquiv I x n).toRingHom.comp
        ((stalkTower I x).map (homOfLE (Nat.le_add_right n 1)).op).hom).comp
          (thickeningStalkLocalizationEquiv I x (n + 1)).symm.toRingHom =
      ((Ideal.Quotient.factorPow (pointIdeal I x) (Nat.le_succ (n + 1))).comp
        (stalkTowerLevelEquiv I x (n + 1)).toRingHom).comp
          (thickeningStalkLocalizationEquiv I x (n + 1)).symm.toRingHom := by
    apply IsLocalization.ringHom_ext (levelPrime I x (n + 1)).asIdeal.primeCompl
    apply Ideal.Quotient.ringHom_ext
    refine RingHom.ext fun y => ?_
    -- the two sides, with every coercion written the way the lemmas below state it
    change stalkTowerLevelEquiv I x n
        (((stalkTower I x).map (homOfLE (Nat.le_add_right n 1)).op).hom
          ((thickeningStalkLocalizationEquiv I x (n + 1)).symm
            (algebraMap (R ⧸ I ^ (n + 1 + 1))
              (Localization.AtPrime (levelPrime I x (n + 1)).asIdeal)
              (Ideal.Quotient.mk (I ^ (n + 1 + 1)) y)))) =
      Ideal.Quotient.factorPow (pointIdeal I x) (Nat.le_succ (n + 1))
        (stalkTowerLevelEquiv I x (n + 1)
          ((thickeningStalkLocalizationEquiv I x (n + 1)).symm
            (algebraMap (R ⧸ I ^ (n + 1 + 1))
              (Localization.AtPrime (levelPrime I x (n + 1)).asIdeal)
              (Ideal.Quotient.mk (I ^ (n + 1 + 1)) y))))
    rw [thickeningStalkLocalizationEquiv_symm_algebraMap I x (n + 1)
        (Ideal.Quotient.mk (I ^ (n + 1 + 1)) y),
      stalkTower_map_germ I x n ⊤ trivial]
    have hstep : (stepRingHom I n).hom (Ideal.Quotient.mk (I ^ (n + 1 + 1)) y) =
        Ideal.Quotient.mk (I ^ (n + 1)) y :=
      Ideal.Quotient.factor_mk (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) y
    have hcomap : ((stepSheafHom I n).hom.app (op (⊤ : Opens (FormalSpectrum I)))).hom
        (algebraMap (R ⧸ I ^ (n + 1 + 1))
          ((thickeningSheaf I (n + 1)).presheaf.obj (op ⊤))
          (Ideal.Quotient.mk (I ^ (n + 1 + 1)) y)) =
        algebraMap (R ⧸ I ^ (n + 1)) ((thickeningSheaf I n).presheaf.obj (op ⊤))
          (Ideal.Quotient.mk (I ^ (n + 1)) y) := by
      have h := comap_step_algebraMap I n ⊤ (Ideal.Quotient.mk (I ^ (n + 1 + 1)) y)
      rw [hstep] at h
      exact h
    rw [hcomap, stalkTowerLevelEquiv_germ_mk I x n ⊤ trivial y,
      stalkTowerLevelEquiv_germ_mk I x (n + 1) ⊤ trivial y, Ideal.Quotient.factor_mk]
  refine RingHom.ext fun z => ?_
  obtain ⟨w, rfl⟩ := (thickeningStalkLocalizationEquiv I x (n + 1)).symm.surjective z
  exact DFunLike.congr_fun hcomp w

/-- **The limit of the tower of stalks is the `I`-adic completion of `Localization.AtPrime p`**, for
`p` the prime of `R` under `x`. This is `AdicCompletion.towerLimitRingEquiv` applied to
`FormalSpectrum.stalkTowerLevelEquiv` and `FormalSpectrum.stalkTowerLevelEquiv_step`, and it is the
stalk analogue of `FormalSpectrum.sectionsBasicOpenEquiv`'s use of the same bridge. -/
def stalkTowerLimitEquiv :
    (limit (stalkTower I x) : CommRingCat) ≃+*
      AdicCompletion (pointIdeal I x) (Localization.AtPrime (pointPrime I x)) :=
  AdicCompletion.towerLimitRingEquiv (pointIdeal I x) (stalkTower I x)
    (stalkTowerLevelEquiv I x) (stalkTowerLevelEquiv_step I x)

/-- **The comparison map, read into an adic completion**:
`O_{Spf R, x} ⟶ AdicCompletion (I · R_p) R_p`. It is `FormalSpectrum.stalkToLimit` followed by
`FormalSpectrum.stalkTowerLimitEquiv`, so it is an isomorphism exactly when the comparison is
(`FormalSpectrum.isStalkLimit_iff_bijective_stalkToAdicCompletion`), and nothing here says whether
it is. -/
def stalkToAdicCompletion : (structureSheaf I).presheaf.stalk x →+*
    AdicCompletion (pointIdeal I x) (Localization.AtPrime (pointPrime I x)) :=
  (stalkTowerLimitEquiv I x).toRingHom.comp (stalkToLimit I x).hom

/-- **`FormalSpectrum.IsStalkLimit`, stated over `R`.** The stalk-level comparison of
`FormalSchemes.StructureSheafStalks` is an isomorphism exactly when the explicit map
`O_{Spf R, x} ⟶ AdicCompletion (I · R_p) R_p` is bijective — informally, exactly when the stalk of
the completion is the completion of the stalk.

This is an `Iff` between two statements neither of which is decided on this tree. Its content is
that the right-hand side is written entirely in terms of `R` and a prime of `R`. -/
theorem isStalkLimit_iff_bijective_stalkToAdicCompletion :
    IsStalkLimit I x ↔ Function.Bijective (stalkToAdicCompletion I x) :=
  (isStalkLimit_iff_bijective I x).trans
    ((stalkTowerLimitEquiv I x).bijective.of_comp_iff' _).symm

end FormalSpectrum
