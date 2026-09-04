import FormalSchemes.StructureSheafStalks
import FormalSchemes.LocalizationQuotientPrime

set_option linter.style.header false

/-!
# The levels of the stalk tower are `R_p ⧸ (I · R_p) ^ (n + 1)`

`FormalSchemes.StructureSheafStalks` builds the tower `FormalSpectrum.stalkTower I x` of stalks of
the thickening sheaves at a point `x ∈ Spf R`, the comparison map
`FormalSpectrum.stalkToLimit` from the stalk of `O_{Spf R}`, and
`FormalSpectrum.thickeningStalkLocalizationEquiv`, which presents level `n` as
`Localization.AtPrime` of `R ⧸ I ^ (n + 1)`. This file finishes that identification: level `n` is
`R_p ⧸ (I · R_p) ^ (n + 1)`, for **one** prime `p` of `R` independent of the level.

The point is the independence. `FormalSpectrum.levelPrime I x n` is a prime of a different ring for
each `n`, so on its own it cannot be the level description a tower needs. What makes the levels a
tower over a fixed base is that all of these primes lie over the single prime
`FormalSpectrum.pointPrime I x` of `R`, which is `FormalSpectrum.comap_mk_toThickening` — the
statement that the thickening homeomorphisms are compatible with the closed embeddings into
`Spec R`. That is what `FormalSpectrum.levelPrime_comap` records, and it is the hypothesis
`Localization.atPrimeQuotientEquiv` is phrased to take.

This is the stalk analogue of `FormalSpectrum.basicOpenLevelEquiv` (`FormalSchemes.Sections`),
which does the same for the tower of sections over a basic open, with
`FormalSchemes.LocalizationQuotient`'s `Away` statement in place of this file's prime-complement
one.

## Main definitions and results

* `FormalSpectrum.pointPrime`: the prime of `R` under a point of `Spf R`, i.e. the underlying ideal
  of `FormalSpectrum.toPrimeSpectrum`, together with `FormalSpectrum.le_pointPrime` saying it
  contains the ideal of definition.
* `FormalSpectrum.levelPrime_comap`: `FormalSpectrum.levelPrime I x n` lies over
  `FormalSpectrum.pointPrime I x`, for every `n`.
* `FormalSpectrum.pointIdeal`: the extension `I · R_p` of the ideal of definition to
  `Localization.AtPrime (pointPrime I x)`.
* `FormalSpectrum.stalkTowerLevelEquiv`: **level `n` of `FormalSpectrum.stalkTower` is**
  `R_p ⧸ (I · R_p) ^ (n + 1)`.

## What is *not* proved here

**The compatibility of `FormalSpectrum.stalkTowerLevelEquiv` with the transition maps of the
tower.** `AdicCompletion.towerLimitRingEquiv` takes a level identification *and* a proof that it
intertwines the tower's transition maps with `Ideal.Quotient.factorPow`; this file supplies the
first and not the second, so it does **not** identify `limit (stalkTower I x)` with an adic
completion, and nothing below should be read as doing so.

That missing half is not a formality. Its analogue for sections,
`FormalSpectrum.basicOpenLevelEquiv_step`, is proved by `IsLocalization.ringHom_ext` from
`FormalSpectrum.comap_step_algebraMap`, which describes the transition map of the tower of
*sections* on the image of the quotient ring. The corresponding description at a stalk needs the
naturality of `FormalSpectrum.thickeningStalkIso` in `n`, and no declaration on this tree provides
it: that isomorphism is built at each level separately, out of
`TopCat.Presheaf.stalkCongr` and `TopCat.Presheaf.stalkPushforward` along the level's own
thickening homeomorphism, and relating two levels means comparing two different such homeomorphisms.

**Whether `FormalSpectrum.stalkToLimit` is an isomorphism.** Unchanged by this file, and still
undecided on this tree in both directions. Identifying the levels of the target says what the
question is *about*; it does not answer it.
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

This is `FormalSpectrum.comap_mk_toThickening` read on underlying ideals, and it is the reason the
levels of `FormalSpectrum.stalkTower` can be described over a single localization of `R`: without
it, each level would be a localization of a different ring at an unrelated prime. -/
theorem levelPrime_comap (n : ℕ) :
    (levelPrime I x n).asIdeal.comap (Ideal.Quotient.mk (I ^ (n + 1))) = pointPrime I x :=
  congrArg PrimeSpectrum.asIdeal (comap_mk_toThickening I (n + 1) n.succ_ne_zero x)

/-! ### The levels of the stalk tower -/

/-- The extension `I · R_p` of the ideal of definition to the localization of `R` at the prime
under `x`. This is the ideal whose adic completion the stalk-level limit would be, were the level
identifications below known to be compatible with the tower's transition maps; see the module
docstring for why they are not. -/
def pointIdeal : Ideal (Localization.AtPrime (pointPrime I x)) :=
  I.map (algebraMap R (Localization.AtPrime (pointPrime I x)))

/-- **Level `n` of the stalk tower is `R_p ⧸ (I · R_p) ^ (n + 1)`**, where `p` is the prime of `R`
under `x`.

Three steps: `FormalSpectrum.thickeningStalkLocalizationEquiv` presents the level as
`Localization.AtPrime` of `R ⧸ I ^ (n + 1)`; `Localization.atPrimeQuotientEquiv` turns that into a
quotient of `Localization.AtPrime (pointPrime I x)`, using `FormalSpectrum.levelPrime_comap` to
supply the prime below; and `Ideal.map_pow` rewrites the extension of `I ^ (n + 1)` as the
`(n + 1)`-st power of the extension of `I`.

This is the level identification an adic-completion description of `limit (stalkTower I x)` would
need, **but not the whole of it**: the compatibility with the tower's transition maps is not proved
here, and without it `AdicCompletion.towerLimitRingEquiv` does not apply. -/
def stalkTowerLevelEquiv (n : ℕ) :
    ((stalkTower I x).obj ⟨n⟩ : Type u) ≃+*
      Localization.AtPrime (pointPrime I x) ⧸ pointIdeal I x ^ (n + 1) :=
  (thickeningStalkLocalizationEquiv I x n).trans
    ((Localization.atPrimeQuotientEquiv (I ^ (n + 1)) (levelPrime I x n).asIdeal
        (pointPrime I x) (levelPrime_comap I x n)).trans
      (Ideal.quotEquivOfEq (by rw [pointIdeal, Ideal.map_pow])))

end FormalSpectrum
