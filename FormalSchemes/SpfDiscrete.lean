import FormalSchemes.AdicCofinalOpenImmersion
import FormalSchemes.IndSchemeThickening
import FormalSchemes.SpfGammaRoundTrip
import FormalSchemes.ThickeningCocone
import FormalSchemes.ThickeningHomExt

set_option linter.style.header false

/-!
# An affine scheme is the formal spectrum of its ring, taken discrete (EGA I, 10.1.6)

An ordinary affine scheme is a formal scheme: `Spec A` is `Spf` of the adic ring `(A, ⊥)`, whose
topology is discrete. `FormalSchemes/AdicRing.lean` already records the ring-theoretic half —
`AdicRing.instIsAdicRingBotOfDiscreteTopology` makes a discrete ring adic with ideal of definition
`⊥` — but nothing on the tree identified the two locally ringed spaces. This file does.

The identification is `FormalSpectrum.thickeningMap (⊥ : Ideal A) 0` itself: the canonical morphism
`Spec (A ⧸ ⊥ ^ 1) ⟶ Spf ⊥` out of the zeroth infinitesimal thickening. Every thickening of `⊥` is
already the whole ring, so that morphism is an isomorphism, and no sheaf-level work is needed to
see it:

* its **inverse** is `(specHomEquiv ⊥ _).symm` of the canonical ring isomorphism `A ⧸ ⊥ ^ 1 ≃+* A`
  — the affine-target universal property `FormalSpectrum.specHomEquiv`
  (`FormalSchemes/IndScheme.lean`) supplies morphisms *into* an affine scheme for free;
* one round trip is a computation with ring maps, through
  `FormalSpectrum.thickeningMap_comp_specHomEquiv_symm` (`FormalSchemes/IndSchemeThickening.lean`);
* the other is `FormalSpectrum.hom_ext_thickeningMap_lrs` (`FormalSchemes/ThickeningHomExt.lean`),
  which has **no hypothesis on the target**, against
  `FormalSpectrum.specMap_factor_comp_thickeningMap` (`FormalSchemes/ThickeningCocone.lean`).

## Why this is worth a file: it moves `Spec`-shaped sources onto `Spf`-shaped ones

Issue 62m's goal 2 is the surjectivity of
`FormalSpectrum.restrictToThickeningsLRS I (locallyRingedSpaceObj L)`
(`FormalSchemes/SpfTargetColimit.lean`): a compatible family `Spec (R ⧸ I ^ (n + 1)) ⟶ Spf L`
comes from a morphism `Spf R ⟶ Spf L`. The family's members have **`Spec`-shaped sources**, while
every rigidity statement this tree owns about a formal-affine *target* has a **`Spf`-shaped
source**: `FormalSpectrum.map_le_radical_of_hom` (`FormalSchemes/AdicCofinalOpenImmersion.lean`)
and `FormalSpectrum.locallyRingedSpaceMap_globalSectionsMap`
(`FormalSchemes/SpfGammaRoundTrip.lean`) are both stated for a morphism `Spf S ⟶ Spf R`. The
isomorphism below is exactly what applies them to a family member, and the last section does so:

* `FormalSpectrum.exists_pow_map_eq_bot_of_specHom` — the global-sections map of a morphism
  `Spec A ⟶ Spf L` out of a **discrete** `A` kills a power of `L`. This is #418's nilpotence half,
  read at `J = ⊥`, where `Ideal.radical ⊥` is the nilradical.
* `FormalSpectrum.hom_ext_specHom` — a morphism `Spec A ⟶ Spf L` whose global-sections map carries
  `L` to `0` is determined by that ring map. This is the round trip read at `J = ⊥`.

Together those two are the shape "a morphism out of an affine scheme into `Spf L` is a continuous
ring map, up to replacing `L` by a power" — the statement the issue-156 counterexample bounds from
below, and which `FormalSpectrum.cofinalSpfIso`
(`FormalSchemes/CofinalSheafComparisonIso.lean`) is what absorbs.

## What is *not* proved here

* Goal 2 of issue 62m itself. Nothing below builds a morphism `Spf R ⟶ Spf L` from a family, and
  no statement of this file mentions `restrictToThickeningsLRS`.
* Naturality of `specIsoSpfBot` in `A`. `specGlobalSectionsMap` is therefore not yet known to be
  compatible with precomposition by `Spec` of a ring map, which is what a *family* — as opposed to
  a single morphism — will need in order to produce a compatible system of ring maps.
* Any statement about a `Spf`-target *cover*: this is the single formal-affine target `Spf L`.

## Main definitions and results

* `FormalSpectrum.botQuotEquiv`: the canonical `A ⧸ ⊥ ^ (n + 1) ≃+* A`.
* `FormalSpectrum.spfBotToSpec`: the inverse morphism, from the affine-target universal property.
* `FormalSpectrum.isIso_thickeningMap_bot_zero`: `thickeningMap (⊥ : Ideal A) 0` is an isomorphism.
* `FormalSpectrum.specIsoSpfBot`: **`Spec A ≅ Spf (⊥ : Ideal A)`** for a discrete `A`.
* `FormalSpectrum.specGlobalSectionsMap`, `FormalSpectrum.exists_pow_map_eq_bot_of_specHom`,
  `FormalSpectrum.hom_ext_specHom`: the two transports described above.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1 (10.1.6), §10.4.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FormalSpectrum

section Bot

variable (A : Type u) [CommRing A]

/-- The canonical isomorphism `A ⧸ ⊥ ^ (n + 1) ≃+* A`: every infinitesimal thickening of the zero
ideal is the ring itself, since `⊥ ^ (n + 1) = ⊥`. -/
def botQuotEquiv (n : ℕ) : (A ⧸ (⊥ : Ideal A) ^ (n + 1)) ≃+* A :=
  (Ideal.quotEquivOfEq (Ideal.bot_pow n.succ_ne_zero)).trans (RingEquiv.quotientBot A)

@[simp]
theorem botQuotEquiv_mk (n : ℕ) (x : A) :
    botQuotEquiv A n (Ideal.Quotient.mk ((⊥ : Ideal A) ^ (n + 1)) x) = x := by
  rw [botQuotEquiv]
  simp

/-- The level-`n` section of the tower of thickenings of `⊥`: the inverse of the tower map
`A ⧸ ⊥ ^ (n + 1) →+* A ⧸ ⊥ ^ 1`, spelled as reduction of the isomorphism `botQuotEquiv A 0`. -/
def botLevelHom (n : ℕ) : (A ⧸ (⊥ : Ideal A) ^ (0 + 1)) →+* (A ⧸ (⊥ : Ideal A) ^ (n + 1)) :=
  (Ideal.Quotient.mk ((⊥ : Ideal A) ^ (n + 1))).comp (botQuotEquiv A 0).toRingHom

/-- `botLevelHom A n` is a section of the tower map `A ⧸ ⊥ ^ (n + 1) →+* A ⧸ ⊥ ^ 1`, on the side
that matters below: precomposing it with that map is the identity of `A ⧸ ⊥ ^ (n + 1)`. -/
theorem botLevelHom_comp_factor (n : ℕ) :
    (botLevelHom A n).comp (Ideal.Quotient.factor (Ideal.pow_le_pow_right (I := (⊥ : Ideal A))
      (Nat.add_le_add_right (Nat.zero_le n) 1))) = RingHom.id (A ⧸ (⊥ : Ideal A) ^ (n + 1)) :=
  Ideal.Quotient.ringHom_ext (by ext x; simp [botLevelHom, Ideal.Quotient.factor_mk])

/-- At level `0` the section is the identity. -/
theorem botLevelHom_zero : botLevelHom A 0 = RingHom.id (A ⧸ (⊥ : Ideal A) ^ (0 + 1)) :=
  Ideal.Quotient.ringHom_ext (by ext x; simp [botLevelHom])

variable [TopologicalSpace A] [DiscreteTopology A]

/-- The candidate inverse of `thickeningMap (⊥ : Ideal A) 0`: the morphism
`Spf ⊥ ⟶ Spec (A ⧸ ⊥ ^ 1)` corresponding, under the affine-target universal property
`specHomEquiv`, to the canonical ring isomorphism `A ⧸ ⊥ ^ 1 ≃+* A`. -/
def spfBotToSpec :
    locallyRingedSpaceObj (⊥ : Ideal A) ⟶
      Spec.locallyRingedSpaceObj (CommRingCat.of (A ⧸ (⊥ : Ideal A) ^ (0 + 1))) :=
  (specHomEquiv (⊥ : Ideal A) (A ⧸ (⊥ : Ideal A) ^ (0 + 1))).symm (botQuotEquiv A 0).toRingHom

/-- The restriction of `spfBotToSpec` to the `n`-th thickening is `Spec` of `botLevelHom A n`.
This is `thickeningMap_comp_specHomEquiv_symm` at the ring isomorphism defining `spfBotToSpec`. -/
theorem thickeningMap_comp_spfBotToSpec (n : ℕ) :
    thickeningMap (⊥ : Ideal A) n ≫ spfBotToSpec A =
      Spec.locallyRingedSpaceMap (CommRingCat.ofHom (botLevelHom A n)) :=
  thickeningMap_comp_specHomEquiv_symm _ _ _ _

omit [TopologicalSpace A] [DiscreteTopology A] in
/-- `Spec` of the section `botLevelHom A n`, followed by the canonical morphism out of the zeroth
thickening, is the canonical morphism out of the `n`-th one. This is the general cocone identity
`specMap_factor_comp_thickeningMap` composed with the section identity
`botLevelHom_comp_factor`. -/
theorem specMap_botLevelHom_comp_thickeningMap (n : ℕ) :
    Spec.locallyRingedSpaceMap (CommRingCat.ofHom (botLevelHom A n)) ≫
      thickeningMap (⊥ : Ideal A) 0 = thickeningMap (⊥ : Ideal A) n := by
  rw [← specMap_factor_comp_thickeningMap (⊥ : Ideal A) (Nat.zero_le n), ← Category.assoc,
    ← Spec.locallyRingedSpaceMap_comp, ← CommRingCat.ofHom_comp, botLevelHom_comp_factor,
    CommRingCat.ofHom_id, Spec.locallyRingedSpaceMap_id, Category.id_comp]

/-- First round trip: `Spec (A ⧸ ⊥ ^ 1) ⟶ Spf ⊥ ⟶ Spec (A ⧸ ⊥ ^ 1)` is the identity. It is
`Spec` of `botLevelHom A 0`, which is the identity ring map. -/
theorem thickeningMap_zero_comp_spfBotToSpec :
    thickeningMap (⊥ : Ideal A) 0 ≫ spfBotToSpec A = 𝟙 _ := by
  rw [thickeningMap_comp_spfBotToSpec, botLevelHom_zero, CommRingCat.ofHom_id,
    Spec.locallyRingedSpaceMap_id]

/-- Second round trip: `Spf ⊥ ⟶ Spec (A ⧸ ⊥ ^ 1) ⟶ Spf ⊥` is the identity. Both sides are
morphisms out of `Spf ⊥`, so `hom_ext_thickeningMap_lrs` reduces the claim to their restrictions
to the thickenings, and there it is `specMap_botLevelHom_comp_thickeningMap`. -/
theorem spfBotToSpec_comp_thickeningMap_zero :
    spfBotToSpec A ≫ thickeningMap (⊥ : Ideal A) 0 = 𝟙 _ :=
  hom_ext_thickeningMap_lrs _ _ fun n => by
    rw [← Category.assoc, thickeningMap_comp_spfBotToSpec,
      specMap_botLevelHom_comp_thickeningMap, Category.comp_id]

/-- **The zeroth thickening of a discrete ring is its formal spectrum.** -/
instance isIso_thickeningMap_bot_zero : IsIso (thickeningMap (⊥ : Ideal A) 0) :=
  ⟨spfBotToSpec A, thickeningMap_zero_comp_spfBotToSpec A, spfBotToSpec_comp_thickeningMap_zero A⟩

omit [TopologicalSpace A] [DiscreteTopology A] in
/-- `Spec A ≅ Spec (A ⧸ ⊥ ^ 1)`, from `botQuotEquiv A 0`. -/
def specBotQuotIso :
    Spec.locallyRingedSpaceObj (CommRingCat.of A) ≅
      Spec.locallyRingedSpaceObj (CommRingCat.of (A ⧸ (⊥ : Ideal A) ^ (0 + 1))) where
  hom := Spec.locallyRingedSpaceMap (CommRingCat.ofHom (botQuotEquiv A 0).toRingHom)
  inv := Spec.locallyRingedSpaceMap (CommRingCat.ofHom (botQuotEquiv A 0).symm.toRingHom)
  hom_inv_id := by
    rw [← Spec.locallyRingedSpaceMap_comp, ← CommRingCat.ofHom_comp,
      show ((botQuotEquiv A 0).toRingHom.comp (botQuotEquiv A 0).symm.toRingHom) =
        RingHom.id A from RingHom.ext fun x => (botQuotEquiv A 0).apply_symm_apply x,
      CommRingCat.ofHom_id, Spec.locallyRingedSpaceMap_id]
  inv_hom_id := by
    rw [← Spec.locallyRingedSpaceMap_comp, ← CommRingCat.ofHom_comp,
      show ((botQuotEquiv A 0).symm.toRingHom.comp (botQuotEquiv A 0).toRingHom) =
        RingHom.id (A ⧸ (⊥ : Ideal A) ^ (0 + 1)) from
          RingHom.ext fun x => (botQuotEquiv A 0).symm_apply_apply x,
      CommRingCat.ofHom_id, Spec.locallyRingedSpaceMap_id]

/-- **An affine scheme is the formal spectrum of its ring, taken discrete** (EGA I, 10.1.6):
for a ring `A` carrying the discrete topology — so that `IsAdicRing (⊥ : Ideal A)` holds —
`Spec A` is isomorphic, as a locally ringed space, to `Spf (A, ⊥)`. -/
def specIsoSpfBot :
    Spec.locallyRingedSpaceObj (CommRingCat.of A) ≅ locallyRingedSpaceObj (⊥ : Ideal A) :=
  specBotQuotIso A ≪≫ asIso (thickeningMap (⊥ : Ideal A) 0)

end Bot

section SpecSource

variable {C : Type u} [CommRing C] [TopologicalSpace C] (L : Ideal C) [IsAdicRing L]
variable (A : Type u) [CommRing A] [TopologicalSpace A] [DiscreteTopology A]

/-- The global-sections ring homomorphism `C →+* A` of a morphism `Spec A ⟶ Spf L` out of an
ordinary affine scheme with `A` discrete: `globalSectionsMap` read through `specIsoSpfBot`. -/
def specGlobalSectionsMap
    (u : Spec.locallyRingedSpaceObj (CommRingCat.of A) ⟶ locallyRingedSpaceObj L) : C →+* A :=
  globalSectionsMap L (⊥ : Ideal A) ((specIsoSpfBot A).inv ≫ u)

/-- **The global-sections map of a morphism out of an affine scheme kills a power of the ideal of
definition.** For `L` finitely generated and `A` discrete, a morphism `Spec A ⟶ Spf L` sends
`L ^ k` to `0` for some `k`.

This is `exists_pow_map_le_of_hom` (`FormalSchemes/AdicCofinalOpenImmersion.lean`, issue 62k) at
`J = ⊥`, transported along `specIsoSpfBot`: the containment `L · A ≤ Ideal.radical ⊥` of that
theorem is the statement that the image of `L` consists of nilpotents, and a finitely generated
ideal of nilpotents is nilpotent. No hypothesis on the morphism is used. -/
theorem exists_pow_map_eq_bot_of_specHom [Algebra C A] (hL : L.FG)
    (u : Spec.locallyRingedSpaceObj (CommRingCat.of A) ⟶ locallyRingedSpaceObj L)
    (halg : algebraMap C A = specGlobalSectionsMap L A u) :
    ∃ k : ℕ, (L ^ k).map (algebraMap C A) = ⊥ := by
  obtain ⟨k, hk⟩ := exists_pow_map_le_of_hom L (⊥ : Ideal A) hL
    ((specIsoSpfBot A).inv ≫ u) halg
  exact ⟨k, le_bot_iff.mp (by rwa [Ideal.map_pow])⟩

/-- **A morphism out of an affine scheme into `Spf L` is determined by its global-sections map**,
provided that map carries `L` to `0`. This is the Spf–Γ round trip
`locallyRingedSpaceMap_globalSectionsMap` (`FormalSchemes/SpfGammaRoundTrip.lean`, issue 96) at
`J = ⊥`, transported along `specIsoSpfBot`.

The hypothesis that the ring map kills `L` on the nose is exactly the continuity hypothesis of the
round trip, and it is not automatic: `exists_pow_map_eq_bot_of_specHom` gives it only for a power
of `L`. That gap is the issue-156 phenomenon, and the ideal-of-definition slack
`FormalSpectrum.cofinalSpfIso` is what a consumer uses to close it. -/
theorem hom_ext_specHom (hL : L.FG)
    (u v : Spec.locallyRingedSpaceObj (CommRingCat.of A) ⟶ locallyRingedSpaceObj L)
    (hu : L ≤ (⊥ : Ideal A).comap (specGlobalSectionsMap L A u))
    (hv : L ≤ (⊥ : Ideal A).comap (specGlobalSectionsMap L A v))
    (h : specGlobalSectionsMap L A u = specGlobalSectionsMap L A v) : u = v := by
  have key : (specIsoSpfBot A).inv ≫ u = (specIsoSpfBot A).inv ≫ v := by
    rw [← locallyRingedSpaceMap_globalSectionsMap L (⊥ : Ideal A) hL Submodule.fg_bot
        ((specIsoSpfBot A).inv ≫ u) hu,
      ← locallyRingedSpaceMap_globalSectionsMap L (⊥ : Ideal A) hL Submodule.fg_bot
        ((specIsoSpfBot A).inv ≫ v) hv]
    exact locallyRingedSpaceMap_congr L (⊥ : Ideal A) _ _ hu hv h
  exact (cancel_epi (specIsoSpfBot A).inv).mp key

end SpecSource

end FormalSpectrum

end
