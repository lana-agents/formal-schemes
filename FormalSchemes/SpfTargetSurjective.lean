import FormalSchemes.CofinalStructMap
import FormalSchemes.CompletionToSpec
import FormalSchemes.SpfDiscrete
import FormalSchemes.SpfTargetColimit

set_option linter.style.header false

/-!
# The `Spf`-target colimit property at an affine target (EGA I, 10.6.7), issue 62m goal 2

`FormalSchemes/SpfTargetColimit.lean` reduces the `Spf`-shaped analogue of EGA I 10.6.10 — the
colimit property of `Spf R` at a target covered by **formal** affines — at the smallest instance,
the single target `Spf L`, to one statement:

```lean
Function.Surjective (FormalSpectrum.restrictToThickeningsLRS I (locallyRingedSpaceObj L))
```

i.e. a compatible family `Spec (R ⧸ Iⁿ⁺¹) ⟶ Spf L` comes from a morphism `Spf R ⟶ Spf L`.
Injectivity is `injective_restrictToThickeningsLRS` and is free. This file proves the surjectivity,
for `L` finitely generated and with no hypothesis on `I` beyond `IsAdicRing I`, and packages the
resulting bijection and `∃!`.

## Why the routes recorded in `SpfTargetColimit.lean` did not close, and what does

That file lists three routes and diagnoses all three as blocked on a continuity hypothesis: a
morphism of locally ringed spaces `Spec (R ⧸ Iⁿ⁺¹) ⟶ Spf L` supplies no ring map, and the tree's
`Spf`-target rigidity theorems — `FormalSpectrum.locallyRingedSpaceMap_globalSectionsMap`
(`FormalSchemes/SpfGammaRoundTrip.lean`) and `FormalSpectrum.map_le_radical_of_hom`
(`FormalSchemes/AdicCofinalOpenImmersion.lean`) — are stated for a morphism `Spf S ⟶ Spf R`.

The gap is one of **shape**, and `FormalSpectrum.specIsoSpfBot` (`FormalSchemes/SpfDiscrete.lean`)
closes it: an ordinary affine scheme is `Spf` of its own ring taken discrete, so both theorems apply
to a family member after all. What they give, in the two forms this file consumes them in:

* `FormalSpectrum.exists_pow_map_eq_bot_of_comp_toSpecAmbient` — the ring map of a morphism
  `Spec A ⟶ Spf L` kills a **power** of `L`. At the level-0 member of a family this is exactly
  `ψ (L ^ k) ⊆ I`, the containment route 2 of `SpfTargetColimit.lean` records as unavailable.
* `FormalSpectrum.hom_ext_of_comp_toSpecAmbient` — a morphism `Spec A ⟶ Spf L` is determined by
  that ring map, once the map kills `L` on the nose.

The nose-versus-power gap is the issue-156 phenomenon, and `FormalSpectrum.cofinalSpfIso`
(`FormalSchemes/CofinalSheafComparisonIso.lean`) absorbs it: the morphism produced here is built at
`Spf (L ^ (k + 1))` and transported to `Spf L` along that isomorphism.

## The one place the argument is not bookkeeping

The continuity power is **not uniform in the level**. From `ψ (L ^ (k + 1)) ⊆ I` one gets
`ψ (L ^ ((k + 1) · (m + 1))) ⊆ I ^ (m + 1)`, so the comparison at level `m` has to be made at the
target `Spf (L ^ ((k + 1) · (m + 1)))` rather than at the single `Spf (L ^ (k + 1))` where the
morphism was built. That is what `cofinalSpfIso_hom_comp_toSpecAmbient` and
`cofinalSpfIso_inv_comp_toSpecAmbient` are for: both legs of a cofinal comparison act as the
identity on global sections, so composing with `toSpecAmbient` is insensitive to which power one
is at, and the level-`m` comparison can be made at whichever power is convenient.

## What is *not* proved here

* **The `Spf`-target theorem at a target with a formal-affine cover** — issue 62m's goal 3. This is
  the affine case only, i.e. the single target `Spf L`. Steps 4 and 5 of that row
  (`FormalSchemes/ChartSpfHomIndep.lean`, `FormalSchemes/ChartSpfHomOverlap.lean`) are untouched.
* Anything about issue 1197 or the Tate quotient. The circularity question that row raises is not
  addressed and nothing here mentions it.
* Any statement with `I.FG` removed from a theorem that has it, or added to one that does not:
  `surjective_restrictToThickeningsLRS_spf` needs `L.FG` and does **not** need `I.FG`.

## Main definitions and results

* `FormalSpectrum.toSpecAmbient`: the canonical morphism `Spf L ⟶ Spec C`.
* `FormalSpectrum.comp_toSpecAmbient_spec`: composing a morphism out of an affine scheme with it
  is `Spec` of the global-sections ring map — the statement that `specGlobalSectionsMap` is the
  honest one.
* `FormalSpectrum.surjective_restrictToThickeningsLRS_spf`: **issue 62m's goal 2**.
* `FormalSpectrum.thickeningRestrictionEquivSpfOfFG`,
  `FormalSpectrum.existsUnique_hom_thickeningMap_spf`: the bijection and the `∃!`, unconditional
  at a formal-affine target.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6 (10.6.7, 10.6.10).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FormalSpectrum

/-- **`Spec` is faithful into locally ringed spaces**, in the spelling this tree uses. Mathlib's
`Spec.toLocallyRingedSpace` carries the `Faithful` instance, but its `map` is applied to an
`op`-ped morphism; every statement here is phrased with `Spec.locallyRingedSpaceMap`, so the `op`
is peeled off once, here, rather than at each use site. -/
theorem specMap_injective {P Q : CommRingCat.{u}} {f g : P ⟶ Q}
    (h : Spec.locallyRingedSpaceMap f = Spec.locallyRingedSpaceMap g) : f = g :=
  Quiver.Hom.op_inj (Spec.toLocallyRingedSpace.map_injective h)

section Ambient

variable {C : Type u} [CommRing C] [TopologicalSpace C] (L : Ideal C) [IsAdicRing L]

/-- The canonical morphism `Spf L ⟶ Spec C`. -/
def toSpecAmbient : locallyRingedSpaceObj L ⟶ Spec.locallyRingedSpaceObj (CommRingCat.of C) :=
  (specHomEquiv L C).symm (RingHom.id C)

@[simp]
theorem specHomEquiv_toSpecAmbient : specHomEquiv L C (toSpecAmbient L) = RingHom.id C :=
  (specHomEquiv L C).apply_symm_apply _

variable {S : Type u} [CommRing S] [TopologicalSpace S] (J : Ideal S) [IsAdicRing J]

/-- Composing a morphism of formal spectra with `toSpecAmbient` reads off its global-sections
map. -/
theorem comp_toSpecAmbient (u : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj L) :
    u ≫ toSpecAmbient L = (specHomEquiv J C).symm (globalSectionsMap L J u) := by
  refine (Equiv.eq_symm_apply (specHomEquiv J C)).mpr ?_
  rw [specHomEquiv_naturality_left, specHomEquiv_toSpecAmbient, RingHom.comp_id]

end Ambient

section SpecSource

variable {C : Type u} [CommRing C] [TopologicalSpace C] (L : Ideal C) [IsAdicRing L]
variable (A : Type u) [CommRing A] [TopologicalSpace A] [DiscreteTopology A]

omit [TopologicalSpace A] [DiscreteTopology A] in
/-- The isomorphism `A ⧸ ⊥ ^ 1 ≃+* A` inverts the quotient map on the other side too. -/
theorem botQuotEquiv_comp_mk :
    (botQuotEquiv A 0).toRingHom.comp (Ideal.Quotient.mk ((⊥ : Ideal A) ^ (0 + 1))) =
      RingHom.id A :=
  RingHom.ext fun x => botQuotEquiv_mk A 0 x

/-- **`specGlobalSectionsMap` is the honest global-sections map.** For a morphism out of an
ordinary affine scheme with `A` discrete, composing with `toSpecAmbient` gives `Spec` of it. This
is what lets a *family* be turned into a compatible system of ring maps: `Spec` is faithful, so
compatibility of the family transfers to the ring maps without any naturality statement about
`specIsoSpfBot`. -/
theorem comp_toSpecAmbient_spec
    (u : Spec.locallyRingedSpaceObj (CommRingCat.of A) ⟶ locallyRingedSpaceObj L) :
    u ≫ toSpecAmbient L =
      Spec.locallyRingedSpaceMap (CommRingCat.ofHom (specGlobalSectionsMap L A u)) := by
  have h1 : (specIsoSpfBot A).inv ≫ u ≫ toSpecAmbient L =
      (specHomEquiv (⊥ : Ideal A) C).symm (specGlobalSectionsMap L A u) := by
    rw [← Category.assoc, comp_toSpecAmbient]
    rfl
  have h2 : u ≫ toSpecAmbient L =
      (specIsoSpfBot A).hom ≫ (specHomEquiv (⊥ : Ideal A) C).symm
        (specGlobalSectionsMap L A u) := by
    rw [← h1, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  have hhom : (specBotQuotIso A).hom =
      Spec.locallyRingedSpaceMap (CommRingCat.ofHom (botQuotEquiv A 0).toRingHom) := rfl
  rw [h2, specIsoSpfBot, Iso.trans_hom, asIso_hom, Category.assoc,
    thickeningMap_comp_specHomEquiv_symm, hhom, ← Spec.locallyRingedSpaceMap_comp,
    ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, botQuotEquiv_comp_mk, RingHom.id_comp]

/-- `specMap_injective` for ring homomorphisms rather than `CommRingCat` morphisms. -/
theorem specMap_ofHom_injective {P Q : Type u} [CommRing P] [CommRing Q] {f g : P →+* Q}
    (h : Spec.locallyRingedSpaceMap (CommRingCat.ofHom f) =
      Spec.locallyRingedSpaceMap (CommRingCat.ofHom g)) : f = g :=
  congrArg CommRingCat.Hom.hom (specMap_injective h)

end SpecSource

section Cofinal

variable {C : Type u} [CommRing C] [TopologicalSpace C] (M L : Ideal C) [IsAdicRing M]
  [IsAdicRing L] (hML : M ≤ L) (hM : M.FG) (hL : L.FG)

/-- **A cofinal comparison is invisible to `toSpecAmbient`**, backward leg. This is what makes the
level-dependent choice of power harmless: whichever ideal of definition one reads a morphism at,
its composite with `toSpecAmbient` is the same. -/
theorem cofinalSpfIso_inv_comp_toSpecAmbient :
    (cofinalSpfIso M L hML hM hL).inv ≫ toSpecAmbient M = toSpecAmbient L := by
  rw [comp_toSpecAmbient, globalSectionsMap_cofinalSpfIso_inv, toSpecAmbient]

/-- The same, forward leg. -/
theorem cofinalSpfIso_hom_comp_toSpecAmbient :
    (cofinalSpfIso M L hML hM hL).hom ≫ toSpecAmbient L = toSpecAmbient M := by
  rw [comp_toSpecAmbient, globalSectionsMap_cofinalSpfIso_hom, toSpecAmbient]

end Cofinal

section Discrete

variable {C : Type u} [CommRing C] [TopologicalSpace C] (L : Ideal C) [IsAdicRing L]
variable (A : Type u) [CommRing A]

/-- Every morphism `Spec A ⟶ Spf L` composes with `toSpecAmbient` to `Spec` of a ring map. -/
theorem exists_ringHom_comp_toSpecAmbient
    (u : Spec.locallyRingedSpaceObj (CommRingCat.of A) ⟶ locallyRingedSpaceObj L) :
    ∃ φ : C →+* A, u ≫ toSpecAmbient L =
      Spec.locallyRingedSpaceMap (CommRingCat.ofHom φ) := by
  letI : TopologicalSpace A := ⊥
  haveI : DiscreteTopology A := ⟨rfl⟩
  exact ⟨specGlobalSectionsMap L A u, comp_toSpecAmbient_spec L A u⟩

/-- That ring map kills a power of `L`. -/
theorem exists_pow_map_eq_bot_of_comp_toSpecAmbient (hL : L.FG)
    (u : Spec.locallyRingedSpaceObj (CommRingCat.of A) ⟶ locallyRingedSpaceObj L) (φ : C →+* A)
    (h : u ≫ toSpecAmbient L = Spec.locallyRingedSpaceMap (CommRingCat.ofHom φ)) :
    ∃ k : ℕ, (L ^ k).map φ = ⊥ := by
  letI : TopologicalSpace A := ⊥
  haveI : DiscreteTopology A := ⟨rfl⟩
  have hφ : specGlobalSectionsMap L A u = φ :=
    specMap_ofHom_injective ((comp_toSpecAmbient_spec L A u).symm.trans h)
  letI : Algebra C A := φ.toAlgebra
  have halg : algebraMap C A = specGlobalSectionsMap L A u := hφ.symm
  obtain ⟨k, hk⟩ := exists_pow_map_eq_bot_of_specHom L A hL u halg
  exact ⟨k, hk⟩

/-- And it determines the morphism, once it kills `L` on the nose. -/
theorem hom_ext_of_comp_toSpecAmbient (hL : L.FG)
    (u v : Spec.locallyRingedSpaceObj (CommRingCat.of A) ⟶ locallyRingedSpaceObj L) (φ : C →+* A)
    (hmap : L.map φ = ⊥)
    (hu : u ≫ toSpecAmbient L = Spec.locallyRingedSpaceMap (CommRingCat.ofHom φ))
    (hv : v ≫ toSpecAmbient L = Spec.locallyRingedSpaceMap (CommRingCat.ofHom φ)) : u = v := by
  letI : TopologicalSpace A := ⊥
  haveI : DiscreteTopology A := ⟨rfl⟩
  have hφu : specGlobalSectionsMap L A u = φ :=
    specMap_ofHom_injective ((comp_toSpecAmbient_spec L A u).symm.trans hu)
  have hφv : specGlobalSectionsMap L A v = φ :=
    specMap_ofHom_injective ((comp_toSpecAmbient_spec L A v).symm.trans hv)
  have hcont : L ≤ (⊥ : Ideal A).comap φ := Ideal.map_le_iff_le_comap.mp hmap.le
  exact hom_ext_specHom L A hL u v (hφu ▸ hcont) (hφv ▸ hcont) (hφu.trans hφv.symm)

end Discrete

section Family

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable {C : Type u} [CommRing C] [TopologicalSpace C] (L : Ideal C) [IsAdicRing L]

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The level ring maps of a family.** Each member of a `ThickeningFamilyLRS` into `Spf L` has a
global-sections ring map `C →+* R ⧸ Iⁿ⁺¹`, characterised by its composite with `toSpecAmbient`. -/
theorem exists_levelHom (F : ThickeningFamilyLRS I (locallyRingedSpaceObj L)) :
    ∃ φ : ∀ n : ℕ, C →+* R ⧸ I ^ (n + 1), ∀ n : ℕ,
      F.1 n ≫ toSpecAmbient L = Spec.locallyRingedSpaceMap (CommRingCat.ofHom (φ n)) :=
  ⟨fun n => (exists_ringHom_comp_toSpecAmbient L _ (F.1 n)).choose,
    fun n => (exists_ringHom_comp_toSpecAmbient L _ (F.1 n)).choose_spec⟩

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **They form a compatible system.** The family's own compatibility, pushed through
`toSpecAmbient` and faithfulness of `Spec`. -/
theorem levelHom_compat (F : ThickeningFamilyLRS I (locallyRingedSpaceObj L))
    (φ : ∀ n : ℕ, C →+* R ⧸ I ^ (n + 1))
    (hφ : ∀ n : ℕ, F.1 n ≫ toSpecAmbient L =
      Spec.locallyRingedSpaceMap (CommRingCat.ofHom (φ n))) (n : ℕ) :
    (stepRingHom I n).hom.comp (φ (n + 1)) = φ n := by
  refine specMap_ofHom_injective ?_
  rw [CommRingCat.ofHom_comp, Spec.locallyRingedSpaceMap_comp, ← hφ (n + 1), ← Category.assoc]
  rw [show CommRingCat.ofHom (CommRingCat.Hom.hom (stepRingHom I n)) = stepRingHom I n from rfl,
    F.2 n, hφ n]

/-- The level maps re-indexed for `existsUnique_thickeningMap_comp`, whose tower is `R ⧸ Iⁿ`
rather than `R ⧸ Iⁿ⁺¹`. Level `0` is filled in from level `1`; `R ⧸ I ^ 0` is the zero ring, so
nothing is chosen there. -/
def towerHom (φ : ∀ n : ℕ, C →+* R ⧸ I ^ (n + 1)) : ∀ n : ℕ, C →+* R ⧸ I ^ n
  | 0 => (Ideal.Quotient.factorPow I (Nat.zero_le 1)).comp (φ 0)
  | (n + 1) => φ n

omit [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace C] in
/-- The re-indexed system is compatible, in the `factorPow` spelling that
`existsUnique_thickeningMap_comp` asks for. -/
theorem towerHom_compat (φ : ∀ n : ℕ, C →+* R ⧸ I ^ (n + 1))
    (hφ : ∀ n : ℕ, (stepRingHom I n).hom.comp (φ (n + 1)) = φ n) (n : ℕ) :
    (Ideal.Quotient.factorPow I (Nat.le_succ n)).comp (towerHom I φ (n + 1)) =
      towerHom I φ n := by
  cases n with
  | zero => rfl
  | succ m => exact hφ m

omit [TopologicalSpace C] in
/-- **The limit ring homomorphism.** A compatible system of ring maps `C →+* R ⧸ Iⁿ⁺¹` comes from a
single `ψ : C →+* R`, because `R` is `I`-adically complete. This is the landed affine-target
existence theorem `existsUnique_thickeningMap_comp` together with `specHomEquiv`; no continuity is
involved, and none is available at this point. -/
theorem exists_ringHom_of_levelHom (φ : ∀ n : ℕ, C →+* R ⧸ I ^ (n + 1))
    (hφ : ∀ n : ℕ, (stepRingHom I n).hom.comp (φ (n + 1)) = φ n) :
    ∃ ψ : C →+* R, ∀ n : ℕ, (Ideal.Quotient.mk (I ^ (n + 1))).comp ψ = φ n := by
  obtain ⟨g, hg, -⟩ :=
    existsUnique_thickeningMap_comp I C (towerHom I φ) (towerHom_compat I φ hφ)
  refine ⟨specHomEquiv I C g, fun n => ?_⟩
  exact specMap_ofHom_injective ((thickeningMap_comp_specHom I C g n).symm.trans (hg n))

/-- **Issue 62m, goal 2: the `Spf`-target colimit property at an affine target** (EGA I, 10.6.7).
A compatible family of morphisms `Spec (R ⧸ Iⁿ⁺¹) ⟶ Spf L` out of the infinitesimal thickenings of
`Spf R` comes from a morphism `Spf R ⟶ Spf L`.

The morphism is `Spf ψ` for the limit `ψ : C →+* R` of the family's level ring maps, transported
from `Spf (L ^ (k + 1))` to `Spf L` along `cofinalSpfIso`. The power is unavoidable and is not an
artefact of the proof: `FormalSpectrum.cofinalSpfIso` at `L` versus `L ^ 2` over `k⟦y⟧` is the
issue-156 counterexample to the on-the-nose statement, so a morphism out of `Spf R` cannot in
general be `Spf` of a homomorphism continuous for `L` itself.

`I.FG` is **not** needed: the only finiteness used is `L.FG`, and it is used exactly once, to turn
"the image of `L` consists of nilpotents" into "`L ^ k` maps to zero". -/
theorem surjective_restrictToThickeningsLRS_spf (hL : L.FG) :
    Function.Surjective (restrictToThickeningsLRS I (locallyRingedSpaceObj L)) := by
  intro F
  obtain ⟨φ, hφ⟩ := exists_levelHom I L F
  obtain ⟨ψ, hψ⟩ := exists_ringHom_of_levelHom I φ (levelHom_compat I L F φ hφ)
  obtain ⟨k, hk⟩ := exists_pow_map_eq_bot_of_comp_toSpecAmbient L (R ⧸ I ^ (0 + 1)) hL
    (F.1 0) (φ 0) (hφ 0)
  have h0 : (L ^ (k + 1)).map ψ ≤ I ^ (0 + 1) := by
    rw [← hψ 0, ← Ideal.map_map] at hk
    have h := (Ideal.map_eq_bot_iff_le_ker _).mp hk
    rw [Ideal.mk_ker] at h
    exact le_trans (Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ k))) h
  have hmapψ : ∀ m : ℕ, (L ^ ((k + 1) * (m + 1))).map ψ ≤ I ^ (m + 1) := by
    intro m
    rw [pow_mul, Ideal.map_pow]
    calc ((L ^ (k + 1)).map ψ) ^ (m + 1) ≤ (I ^ (0 + 1)) ^ (m + 1) := Ideal.pow_right_mono h0 _
      _ = I ^ (m + 1) := by rw [← pow_mul]; norm_num
  have hbot : ∀ m : ℕ, (L ^ ((k + 1) * (m + 1))).map (φ m) = ⊥ := by
    intro m
    rw [← hψ m, ← Ideal.map_map]
    exact (Ideal.map_eq_bot_iff_le_ker _).mpr (by rw [Ideal.mk_ker]; exact hmapψ m)
  haveI hMadic : IsAdicRing (L ^ (k + 1)) :=
    IsAdicRing.of_isCofinal (Ideal.IsCofinal.pow L (Nat.succ_ne_zero k))
  have hMfg : (L ^ (k + 1)).FG := hL.pow
  have hML : L ^ (k + 1) ≤ L := Ideal.pow_le_self (Nat.succ_ne_zero k)
  have hψM : L ^ (k + 1) ≤ I.comap ψ := by
    refine Ideal.map_le_iff_le_comap.mp ?_
    simpa using h0
  refine ⟨locallyRingedSpaceMap (L ^ (k + 1)) I ψ hψM ≫
    (cofinalSpfIso (L ^ (k + 1)) L hML hMfg hL).hom, Subtype.ext (funext fun n => ?_)⟩
  change thickeningMap I n ≫ (locallyRingedSpaceMap (L ^ (k + 1)) I ψ hψM ≫
    (cofinalSpfIso (L ^ (k + 1)) L hML hMfg hL).hom) = F.1 n
  have hK0 : (k + 1) * (n + 1) ≠ 0 := Nat.mul_ne_zero (Nat.succ_ne_zero k) (Nat.succ_ne_zero n)
  haveI : IsAdicRing (L ^ ((k + 1) * (n + 1))) :=
    IsAdicRing.of_isCofinal (Ideal.IsCofinal.pow L hK0)
  have hNfg : (L ^ ((k + 1) * (n + 1))).FG := hL.pow
  have hNL : L ^ ((k + 1) * (n + 1)) ≤ L := Ideal.pow_le_self hK0
  refine (cancel_mono (cofinalSpfIso (L ^ ((k + 1) * (n + 1))) L hNL hNfg hL).inv).mp ?_
  refine hom_ext_of_comp_toSpecAmbient (L ^ ((k + 1) * (n + 1))) (R ⧸ I ^ (n + 1)) hNfg _ _
    (φ n) (hbot n) ?_ ?_
  · simp only [Category.assoc]
    rw [cofinalSpfIso_inv_comp_toSpecAmbient, cofinalSpfIso_hom_comp_toSpecAmbient,
      comp_toSpecAmbient, globalSectionsMap_locallyRingedSpaceMap,
      thickeningMap_comp_specHomEquiv_symm, hψ n]
  · simp only [Category.assoc]
    rw [cofinalSpfIso_inv_comp_toSpecAmbient, hφ n]

/-- **The bijection at a formal-affine target, unconditionally** (EGA I, 10.6.7). This is
`thickeningRestrictionEquivSpf` with its surjectivity hypothesis discharged: for `L` finitely
generated, morphisms `Spf R ⟶ Spf L` are exactly the compatible families of morphisms out of the
thickenings of `Spf R`. -/
def thickeningRestrictionEquivSpfOfFG (hL : L.FG) :
    (locallyRingedSpaceObj I ⟶ locallyRingedSpaceObj L) ≃
      ThickeningFamilyLRS I (locallyRingedSpaceObj L) :=
  thickeningRestrictionEquivSpf I L (surjective_restrictToThickeningsLRS_spf I L hL)

/-- **EGA I 10.6.10 at a formal-affine target.** A compatible family of morphisms out of the
infinitesimal thickenings of `Spf R` into `Spf L` comes from a **unique** morphism `Spf R ⟶ Spf L`.

Compare `FormalSpectrum.existsUnique_hom_thickeningMap` (`FormalSchemes/SpfHomOfFamily.lean`),
which is the same statement for a target covered by ordinary affines, and
`FormalSpectrum.existsUnique_hom_thickeningMap_spf_of_continuous`
(`FormalSchemes/SpfTargetColimit.lean`), which is this statement restricted to the families already
known to come from a continuous ring homomorphism. The restriction is now unnecessary. -/
theorem existsUnique_hom_thickeningMap_spf (hL : L.FG)
    (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶
      locallyRingedSpaceObj L)
    (hf : ∀ n : ℕ, Spec.locallyRingedSpaceMap (stepRingHom I n) ≫ f (n + 1) = f n) :
    ∃! g : locallyRingedSpaceObj I ⟶ locallyRingedSpaceObj L,
      ∀ n : ℕ, thickeningMap I n ≫ g = f n := by
  refine existsUnique_hom_thickeningMap_of_exists I f ?_
  obtain ⟨g, hg⟩ := surjective_restrictToThickeningsLRS_spf I L hL ⟨f, hf⟩
  exact ⟨g, fun n => congrFun (congrArg Subtype.val hg) n⟩

end Family

end FormalSpectrum

end
