import FormalSchemes.CompletionToSpec
import FormalSchemes.SpfDiscrete
import FormalSchemes.SpfTargetColimit

set_option linter.style.header false

/-!
# Placeholder
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FormalSpectrum

/-- `Spec` is faithful on `LocallyRingedSpace`. -/
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
theorem botQuotEquiv_comp_mk :
    (botQuotEquiv A 0).toRingHom.comp (Ideal.Quotient.mk ((⊥ : Ideal A) ^ (0 + 1))) =
      RingHom.id A :=
  RingHom.ext fun x => botQuotEquiv_mk A 0 x

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

theorem specMap_ofHom_injective {P Q : Type u} [CommRing P] [CommRing Q] {f g : P →+* Q}
    (h : Spec.locallyRingedSpaceMap (CommRingCat.ofHom f) =
      Spec.locallyRingedSpaceMap (CommRingCat.ofHom g)) : f = g :=
  congrArg CommRingCat.Hom.hom (specMap_injective h)

end SpecSource

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

end FormalSpectrum

end
