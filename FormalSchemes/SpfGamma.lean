import FormalSchemes.SpfMap
import FormalSchemes.Sections

set_option linter.style.header false

/-!
# Global sections of a morphism of formal spectra

For adic rings `(R, I)` and `(S, J)`, taking global sections turns a morphism of formal
spectra `Spf S ⟶ Spf R` into a ring homomorphism `Γ(Spf R) → Γ(Spf S)`, i.e. `R → S` after the
identifications `Γ(⊤, O_{Spf R}) ≃+* R` of `FormalSchemes/Sections.lean`. This file constructs
that map (`FormalSpectrum.globalSectionsMap`) and proves the key computation

```
globalSectionsMap (Spf φ) = φ
```

(`FormalSpectrum.globalSectionsMap_locallyRingedSpaceMap`): the passage from a continuous ring
homomorphism to a morphism of formal spectra and back is the identity. This is one half of the
universal property of `Spf` (EGA I, 10.4.6) — in particular `Spf` is faithful on continuous
ring homomorphisms. The converse half (every morphism of formal spectra arises this way, so
that the correspondence is bijective) is the analogue of the `Γ ⊣ Spec` adjunction for schemes
and is left to future work.

## Main definitions and results

* `FormalSpectrum.globalSectionsMap`: the ring homomorphism `R →+* S` induced by a morphism of
  locally ringed spaces `Spf S ⟶ Spf R`.
* `FormalSpectrum.mk_globalSectionsEquiv`: the level-`n` computation rule for the
  identification `Γ(⊤, O_{Spf R}) ≃+* R`.
* `FormalSpectrum.globalSectionsMap_locallyRingedSpaceMap`: `Γ(Spf φ) = φ`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4.6.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FormalSpectrum

variable {R S : Type u} [CommRing R] [CommRing S]
variable (I : Ideal R) (J : Ideal S)

/-!
### The level-`n` computation rule for global sections
-/

section Computation

variable [TopologicalSpace R] [IsAdicRing I]

/-- The identification `Γ(⊤, O_{Spf R}) ≃+* R` is computed level by level: modulo `I ^ (n + 1)`,
the element of `R` attached to a global section is the level-`n` component of the section. -/
theorem mk_globalSectionsEquiv (n : ℕ)
    (s : (structureSheaf I).presheaf.obj (op (⊤ : Opens (FormalSpectrum I)))) :
    Ideal.Quotient.mk (I ^ (n + 1)) (globalSectionsEquiv I s) =
      topLevelEquiv I n
        (((limit.π (structureSheafFunctor I) ⟨n⟩).hom.app
          (op (⊤ : Opens (FormalSpectrum I)))).hom s) := by
  -- unfold the identification through the completion and the shifted-tower bridge
  have h1 : AdicCompletion.of I R (globalSectionsEquiv I s) =
      globalSectionsEquivCompletion I s := by
    change (AdicCompletion.ofAlgEquiv I) ((AdicCompletion.ofAlgEquiv (S := R) I).symm
      (globalSectionsEquivCompletion I s)) = _
    exact (AdicCompletion.ofAlgEquiv (S := R) I).toRingEquiv.apply_symm_apply _
  have h2 : AdicCompletion.evalₐ I (n + 1) (globalSectionsEquivCompletion I s) =
      topLevelEquiv I n
        (((limit.π (structureSheafFunctor I) ⟨n⟩).hom.app
          (op (⊤ : Opens (FormalSpectrum I)))).hom s) := by
    change AdicCompletion.evalₐ I (n + 1)
      (AdicCompletion.towerLimitRingEquiv I (sectionsTower I ⊤) (topLevelEquiv I)
        (fun m => by rw [sectionsTower_map_succ]; exact topLevelEquiv_step I m)
        ((sectionsLimitIso I (op (⊤ : Opens (FormalSpectrum I)))).hom.hom s)) = _
    rw [AdicCompletion.evalₐ_towerLimitRingEquiv, AdicCompletion.towerProj_apply]
    congr 1
    exact DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
      (sectionsLimitIso_hom_π I (op (⊤ : Opens (FormalSpectrum I))) n)) s
  rw [← h2, ← h1]
  exact (AdicCompletion.evalₐ_of I (n + 1) _).symm

end Computation

/-!
### Global sections of a morphism
-/

section Map

variable [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J]

/-- The ring homomorphism `R →+* S` induced by a morphism of formal spectra `Spf S ⟶ Spf R`,
by taking global sections and using the identifications `Γ(⊤, O_{Spf R}) ≃+* R`. -/
def globalSectionsMap (f : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I) : R →+* S :=
  ((globalSectionsEquiv J).toRingHom.comp
    (f.c.app (op (⊤ : Opens (FormalSpectrum I)))).hom).comp
      (globalSectionsEquiv I).symm.toRingHom

theorem globalSectionsMap_apply (f : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    (r : R) :
    globalSectionsMap I J f r =
      globalSectionsEquiv J ((f.c.app (op (⊤ : Opens (FormalSpectrum I)))).hom
        ((globalSectionsEquiv I).symm r)) :=
  rfl

variable (φ : R →+* S) (hφ : I ≤ J.comap φ)

/-- **Taking global sections inverts `Spf`** (one half of EGA I, 10.4.6): the ring
homomorphism recovered from the morphism of formal spectra induced by `φ` is `φ` itself. In
particular `Spf` is faithful on continuous ring homomorphisms. -/
theorem globalSectionsMap_locallyRingedSpaceMap :
    globalSectionsMap I J (locallyRingedSpaceMap I J φ hφ) = φ := by
  refine RingHom.ext fun r => ?_
  rw [globalSectionsMap_apply]
  -- compare the two sides modulo every power of `J`, then use Hausdorffness
  set s := (globalSectionsEquiv I).symm r with hs
  set t := ((locallyRingedSpaceMap I J φ hφ).c.app
    (op (⊤ : Opens (FormalSpectrum I)))).hom s with ht
  refine (IsHausdorff.eq_iff_smodEq (I := J)).mpr fun n => ?_
  rw [SModEq.sub_mem]
  have hmem : ∀ (m : ℕ) (z : S), z ∈ (J ^ m • ⊤ : Submodule S S) ↔ z ∈ J ^ m := by
    intro m z
    rw [Ideal.smul_top_eq_map (J ^ m), Submodule.restrictScalars_mem, Algebra.algebraMap_self,
      Ideal.map_id]
  refine (hmem n _).mpr (Ideal.Quotient.eq.mp ?_)
  -- it suffices to compare the level-`n` components
  cases n with
  | zero =>
    have htop : (J ^ 0 : Ideal S) = ⊤ := by rw [pow_zero]; exact Ideal.one_eq_top
    refine Ideal.Quotient.eq.mpr ?_
    rw [htop]
    trivial
  | succ n =>
    rw [mk_globalSectionsEquiv J n t]
    -- the level-`n` component of the image section
    have hπ : ((limit.π (structureSheafFunctor J) ⟨n⟩).hom.app
        (op (⊤ : Opens (FormalSpectrum J)))).hom t =
        ((levelSheafHom I J φ hφ n).hom.app (op (⊤ : Opens (FormalSpectrum I)))).hom
          (((limit.π (structureSheafFunctor I) ⟨n⟩).hom.app
            (op (⊤ : Opens (FormalSpectrum I)))).hom s) := by
      have h := DFunLike.congr_fun (congrArg (fun (α : structureSheaf I ⟶
        (TopCat.Sheaf.pushforward CommRingCat (mapTop I J φ hφ)).obj (thickeningSheaf J n)) =>
          (α.hom.app (op (⊤ : Opens (FormalSpectrum I)))).hom) (mapSheafHom_π I J φ hφ n)) s
      exact h
    rw [hπ]
    -- the level-`n` component of `s` is the residue of `r`
    have hs' : ((limit.π (structureSheafFunctor I) ⟨n⟩).hom.app
        (op (⊤ : Opens (FormalSpectrum I)))).hom s =
        (topLevelEquiv I n).symm (Ideal.Quotient.mk (I ^ (n + 1)) r) := by
      have h := mk_globalSectionsEquiv I n s
      rw [hs, RingEquiv.apply_symm_apply] at h
      rw [h, RingEquiv.symm_apply_apply]
    rw [hs', topLevelEquiv_symm_apply,
      levelSheafHom_hom_app I J φ hφ n (⊤ : Opens (FormalSpectrum I))]
    -- and `comap` of the level map sends it to the residue of `φ r`
    have hval : (CommRingCat.ofHom (StructureSheaf.comap (levelRingHom I J φ hφ n)
        (thickeningOpen I n ⊤) (thickeningOpen J n ((Opens.map (mapTop I J φ hφ)).obj ⊤))
        (thickeningOpen_map_le I J φ hφ n ⊤))).hom
        (algebraMap (R ⧸ I ^ (n + 1))
          ((thickeningSheaf I n).presheaf.obj (op (⊤ : Opens (FormalSpectrum I))))
          (Ideal.Quotient.mk (I ^ (n + 1)) r)) =
        algebraMap (S ⧸ J ^ (n + 1))
          ((thickeningSheaf J n).presheaf.obj
            (op ((Opens.map (mapTop I J φ hφ)).obj (⊤ : Opens (FormalSpectrum I)))))
          (Ideal.Quotient.mk (J ^ (n + 1)) (φ r)) := by
      have hc := comap_algebraMap (levelRingHom I J φ hφ n) (thickeningOpen I n ⊤)
        (thickeningOpen J n ((Opens.map (mapTop I J φ hφ)).obj ⊤))
        (thickeningOpen_map_le I J φ hφ n ⊤) (Ideal.Quotient.mk (I ^ (n + 1)) r)
      rw [levelRingHom_mk] at hc
      exact hc
    exact Eq.trans (congrArg (topLevelEquiv J n) hval) (topLevelEquiv_algebraMap J n _)

end Map

end FormalSpectrum
