import FormalSchemes.StructureSheafSections
import FormalSchemes.AdicCompletionLimit
import FormalSchemes.LocalizationQuotient

set_option linter.style.header false

/-!
# Sections of the structure sheaf of the formal spectrum

This file computes the sections of the structure sheaf `O_{Spf R}` of the formal spectrum of an
adic ring `R` with ideal of definition `I`, following EGA I, 10.1.3–10.1.4 (and Stacks, Tag
0AI7):

* over a basic open `D(f)`, `f ∈ R`, the sections are the `I`-adic completion of the localized
  ring `R_f = Localization.Away f`:
  `Γ(D(f), O_{Spf R}) ≃+* AdicCompletion (I·R_f) R_f` (`sectionsBasicOpenEquiv`);
* over the whole space, the sections are the `I`-adic completion of `R` itself,
  `Γ(⊤, O_{Spf R}) ≃+* AdicCompletion I R` (`globalSectionsEquivCompletion`), and hence — since
  an adic ring is complete — the sections recover `R`:
  `Γ(⊤, O_{Spf R}) ≃+* R` (`globalSectionsEquiv`).

The proofs assemble three ingredients: the description of `Γ(U, O_{Spf R})` as the limit of the
tower `n ↦ Γ(U, thickeningSheaf I n)` (`FormalSpectrum.sectionsLimitIso`), the level-`n`
identifications of these section rings with localizations of `R ⧸ I ^ (n + 1)`
(`FormalSpectrum.isLocalization_away_basicOpen_sections`, and
`StructureSheaf.algebraMap_obj_top_bijective` for `U = ⊤`), and the generic bridge
`AdicCompletion.towerLimitRingEquiv` identifying the limit of a tower whose level `n` is
`A ⧸ J ^ (n + 1)` with `AdicCompletion J A`.

## Main definitions

* `FormalSpectrum.basicOpenLevelEquiv I f n`: the identification of `Γ(D(f), thickeningSheaf n)`
  with `R_f ⧸ (I·R_f) ^ (n + 1)`.
* `FormalSpectrum.sectionsBasicOpenEquiv I f`:
  `Γ(D(f), O_{Spf R}) ≃+* AdicCompletion (I·R_f) R_f`.
* `FormalSpectrum.topLevelEquiv I n`: the identification of `Γ(⊤, thickeningSheaf n)` with
  `R ⧸ I ^ (n + 1)`.
* `FormalSpectrum.globalSectionsEquivCompletion I`: `Γ(⊤, O_{Spf R}) ≃+* AdicCompletion I R`.
* `FormalSpectrum.globalSectionsEquiv I`: `Γ(⊤, O_{Spf R}) ≃+* R` (EGA I, 10.1.3).

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1.
* [The Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]

namespace FormalSpectrum

/-!
### The tower of sections over a fixed open

For a fixed open `U ⊆ Spf R`, the sections of `O_{Spf R}` over `U` are the limit of the tower
`sectionsTower I U := n ↦ Γ(U, thickeningSheaf I n)` (`FormalSpectrum.sectionsLimitIso`).
-/

section Tower

omit [TopologicalSpace R] [IsAdicRing I]

variable (U : Opens (FormalSpectrum I))

/-- The tower of section rings `n ↦ Γ(U, thickeningSheaf I n)` of the thickening sheaves over a
fixed open `U ⊆ Spf R`, whose limit computes `Γ(U, O_{Spf R})`. -/
def sectionsTower : ℕᵒᵖ ⥤ CommRingCat :=
  structureSheafFunctor I ⋙ sectionsFunctor I (op U)

theorem sectionsTower_obj (n : ℕ) :
    (sectionsTower I U).obj ⟨n⟩ = (thickeningSheaf I n).presheaf.obj (op U) :=
  rfl

theorem sectionsTower_map_succ (n : ℕ) :
    (sectionsTower I U).map (homOfLE (Nat.le_add_right n 1)).op =
      (stepSheafHom I n).hom.app (op U) := by
  have h : (structureSheafFunctor I).map (homOfLE (Nat.le_add_right n 1)).op =
      stepSheafHom I n := by
    simp only [structureSheafFunctor]
    exact Functor.ofOpSequence_map_homOfLE_succ _ n
  change (sectionsFunctor I (op U)).map
    ((structureSheafFunctor I).map (homOfLE (Nat.le_add_right n 1)).op) = _
  rw [h]
  rfl

end Tower

/-!
### Sections on basic opens (EGA I, 10.1.4)
-/

section BasicOpen

omit [TopologicalSpace R] [IsAdicRing I]

variable (f : R) (n : ℕ)

/-- The identification of the sections of the `n`-th thickening sheaf over `D(f) ⊆ Spf R` with
the quotient `R_f ⧸ (I·R_f) ^ (n + 1)` of the localization `R_f = Localization.Away f`:
sections at level `n` are the localization of `R ⧸ I ^ (n + 1)` away from `f`, and localization
commutes with quotients. -/
def basicOpenLevelEquiv :
    ((thickeningSheaf I n).presheaf.obj (op (basicOpen I f)) : Type u) ≃+*
      Localization.Away f ⧸ (I.map (algebraMap R (Localization.Away f))) ^ (n + 1) :=
  (basicOpenSectionsEquiv I n f).trans
    ((Localization.awayQuotientEquiv f (I ^ (n + 1))).trans
      (Ideal.quotEquivOfEq (by rw [Ideal.map_pow])))

/-- `basicOpenLevelEquiv` matches up the canonical images of elements of `R` on the two sides. -/
theorem basicOpenLevelEquiv_algebraMap_mk (x : R) :
    basicOpenLevelEquiv I f n
        (algebraMap (R ⧸ I ^ (n + 1))
          ((thickeningSheaf I n).presheaf.obj (op (basicOpen I f)))
          (Ideal.Quotient.mk (I ^ (n + 1)) x)) =
      Ideal.Quotient.mk ((I.map (algebraMap R (Localization.Away f))) ^ (n + 1))
        (algebraMap R (Localization.Away f) x) := by
  simp only [basicOpenLevelEquiv, RingEquiv.trans_apply]
  have h1 : basicOpenSectionsEquiv I n f
      (algebraMap (R ⧸ I ^ (n + 1)) _ (Ideal.Quotient.mk (I ^ (n + 1)) x)) =
      algebraMap (R ⧸ I ^ (n + 1)) (Localization.Away (Ideal.Quotient.mk (I ^ (n + 1)) f))
        (Ideal.Quotient.mk (I ^ (n + 1)) x) :=
    (IsLocalization.algEquiv (Submonoid.powers (Ideal.Quotient.mk (I ^ (n + 1)) f)) _ _).commutes
      _
  rw [h1, Localization.awayQuotientEquiv_algebraMap]
  have h2 : (algebraMap (R ⧸ I ^ (n + 1))
      (Localization.Away f ⧸ (I ^ (n + 1)).map (algebraMap R (Localization.Away f))))
        (Ideal.Quotient.mk (I ^ (n + 1)) x) =
      Ideal.Quotient.mk ((I ^ (n + 1)).map (algebraMap R (Localization.Away f)))
        (algebraMap R (Localization.Away f) x) :=
    rfl
  rw [h2, Ideal.quotEquivOfEq_mk]

/-- The level identifications `basicOpenLevelEquiv` intertwine the transition maps of the tower
of sections over `D(f)` with the quotient factor maps of `R_f ⧸ (I·R_f) ^ (n + 1)`. -/
theorem basicOpenLevelEquiv_step :
    (basicOpenLevelEquiv I f n).toRingHom.comp
        ((sectionsTower I (basicOpen I f)).map (homOfLE (Nat.le_add_right n 1)).op).hom =
      (Ideal.Quotient.factorPow (I.map (algebraMap R (Localization.Away f)))
        (Nat.le_succ (n + 1))).comp (basicOpenLevelEquiv I f (n + 1)).toRingHom := by
  rw [sectionsTower_map_succ]
  change (basicOpenLevelEquiv I f n).toRingHom.comp
      ((stepSheafHom I n).hom.app (op (basicOpen I f))).hom = _
  apply IsLocalization.ringHom_ext (Submonoid.powers (Ideal.Quotient.mk (I ^ (n + 1 + 1)) f))
  apply Ideal.Quotient.ringHom_ext
  refine RingHom.ext fun x => ?_
  have key : basicOpenLevelEquiv I f n
      (StructureSheaf.comap (stepRingHom I n).hom
        (thickeningOpen I (n + 1) (basicOpen I f)) (thickeningOpen I n (basicOpen I f))
        (thickeningOpen_le_comap I n (basicOpen I f))
        ((algebraMap (R ⧸ I ^ (n + 1 + 1))
          ((thickeningSheaf I (n + 1)).presheaf.obj (op (basicOpen I f))))
          (Ideal.Quotient.mk (I ^ (n + 1 + 1)) x))) =
      Ideal.Quotient.factorPow (I.map (algebraMap R (Localization.Away f)))
        (Nat.le_succ (n + 1))
        (basicOpenLevelEquiv I f (n + 1)
          ((algebraMap (R ⧸ I ^ (n + 1 + 1))
            ((thickeningSheaf I (n + 1)).presheaf.obj (op (basicOpen I f))))
            (Ideal.Quotient.mk (I ^ (n + 1 + 1)) x))) := by
    rw [comap_step_algebraMap I n (basicOpen I f)]
    have hstep : (stepRingHom I n).hom (Ideal.Quotient.mk (I ^ (n + 1 + 1)) x) =
        Ideal.Quotient.mk (I ^ (n + 1)) x :=
      Ideal.Quotient.factor_mk (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) x
    rw [hstep, basicOpenLevelEquiv_algebraMap_mk, basicOpenLevelEquiv_algebraMap_mk,
      Ideal.Quotient.factor_mk]
  exact key

/-- **Sections of `O_{Spf R}` on a basic open** (EGA I, 10.1.4; Stacks, Tag 0AI7): the ring of
sections of the structure sheaf of `Spf R` over the basic open `D(f)` is the `I`-adic completion
of the localization `R_f`. -/
def sectionsBasicOpenEquiv :
    ((structureSheaf I).presheaf.obj (op (basicOpen I f)) : Type u) ≃+*
      AdicCompletion (I.map (algebraMap R (Localization.Away f))) (Localization.Away f) :=
  (sectionsLimitIso I (op (basicOpen I f))).commRingCatIsoToRingEquiv.trans
    (AdicCompletion.towerLimitRingEquiv (I.map (algebraMap R (Localization.Away f)))
      (sectionsTower I (basicOpen I f)) (basicOpenLevelEquiv I f)
      (basicOpenLevelEquiv_step I f))

end BasicOpen

/-!
### Global sections (EGA I, 10.1.3)
-/

section GlobalSections

omit [TopologicalSpace R] [IsAdicRing I]

variable (n : ℕ)

/-- The identification of the global sections of the `n`-th thickening sheaf with the ring
`R ⧸ I ^ (n + 1)` of the thickening itself: global sections of the structure sheaf of an affine
scheme are the ring. -/
def topLevelEquiv :
    ((thickeningSheaf I n).presheaf.obj (op (⊤ : Opens (FormalSpectrum I))) : Type u) ≃+*
      R ⧸ I ^ (n + 1) :=
  (RingEquiv.ofBijective
    (algebraMap (R ⧸ I ^ (n + 1))
      ((thickeningSheaf I n).presheaf.obj (op (⊤ : Opens (FormalSpectrum I)))))
    StructureSheaf.algebraMap_obj_top_bijective).symm

theorem topLevelEquiv_symm_apply (b : R ⧸ I ^ (n + 1)) :
    (topLevelEquiv I n).symm b =
      algebraMap (R ⧸ I ^ (n + 1))
        ((thickeningSheaf I n).presheaf.obj (op (⊤ : Opens (FormalSpectrum I)))) b :=
  rfl

theorem topLevelEquiv_algebraMap (b : R ⧸ I ^ (n + 1)) :
    topLevelEquiv I n
        (algebraMap (R ⧸ I ^ (n + 1))
          ((thickeningSheaf I n).presheaf.obj (op (⊤ : Opens (FormalSpectrum I)))) b) = b :=
  (RingEquiv.ofBijective _ StructureSheaf.algebraMap_obj_top_bijective).symm_apply_apply b

/-- The level identifications `topLevelEquiv` intertwine the transition maps of the tower of
global sections with the quotient factor maps of `R ⧸ I ^ (n + 1)`. -/
theorem topLevelEquiv_step :
    (topLevelEquiv I n).toRingHom.comp
        ((sectionsTower I ⊤).map (homOfLE (Nat.le_add_right n 1)).op).hom =
      (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))).comp
        (topLevelEquiv I (n + 1)).toRingHom := by
  rw [sectionsTower_map_succ]
  change (topLevelEquiv I n).toRingHom.comp
      ((stepSheafHom I n).hom.app (op (⊤ : Opens (FormalSpectrum I)))).hom = _
  refine RingHom.ext fun s => ?_
  obtain ⟨b, rfl⟩ := (topLevelEquiv I (n + 1)).symm.surjective s
  have key : topLevelEquiv I n
      (StructureSheaf.comap (stepRingHom I n).hom
        (thickeningOpen I (n + 1) ⊤) (thickeningOpen I n ⊤) (thickeningOpen_le_comap I n ⊤)
        ((topLevelEquiv I (n + 1)).symm b)) =
      Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))
        (topLevelEquiv I (n + 1) ((topLevelEquiv I (n + 1)).symm b)) := by
    rw [RingEquiv.apply_symm_apply, topLevelEquiv_symm_apply, comap_step_algebraMap I n ⊤ b,
      topLevelEquiv_algebraMap]
    rfl
  exact key

/-- The global sections of the structure sheaf of `Spf R` are the `I`-adic completion of `R`. -/
def globalSectionsEquivCompletion :
    ((structureSheaf I).presheaf.obj (op (⊤ : Opens (FormalSpectrum I))) : Type u) ≃+*
      AdicCompletion I R :=
  (sectionsLimitIso I (op (⊤ : Opens (FormalSpectrum I)))).commRingCatIsoToRingEquiv.trans
    (AdicCompletion.towerLimitRingEquiv I (sectionsTower I ⊤) (topLevelEquiv I)
      (topLevelEquiv_step I))

end GlobalSections

/-- **Global sections of `O_{Spf R}`** (EGA I, 10.1.3): the ring of global sections of the
structure sheaf of the formal spectrum of an adic ring `R` recovers `R` itself, since an adic
ring is complete for its `I`-adic topology. -/
def globalSectionsEquiv :
    ((structureSheaf I).presheaf.obj (op (⊤ : Opens (FormalSpectrum I))) : Type u) ≃+* R :=
  (globalSectionsEquivCompletion I).trans
    ((AdicCompletion.ofAlgEquiv (S := R) I).symm : AdicCompletion I R ≃+* R)

end FormalSpectrum
