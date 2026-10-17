/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.QcohAffineLocalization

/-!
# Quasi-coherence is local
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- A module whose restrictions to the members of an open covering have presentations is
quasi-coherent. -/
lemma isQuasicoherent_of_presentation (M : X.Modules) {ι : Type u} (U : ι → X.Opens)
    (hU : iSup U = ⊤) (P : ∀ i, (M.restrict (U i).ι).Presentation) : M.IsQuasicoherent := by
  refine SheafOfModules.QuasicoherentData.isQuasicoherent (M := M)
    { I := ι
      X := fun i ↦ U i
      coversTop := ?_
      presentation := fun i ↦ ?_ }
  · rw [Opens.coversTop_iff]
    exact hU
  · let e := overEquiv (U i)
    let P' :
        (e.functor.obj ((SheafOfModules.overFunctor X.ringCatSheaf (U i)).obj M)).Presentation :=
      (P i).ofIsIso ((overFunctorEquiv (U i)).app M).inv
    exact (P'.map e.inverse ((U i).sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm).ofIsIso
      (e.unitIso.app _).inv

/-- A presentation of the `~` of a module. -/
noncomputable def presentationTildeSelf {R : CommRingCat.{u}} (N : ModuleCat.{u} R) :
    (tilde N).Presentation :=
  presentationTilde _ Set.univ Submodule.span_univ _ (Submodule.span_eq _)

/-- Transport a presentation of `M.restrict hU.fromSpec` to `M.restrict U.ι`. -/
noncomputable def presentationRestrictι {U : X.Opens} (hU : IsAffineOpen U) (M : X.Modules)
    (P : (M.restrict hU.fromSpec).Presentation) : (M.restrict U.ι).Presentation :=
  (presentationRestrict hU.isoSpec.hom P).ofIsIso
    (((restrictFunctorComp hU.isoSpec.hom hU.fromSpec).app M).inv ≫
      ((restrictFunctorCongr hU.isoSpec_hom_fromSpec).app M).hom)

/-- On an affine open `U`, a module whose restriction to `Spec Γ(X, U)` is the `~` of its global
sections has a presentation over `U`. -/
noncomputable def presentationRestrictOfIsIso {U : X.Opens} (hU : IsAffineOpen U) (M : X.Modules)
    (h : IsIso (M.restrict hU.fromSpec).fromTildeΓ) : (M.restrict U.ι).Presentation :=
  let P := @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _
    (M.restrict hU.fromSpec).fromTildeΓ h
    (presentationTilde _ Set.univ Submodule.span_univ _ (Submodule.span_eq _))
  (presentationRestrict hU.isoSpec.hom P).ofIsIso
    (((restrictFunctorComp hU.isoSpec.hom hU.fromSpec).app M).inv ≫
      ((restrictFunctorCongr hU.isoSpec_hom_fromSpec).app M).hom)

/-- **Quasi-coherence is local**: a module that is the `~` of its sections on the members of an
affine open covering is quasi-coherent. -/
lemma isQuasicoherent_of_isIso_fromTildeΓ (M : X.Modules) {ι : Type u} (U : ι → X.Opens)
    (hU : iSup U = ⊤) (hA : ∀ i, IsAffineOpen (U i))
    (h : ∀ i, IsIso (M.restrict (hA i).fromSpec).fromTildeΓ) : M.IsQuasicoherent :=
  isQuasicoherent_of_presentation M U hU fun i ↦ presentationRestrictOfIsIso (hA i) M (h i)

variable {U : X.Opens} (hU : IsAffineOpen U)

include hU in
/-- The `Γ(X, U)`-action on the sections of `M.restrict hU.fromSpec` over an open `V`, in terms
of `M`: a function acts through its restriction to the image of `V`. -/
lemma smul_restrict_fromSpec (M : X.Modules) (V : (Spec Γ(X, U)).Opens) (r : Γ(X, U))
    (x : (modulesSpecToSheaf.obj (M.restrict hU.fromSpec)).obj.obj (op V)) :
    r • x = (show Γ(M, hU.fromSpec ''ᵁ V) from
      X.presheaf.map (homOfLE (image_fromSpec_le hU V)).op r • (show Γ(M, _) from x)) := by
  rw [spec_smul_eq]
  refine (restrict_smul_eq hU.fromSpec M V _ x).trans ?_
  rw [fromSpec_appIso_inv_res]

include hU in
/-- **Converse of `exists_pow_smul_eq_res`/`exists_pow_smul_eq_zero`**: if the restrictions of
`M` from an affine open `U` to its basic opens are localisations, then `M` is the `~` of its
sections over `U`. -/
theorem isIso_fromTildeΓ_restrict (M : X.Modules)
    (hex : ∀ (f : Γ(X, U)) (z : Γ(M, X.basicOpen f)), ∃ (m : Γ(M, U)) (k : ℕ),
      X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ k) • z =
        M.presheaf.map (homOfLE (X.basicOpen_le f)).op m)
    (hker : ∀ (f : Γ(X, U)) (m : Γ(M, U)),
      M.presheaf.map (homOfLE (X.basicOpen_le f)).op m = 0 → ∃ k : ℕ, f ^ k • m = 0) :
    IsIso (M.restrict hU.fromSpec).fromTildeΓ := by
  rw [isIso_fromTildeΓ_iff_isLocalizing]
  intro f
  let g := hU.fromSpec
  have eT := image_fromSpec_top hU
  have eF : g ''ᵁ PrimeSpectrum.basicOpen f = X.basicOpen f := hU.fromSpec_image_basicOpen f
  change IsLocalizedModule _ (specRes (M.restrict g) (le_top : PrimeSpectrum.basicOpen f ≤ ⊤))
  refine ⟨fun x ↦ ?_, fun z ↦ ?_, fun {x y} hxy ↦ ?_⟩
  · obtain ⟨_, ⟨k, rfl⟩⟩ := x
    change IsUnit (algebraMap _ _ (f ^ k))
    rw [map_pow]
    exact ((M.restrict g).isUnit_algebraMap_end_of_le_basicOpen f le_rfl).pow k
  · let z' : Γ(M, X.basicOpen f) :=
      M.presheaf.map (homOfLE eF.ge).op (show Γ(M, g ''ᵁ _) from z)
    obtain ⟨m, k, hk⟩ := hex f z'
    refine ⟨⟨M.presheaf.map (homOfLE eT.le).op m, ⟨f ^ k, k, rfl⟩⟩, ?_⟩
    have h3 := congrArg (M.presheaf.map (homOfLE eF.le).op) hk
    rw [map_smul] at h3
    refine (smul_restrict_fromSpec hU M _ (f ^ k) z).trans ?_
    change _ = M.presheaf.map _ (M.presheaf.map _ m)
    simp only [z', presheaf_map_map_comp, scheme_presheaf_map_map_comp] at h3 ⊢
    rw [presheaf_map_congr M _ (𝟙 _)] at h3
    simp only [op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] at h3
    exact h3.trans (presheaf_map_map M (homOfLE eT.le) (homOfLE (g.image_mono le_top)) _ m).symm
  · obtain ⟨k, hk⟩ := hker f (M.presheaf.map (homOfLE eT.ge).op (show Γ(M, g ''ᵁ ⊤) from x) -
        M.presheaf.map (homOfLE eT.ge).op (show Γ(M, g ''ᵁ ⊤) from y)) (by
      have h1 : M.presheaf.map (homOfLE eF.ge).op (M.presheaf.map
          (homOfLE (g.image_mono (le_top : PrimeSpectrum.basicOpen f ≤ ⊤))).op
            (show Γ(M, g ''ᵁ ⊤) from x)) = M.presheaf.map (homOfLE eF.ge).op (M.presheaf.map
          (homOfLE (g.image_mono (le_top : PrimeSpectrum.basicOpen f ≤ ⊤))).op
            (show Γ(M, g ''ᵁ ⊤) from y)) :=
        congrArg (fun w ↦ M.presheaf.map (homOfLE eF.ge).op w) hxy
      rw [map_sub, sub_eq_zero]
      simp only [presheaf_map_map_comp] at h1 ⊢
      exact h1)
    refine ⟨⟨f ^ k, k, rfl⟩, ?_⟩
    rw [← sub_eq_zero]
    change (f ^ k) • x - (f ^ k) • y = 0
    refine (congrArg₂ (· - ·) (smul_restrict_fromSpec hU M ⊤ (f ^ k) x)
      (smul_restrict_fromSpec hU M ⊤ (f ^ k) y)).trans ?_
    have hid : ∀ w : Γ(M, g ''ᵁ ⊤),
        M.presheaf.map (homOfLE eT.le).op (M.presheaf.map (homOfLE eT.ge).op w) = w := by
      intro w
      rw [presheaf_map_map_comp, presheaf_map_congr M _ (𝟙 _)]
      simp
    have h2 := congrArg (M.presheaf.map (homOfLE eT.le).op) hk
    rw [map_zero, map_smul, map_sub, hid, hid] at h2
    refine (smul_sub (X.presheaf.map (homOfLE (image_fromSpec_le hU ⊤)).op (f ^ k))
      (show Γ(M, g ''ᵁ ⊤) from x) (show Γ(M, g ''ᵁ ⊤) from y)).symm.trans ?_
    exact h2

end AlgebraicGeometry.Scheme.Modules
