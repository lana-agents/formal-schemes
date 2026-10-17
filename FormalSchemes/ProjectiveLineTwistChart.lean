/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ProjectiveLineEquiv

/-!
# Serre twists and chart modules

For a quasi-coherent module `F` on `ℙ¹_A`, the Serre twist `F(d)` (`ProjectiveLine.serreTwist`)
is quasi-coherent (`ProjectiveLine.isQuasicoherent_serreTwist`), and its chart module is the twist
`(chartModule F)(d)` of the chart module of `F` (`ProjectiveLine.chartModuleTwistIso`).
-/

universe u

open AlgebraicGeometry CategoryTheory Opposite AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M : X.Modules} {U V : X.Opens} {τ : Γ(X, U ⊓ V)}

lemma twistAppEquivLeft_smul (hτ : IsUnit τ) {W : X.Opens} (hW : W ≤ U) (r : Γ(X, W))
    (p : Γ(twist M U V τ, W)) :
    twistAppEquivLeft hτ hW (r • p) = r • twistAppEquivLeft hτ hW p := by
  change M.presheaf.map _ (X.presheaf.map (homOfLE inf_le_right : U ⊓ W ⟶ W).op r •
    twistFst p) = r • M.presheaf.map _ (twistFst p)
  rw [Scheme.Modules.map_smul, scheme_presheaf_map_map_comp, scheme_presheaf_map_congr _ (𝟙 _)]
  simp

lemma twistAppEquivRight_smul {W : X.Opens} (hW : W ≤ V) (r : Γ(X, W))
    (p : Γ(twist M U V τ, W)) :
    twistAppEquivRight hW (r • p) = r • twistAppEquivRight hW p := by
  change M.presheaf.map _ (X.presheaf.map (homOfLE inf_le_right : V ⊓ W ⟶ W).op r •
    twistSnd p) = r • M.presheaf.map _ (twistSnd p)
  rw [Scheme.Modules.map_smul, scheme_presheaf_map_map_comp, scheme_presheaf_map_congr _ (𝟙 _)]
  simp

lemma twistAppEquivLeft_res (hτ : IsUnit τ) {W W' : X.Opens} (hW : W ≤ U) (h : W' ≤ W)
    (p : Γ(twist M U V τ, W)) :
    twistAppEquivLeft hτ (h.trans hW) ((twist M U V τ).presheaf.map (homOfLE h).op p) =
      M.presheaf.map (homOfLE h).op (twistAppEquivLeft hτ hW p) := by
  exact (presheaf_map_map M (homOfLE (inf_le_inf_left U h)) (homOfLE (le_inf (h.trans hW) le_rfl))
    (homOfLE (le_inf (h.trans hW) h)) (twistFst p)).trans
      (presheaf_map_map M (homOfLE (le_inf hW le_rfl)) (homOfLE h) _ (twistFst p)).symm

lemma twistAppEquivRight_res {W W' : X.Opens} (hW : W ≤ V) (h : W' ≤ W)
    (p : Γ(twist M U V τ, W)) :
    twistAppEquivRight (h.trans hW) ((twist M U V τ).presheaf.map (homOfLE h).op p) =
      M.presheaf.map (homOfLE h).op (twistAppEquivRight hW p) := by
  exact (presheaf_map_map M (homOfLE (inf_le_inf_left V h)) (homOfLE (le_inf (h.trans hW) le_rfl))
    (homOfLE (le_inf (h.trans hW) h)) (twistSnd p)).trans
      (presheaf_map_map M (homOfLE (le_inf hW le_rfl)) (homOfLE h) _ (twistSnd p)).symm

end AlgebraicGeometry.Scheme.Modules

namespace ProjectiveLine

variable {A : Type u} [CommRing A] (F : (scheme A).Modules) [F.IsQuasicoherent] (d : ℤ)

lemma isIso_fromTildeΓ_twist0 :
    IsIso (Scheme.Modules.fromTildeΓ (R := R A 0)
      ((serreTwist A F d).restrict (isAffineOpen_U A 0).fromSpec)) := by
  have hτ := isUnit_transition A d
  let e : ∀ {W : (scheme A).Opens} (hW : W ≤ U A 0), Γ(serreTwist A F d, W) ≃+ Γ(F, W) :=
    fun hW ↦ twistAppEquivLeft hτ hW
  refine isIso_fromTildeΓ_restrict (isAffineOpen_U A 0) _ (fun f z ↦ ?_) (fun f m hm ↦ ?_)
  · obtain ⟨m', k, hk⟩ := exists_pow_smul_eq_res (isAffineOpen_U A 0) F f
      (e ((scheme A).basicOpen_le f) z)
    refine ⟨(e le_rfl).symm m', k, (e ((scheme A).basicOpen_le f)).injective ?_⟩
    rw [twistAppEquivLeft_smul, hk]
    exact ((twistAppEquivLeft_res hτ le_rfl _ _).trans
      (congrArg _ ((e le_rfl).apply_symm_apply m'))).symm
  · obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero (isAffineOpen_U A 0) F f (e le_rfl m) (by
      rw [← twistAppEquivLeft_res hτ le_rfl ((scheme A).basicOpen_le f), hm, map_zero])
    refine ⟨k, (e le_rfl).injective ?_⟩
    rw [twistAppEquivLeft_smul, hk, map_zero]

lemma isIso_fromTildeΓ_twist1 :
    IsIso (Scheme.Modules.fromTildeΓ (R := R A 1)
      ((serreTwist A F d).restrict (isAffineOpen_U A 1).fromSpec)) := by
  let e : ∀ {W : (scheme A).Opens} (hW : W ≤ U A 1), Γ(serreTwist A F d, W) ≃+ Γ(F, W) :=
    fun hW ↦ twistAppEquivRight hW
  refine isIso_fromTildeΓ_restrict (isAffineOpen_U A 1) _ (fun f z ↦ ?_) (fun f m hm ↦ ?_)
  · obtain ⟨m', k, hk⟩ := exists_pow_smul_eq_res (isAffineOpen_U A 1) F f
      (e ((scheme A).basicOpen_le f) z)
    refine ⟨(e le_rfl).symm m', k, (e ((scheme A).basicOpen_le f)).injective ?_⟩
    rw [twistAppEquivRight_smul, hk]
    exact ((twistAppEquivRight_res le_rfl _ _).trans
      (congrArg _ ((e le_rfl).apply_symm_apply m'))).symm
  · obtain ⟨k, hk⟩ := exists_pow_smul_eq_zero (isAffineOpen_U A 1) F f (e le_rfl m) (by
      rw [← twistAppEquivRight_res le_rfl ((scheme A).basicOpen_le f), hm, map_zero])
    refine ⟨k, (e le_rfl).injective ?_⟩
    rw [twistAppEquivRight_smul, hk, map_zero]

/-- **Serre twists of quasi-coherent modules are quasi-coherent.** -/
instance isQuasicoherent_serreTwist : (serreTwist A F d).IsQuasicoherent :=
  isQuasicoherent_of_isIso_fromTildeΓ _ (fun i : ULift.{u} (Fin 2) ↦ U A i.down)
    (by
      refine le_antisymm le_top ((U_sup A).symm.le.trans (sup_le ?_ ?_))
      · exact le_iSup (fun i : ULift.{u} (Fin 2) ↦ U A i.down) ⟨0⟩
      · exact le_iSup (fun i : ULift.{u} (Fin 2) ↦ U A i.down) ⟨1⟩)
    (fun i ↦ isAffineOpen_U A i.down)
    fun ⟨k⟩ ↦ by
      fin_cases k
      · exact isIso_fromTildeΓ_twist0 F d
      · exact isIso_fromTildeΓ_twist1 F d

variable (A) in
lemma transition_add (a b : ℤ) : transition A (a + b) = transition A a * transition A b :=
  (overlapSections A).injective (by
    rw [map_mul, overlapSections_transition, overlapSections_transition,
      overlapSections_transition, LaurentPolynomial.T_add])

variable (A) in
lemma transition_zero : transition A 0 = 1 :=
  (overlapSections A).injective (by
    rw [map_one, overlapSections_transition, LaurentPolynomial.T_zero])

omit [F.IsQuasicoherent] in
lemma tA_zpow_apply (d : ℤ) (z : secA F (U A 0 ⊓ U A 1)) :
    (tA F ^ d) z = smulA F (transition A d) z := by
  induction d using Int.induction_on with
  | zero =>
    rw [zpow_zero, transition_zero]
    exact (one_smul _ (show Γ(F, U A 0 ⊓ U A 1) from z)).symm
  | succ n ih =>
    rw [show (n : ℤ) + 1 = 1 + n by ring, zpow_add, zpow_one, LinearEquiv.mul_apply, ih,
      transition_add]
    exact smul_smul (transition A 1) (transition A n) (show Γ(F, U A 0 ⊓ U A 1) from z)
  | pred n ih =>
    rw [show -(n : ℤ) - 1 = -1 + -n by ring, zpow_add, zpow_neg_one, LinearEquiv.mul_apply, ih,
      transition_add]
    exact smul_smul (transition A (-1)) (transition A (-n)) (show Γ(F, U A 0 ⊓ U A 1) from z)

omit [F.IsQuasicoherent] in
lemma twist_r1 (p : Γ(serreTwist A F d, U A 1)) :
    twistAppEquivLeft (isUnit_transition A d) (inf_le_left : U A 0 ⊓ U A 1 ≤ U A 0)
      ((serreTwist A F d).presheaf.map (homOfLE (inf_le_right : U A 0 ⊓ U A 1 ≤ U A 1)).op p) =
      ((tA F) ^ d) (F.presheaf.map (homOfLE (inf_le_right : U A 0 ⊓ U A 1 ≤ U A 1)).op
        (twistAppEquivRight (le_rfl : U A 1 ≤ U A 1) p)) := by
  have c := twist_cond p
  let ι : U A 0 ⊓ U A 1 ⟶ (U A 0 ⊓ U A 1) ⊓ U A 1 := homOfLE (le_inf le_rfl inf_le_right)
  have c' := congrArg (F.presheaf.map ι.op) c
  rw [Scheme.Modules.map_smul] at c'
  have l1 : twistAppEquivLeft (isUnit_transition A d) (inf_le_left : U A 0 ⊓ U A 1 ≤ U A 0)
      ((serreTwist A F d).presheaf.map (homOfLE (inf_le_right : U A 0 ⊓ U A 1 ≤ U A 1)).op p) =
        F.presheaf.map ι.op (F.presheaf.map (homOfLE (inf_le_inf_right (U A 1) inf_le_left) :
          (U A 0 ⊓ U A 1) ⊓ U A 1 ⟶ U A 0 ⊓ U A 1).op (twistFst p)) :=
    (presheaf_map_map F (homOfLE (inf_le_inf_left (U A 0) inf_le_right))
      (homOfLE (le_inf inf_le_left le_rfl)) (homOfLE le_rfl) (twistFst p)).trans
        (presheaf_map_map F _ ι (homOfLE le_rfl) (twistFst p)).symm
  have l2 : F.presheaf.map ι.op (F.presheaf.map (homOfLE (inf_le_inf_right (U A 1) inf_le_right) :
      (U A 0 ⊓ U A 1) ⊓ U A 1 ⟶ U A 1 ⊓ U A 1).op (twistSnd p)) =
        F.presheaf.map (homOfLE (inf_le_right : U A 0 ⊓ U A 1 ≤ U A 1)).op
          (twistAppEquivRight (le_rfl : U A 1 ≤ U A 1) p) :=
    (presheaf_map_map F _ _ (homOfLE (le_inf inf_le_right inf_le_right)) _).trans
      (presheaf_map_map F _ _ _ _).symm
  have l3 : (scheme A).presheaf.map ι.op ((scheme A).presheaf.map (homOfLE inf_le_left :
      (U A 0 ⊓ U A 1) ⊓ U A 1 ⟶ U A 0 ⊓ U A 1).op (transition A d)) = transition A d := by
    rw [scheme_presheaf_map_map_comp, scheme_presheaf_map_congr _ (𝟙 _)]
    simp
  rw [l1, c', l2, l3, tA_zpow_apply]
  rfl

/-- The chart module of `F(d)` is the twist of the chart module of `F`. -/
noncomputable def chartModuleTwistHom :
    ChartModule.Hom (chartModule (serreTwist A F d)) ((chartModule F).twist d) where
  f0 :=
    { toFun := twistAppEquivLeft (isUnit_transition A d) (le_rfl : U A 0 ≤ U A 0)
      map_add' := map_add _
      map_smul' a p := twistAppEquivLeft_smul _ _ (secMap A (U A 0) a) p }
  f1 :=
    { toFun := twistAppEquivRight (le_rfl : U A 1 ≤ U A 1)
      map_add' := map_add _
      map_smul' a p := twistAppEquivRight_smul _ (secMap A (U A 1) a) p }
  f01 :=
    { toFun := twistAppEquivLeft (isUnit_transition A d) (inf_le_left : U A 0 ⊓ U A 1 ≤ U A 0)
      map_add' := map_add _
      map_smul' a p := twistAppEquivLeft_smul _ _ (secMap A (U A 0 ⊓ U A 1) a) p }
  comm_x0 p := twistAppEquivLeft_smul _ _ (coord A 0) p
  comm_x1 p := twistAppEquivRight_smul _ (coord A 1) p
  comm_t z := twistAppEquivLeft_smul _ _ (transition A 1) z
  comm_r0 p := twistAppEquivLeft_res (isUnit_transition A d) le_rfl inf_le_left p
  comm_r1 p := twist_r1 F d p

/-- **The chart module of a Serre twist** is the twist of the chart module. -/
noncomputable def chartModuleTwistIso :
    chartModule (serreTwist A F d) ≅ (chartModule F).twist d :=
  haveI := ChartModule.Hom.isIso_of_bijective (M := chartModule (serreTwist A F d))
    (N := (chartModule F).twist d) (chartModuleTwistHom F d)
    (twistAppEquivLeft (isUnit_transition A d) (le_rfl : U A 0 ≤ U A 0)).bijective
    (twistAppEquivRight (le_rfl : U A 1 ≤ U A 1)).bijective
    (twistAppEquivLeft (isUnit_transition A d) (inf_le_left : U A 0 ⊓ U A 1 ≤ U A 0)).bijective
  asIso (C := ChartModule A) (chartModuleTwistHom F d)

end ProjectiveLine
