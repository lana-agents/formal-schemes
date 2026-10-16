/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.QcohSpecSections
import FormalSchemes.TwoSetTwist

/-!
# Sections of a quasi-coherent module over a basic open of an affine open

For a quasi-coherent module `M` on a scheme `X`, an affine open `U` and `f ∈ Γ(X, U)`, the
restriction `Γ(M, U) → Γ(M, D(f))` is a localization at `f`; this is deduced from the case of
`Spec` (`FormalSchemes.QcohSpecSections`) by transport along `fromSpec : Spec Γ(X, U) → X`:

* `Scheme.Modules.exists_pow_smul_eq_res`: every section over `D(f)` times a power of `f` comes
  from `U`;
* `Scheme.Modules.exists_pow_smul_eq_zero`: a section over `U` vanishing on `D(f)` is killed by a
  power of `f`.
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry

namespace Scheme.Modules

variable {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)

lemma image_fromSpec_le (V : (Spec Γ(X, U)).Opens) : hU.fromSpec ''ᵁ V ≤ U :=
  (hU.fromSpec.image_le_opensRange V).trans hU.opensRange_fromSpec.le

/-- The ring map `Γ(X, U) → Γ(Spec Γ(X, U), V) → Γ(X, fromSpec(V))` is the restriction. -/
lemma fromSpec_appIso_inv_res (V : (Spec Γ(X, U)).Opens) (r : Γ(X, U)) :
    (hU.fromSpec.appIso V).inv ((Spec Γ(X, U)).presheaf.map (homOfLE le_top).op
      ((Scheme.ΓSpecIso Γ(X, U)).inv r)) =
      X.presheaf.map (homOfLE (image_fromSpec_le hU V)).op r := by
  have key : (hU.fromSpec.appIso V).hom
      (X.presheaf.map (homOfLE (image_fromSpec_le hU V)).op r) =
      (Spec Γ(X, U)).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso Γ(X, U)).inv r) := by
    rw [Scheme.Hom.appIso_hom, ← CommRingCat.comp_apply, ← Category.assoc,
      hU.fromSpec.naturality, hU.fromSpec_app_self]
    simp only [Category.assoc, ← Functor.map_comp]
    rfl
  rw [← key, ← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]

lemma spec_smul_eq {R : CommRingCat.{u}} (M : (Spec R).Modules) (V : (Spec R).Opens) (r : R)
    (x : (modulesSpecToSheaf.obj M).obj.obj (op V)) :
    r • x = (show Γ(M, V) from ((Spec R).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
      ((Scheme.ΓSpecIso R).inv r) : Γ(Spec R, V)) • (show Γ(M, V) from x)) := rfl

lemma restrict_smul_eq {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] (M : X.Modules)
    (V : Y.Opens) (s : Γ(Y, V)) (x : Γ(M.restrict g, V)) :
    s • x = (show Γ(M, g ''ᵁ V) from (g.appIso V).inv s • (show Γ(M, g ''ᵁ V) from x)) := rfl

lemma image_fromSpec_top : hU.fromSpec ''ᵁ ⊤ = U := by
  rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]

include hU in
/-- **Kernel of the restriction to a basic open**: a section over an affine `U` vanishing on `D(f)`
is killed by a power of `f`. -/
theorem exists_pow_smul_eq_zero (M : X.Modules) [M.IsQuasicoherent] (f : Γ(X, U))
    (m : Γ(M, U)) (hm : M.presheaf.map (homOfLE (X.basicOpen_le f)).op m = 0) :
    ∃ k : ℕ, f ^ k • m = 0 := by
  let g := hU.fromSpec
  have eT := image_fromSpec_top hU
  have eF : g ''ᵁ PrimeSpectrum.basicOpen f = X.basicOpen f := hU.fromSpec_image_basicOpen f
  let m' : Γ(M.restrict g, ⊤) := M.presheaf.map (homOfLE eT.le).op m
  have hres : specRes (M.restrict g) (le_top : PrimeSpectrum.basicOpen f ≤ ⊤) m' = 0 := by
    change M.presheaf.map (homOfLE (g.image_mono le_top)).op (M.presheaf.map _ m) = 0
    rw [presheaf_map_map_comp, presheaf_map_congr M _
      (homOfLE eF.le ≫ homOfLE (X.basicOpen_le f)), ← presheaf_map_map_comp, hm, map_zero]
  obtain ⟨⟨s, hs⟩, hsz⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f)
    (f := specRes (M.restrict g) (le_top : PrimeSpectrum.basicOpen f ≤ ⊤))
    (hres.trans (map_zero _).symm)
  obtain ⟨k, rfl⟩ := hs
  refine ⟨k, ?_⟩
  rw [smul_zero] at hsz
  have hsz' := ((restrict_smul_eq g M ⊤ _ m').symm.trans
    ((spec_smul_eq (M.restrict g) ⊤ (f ^ k) m').symm.trans hsz))
  rw [fromSpec_appIso_inv_res] at hsz'
  have h2 : M.presheaf.map (homOfLE eT.le).op (f ^ k • m) = 0 := by
    rw [map_smul]
    exact hsz'
  have h3 := congrArg (M.presheaf.map (homOfLE eT.ge).op) h2
  rw [presheaf_map_map_comp, presheaf_map_congr M _ (𝟙 U), map_zero] at h3
  simpa using h3

include hU in
/-- **Sections over a basic open**: every section of `M` over `D(f)`, multiplied by a power of `f`,
comes from the affine open `U`. -/
theorem exists_pow_smul_eq_res (M : X.Modules) [M.IsQuasicoherent] (f : Γ(X, U))
    (z : Γ(M, X.basicOpen f)) : ∃ (m : Γ(M, U)) (k : ℕ),
      X.presheaf.map (homOfLE (X.basicOpen_le f)).op (f ^ k) • z =
        M.presheaf.map (homOfLE (X.basicOpen_le f)).op m := by
  let g := hU.fromSpec
  have eT := image_fromSpec_top hU
  have eF : g ''ᵁ PrimeSpectrum.basicOpen f = X.basicOpen f := hU.fromSpec_image_basicOpen f
  let z' : Γ(M.restrict g, PrimeSpectrum.basicOpen f) := M.presheaf.map (homOfLE eF.le).op z
  obtain ⟨⟨m', ⟨s, hs⟩⟩, hsz⟩ := IsLocalizedModule.surj (Submonoid.powers f)
    (specRes (M.restrict g) (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)) z'
  obtain ⟨k, rfl⟩ := hs
  refine ⟨M.presheaf.map (homOfLE eT.ge).op m', k, ?_⟩
  have hsz' := ((restrict_smul_eq g M _ _ z').symm.trans
    ((spec_smul_eq (M.restrict g) _ (f ^ k) z').symm.trans hsz))
  rw [fromSpec_appIso_inv_res] at hsz'
  have h3 := congrArg (M.presheaf.map (homOfLE eF.ge).op) hsz'
  rw [map_smul] at h3
  change _ • M.presheaf.map _ (M.presheaf.map _ z) =
    M.presheaf.map _ (M.presheaf.map (homOfLE (g.image_mono le_top)).op m') at h3
  simp only [presheaf_map_map_comp, scheme_presheaf_map_map_comp] at h3 ⊢
  rw [presheaf_map_congr M _ (𝟙 _), scheme_presheaf_map_congr _
    (homOfLE (X.basicOpen_le f))] at h3
  simp only [op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] at h3
  rw [h3]
  exact presheaf_map_congr M _ _ _

end Scheme.Modules

end AlgebraicGeometry
