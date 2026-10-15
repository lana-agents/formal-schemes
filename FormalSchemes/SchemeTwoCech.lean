/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.TwoCech
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Čech cohomology of a two-set open covering of a scheme

For a sheaf of `𝒪_X`-modules `M` on a scheme `X` and two opens `U`, `V`, the ordered Čech
complex of the covering `(U, V)` of `U ∪ V` (Stacks, Definition 20.23.2, Tag 01FI) is
`Γ(M, U) × Γ(M, V) → Γ(M, U ∩ V)`, `(s, t) ↦ s| - t|`, and vanishes in degrees `≥ 2`. This file
specialises the algebra of `FormalSchemes.TwoCech` to it:

* `Scheme.Modules.cechH0`, `Scheme.Modules.cechH1`: its cohomology, as abelian groups;
* `Scheme.Modules.cechH0Equiv`: by the sheaf axiom, `Γ(M, U ∪ V) ≃ Ȟ⁰`;
* `Scheme.Modules.cechMapH0`, `Scheme.Modules.cechMapH1`: functoriality in `M`;
* for morphisms `M' ⟶ M ⟶ M''` which are short exact on the sections over `U`, `V` and `U ∩ V`,
  the six-term exact sequence (`Scheme.Modules.cechδ` and the lemmas following it).

When `M'`, `M`, `M''` are quasi-coherent and `U`, `V`, `U ∩ V` are affine, the sections over
these opens of a short exact sequence are short exact (Stacks, Lemma 30.2.2, Tag 01XB), and
`Ȟ¹` of the covering computes `H¹(U ∪ V, -)` (Stacks, Lemma 30.2.6, Tag 01XD); the six-term
sequence is then the Mayer–Vietoris sequence (Stacks, Lemma 20.8.2, Tag 01EB) and its last
surjection is the vanishing of `H²`.
-/

universe u

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The restriction map `Γ(M, U) → Γ(M, W)` along `W ≤ U`, as a `ℤ`-linear map. -/
noncomputable def resℤ (M : X.Modules) {U W : X.Opens} (h : W ≤ U) :
    Γ(M, U) →ₗ[ℤ] Γ(M, W) :=
  (M.presheaf.map (homOfLE h).op).hom.toIntLinearMap

@[simp]
lemma resℤ_apply (M : X.Modules) {U W : X.Opens} (h : W ≤ U) (s : Γ(M, U)) :
    resℤ M h s = M.presheaf.map (homOfLE h).op s := rfl

/-- The map on sections `Γ(M, U) → Γ(N, U)` of a morphism of modules, as a `ℤ`-linear map. -/
noncomputable def appℤ {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens) : Γ(M, U) →ₗ[ℤ] Γ(N, U) :=
  (φ.app U).hom.toIntLinearMap

@[simp]
lemma appℤ_apply {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens) (s : Γ(M, U)) :
    appℤ φ U s = φ.app U s := rfl

lemma appℤ_comp_resℤ {M N : X.Modules} (φ : M ⟶ N) {U W : X.Opens} (h : W ≤ U) :
    appℤ φ W ∘ₗ resℤ M h = resℤ N h ∘ₗ appℤ φ U := by
  ext s
  simp only [LinearMap.comp_apply, appℤ_apply, resℤ_apply]
  rw [← mapPresheaf_app, ← mapPresheaf_app, ← ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply, NatTrans.naturality]

variable (M : X.Modules) (U V : X.Opens)

/-- The Čech `H⁰` of the covering `(U, V)` of `U ∪ V` with coefficients in `M`. -/
noncomputable abbrev cechH0 : Submodule ℤ (Γ(M, U) × Γ(M, V)) :=
  TwoCech.H0 (resℤ M (inf_le_left : U ⊓ V ≤ U)) (resℤ M (inf_le_right : U ⊓ V ≤ V))

/-- The Čech `H¹` of the covering `(U, V)` of `U ∪ V` with coefficients in `M`. -/
noncomputable abbrev cechH1 : Type u :=
  TwoCech.H1 (resℤ M (inf_le_left : U ⊓ V ≤ U)) (resℤ M (inf_le_right : U ⊓ V ≤ V))

/-- Restricting in two steps is restricting in one step. -/
lemma res_res (M : X.Modules) {U W T : X.Opens} (i : W ⟶ U) (j : T ⟶ W) (k : T ⟶ U)
    (s : Γ(M, U)) : M.presheaf.map j.op (M.presheaf.map i.op s) = M.presheaf.map k.op s := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The map `Γ(M, U ∪ V) → Ȟ⁰`, restricting a section to both opens. -/
noncomputable def toCechH0 : Γ(M, U ⊔ V) →ₗ[ℤ] cechH0 M U V :=
  LinearMap.codRestrict _ ((resℤ M le_sup_left).prod (resℤ M le_sup_right)) fun s ↦ by
    rw [TwoCech.mem_H0]
    change M.presheaf.map _ (M.presheaf.map _ s) = M.presheaf.map _ (M.presheaf.map _ s)
    rw [res_res M _ _ (homOfLE (inf_le_left.trans le_sup_left)), res_res]

/-- The sheaf axiom for `M`: sections over `U ∪ V` are exactly the pairs of sections over `U`
and `V` agreeing on `U ∩ V`; i.e. `Ȟ⁰` of the covering is `Γ(M, U ∪ V)`. -/
lemma toCechH0_bijective : Function.Bijective (toCechH0 M U V) := by
  let F : TopCat.Sheaf Ab X := ⟨M.presheaf, M.isSheaf⟩
  constructor
  · intro s t h
    have h' := congrArg Subtype.val h
    exact F.eq_of_locally_eq₂ (homOfLE le_sup_left) (homOfLE le_sup_right) le_rfl s t
      (congrArg Prod.fst h') (congrArg Prod.snd h')
  · rintro ⟨⟨a, b⟩, hab⟩
    rw [TwoCech.mem_H0] at hab
    simp only [resℤ_apply] at hab
    let W : Bool → X.Opens := fun i ↦ cond i U V
    let sf : ∀ i, ToType (F.1.obj (op (W i))) := fun i ↦ match i with
      | true => a
      | false => b
    have hc : TopCat.Presheaf.IsCompatible F.1 W sf := by
      rintro (_ | _) (_ | _)
      · rfl
      · have := congrArg (M.presheaf.map (homOfLE (le_of_eq (inf_comm V U))).op) hab
        rw [res_res, res_res] at this
        exact this.symm
      · exact hab
      · rfl
    obtain ⟨s, hs, -⟩ := F.existsUnique_gluing' W (U ⊔ V)
      (fun i ↦ match i with
        | true => homOfLE le_sup_left
        | false => homOfLE le_sup_right)
      (sup_le (le_iSup W true) (le_iSup W false)) sf hc
    exact ⟨s, Subtype.ext (Prod.ext (hs true) (hs false))⟩

/-- `Γ(M, U ∪ V) ≃ Ȟ⁰` of the covering `(U, V)`. -/
noncomputable def cechH0Equiv : Γ(M, U ⊔ V) ≃ₗ[ℤ] cechH0 M U V :=
  LinearEquiv.ofBijective _ (toCechH0_bijective M U V)

/-! ### Functoriality and the six-term exact sequence -/

variable {M} {N : X.Modules}

/-- The map on `Ȟ⁰` of the covering `(U, V)` induced by a morphism of modules. -/
noncomputable def cechMapH0 (φ : M ⟶ N) : cechH0 M U V →ₗ[ℤ] cechH0 N U V :=
  TwoCech.mapH0 (appℤ φ U) (appℤ φ V) (appℤ φ (U ⊓ V)) (appℤ_comp_resℤ φ _).symm
    (appℤ_comp_resℤ φ _).symm

/-- The map on `Ȟ¹` of the covering `(U, V)` induced by a morphism of modules. -/
noncomputable def cechMapH1 (φ : M ⟶ N) : cechH1 M U V →ₗ[ℤ] cechH1 N U V :=
  TwoCech.mapH1 (appℤ φ U) (appℤ φ V) (appℤ φ (U ⊓ V)) (appℤ_comp_resℤ φ _).symm
    (appℤ_comp_resℤ φ _).symm

/-- The identification `Γ(M, U ∪ V) ≃ Ȟ⁰` is natural in `M`. -/
lemma cechMapH0_toCechH0 (φ : M ⟶ N) (s : Γ(M, U ⊔ V)) :
    cechMapH0 U V φ (toCechH0 M U V s) = toCechH0 N U V (φ.app _ s) := by
  ext
  · exact LinearMap.congr_fun (appℤ_comp_resℤ φ (le_sup_left : U ≤ U ⊔ V)) s
  · exact LinearMap.congr_fun (appℤ_comp_resℤ φ (le_sup_right : V ≤ U ⊔ V)) s

/-- A pair of morphisms `M' ⟶ M ⟶ M''` is short exact on the sections over `W`. -/
def ShortExactOn {M' M M'' : X.Modules} (φ : M' ⟶ M) (ψ : M ⟶ M'') (W : X.Opens) : Prop :=
  Function.Injective (φ.app W) ∧ Function.Exact (φ.app W) (ψ.app W) ∧
    Function.Surjective (ψ.app W)

section SES

variable {M' M M'' : X.Modules} (φ : M' ⟶ M) (ψ : M ⟶ M'')
  (hU : ShortExactOn φ ψ U) (hV : ShortExactOn φ ψ V) (hUV : ShortExactOn φ ψ (U ⊓ V))

include hU hV in
/-- `Ȟ⁰(M') → Ȟ⁰(M)` is injective. -/
lemma cechMapH0_injective : Function.Injective (cechMapH0 U V φ) :=
  TwoCech.mapH0_injective _ _ _ _ _ hU.1 hV.1

include hU hV hUV in
/-- `Ȟ⁰(M') → Ȟ⁰(M) → Ȟ⁰(M'')` is exact. -/
lemma exact_cechMapH0 : Function.Exact (cechMapH0 U V φ) (cechMapH0 U V ψ) :=
  TwoCech.exact_mapH0 _ _ _ _ _ _ _ _ _ _ hU.2.1 hV.2.1 hUV.1

/-- The connecting map `Ȟ⁰(M'') → Ȟ¹(M')` of the covering `(U, V)`. -/
noncomputable def cechδ : cechH0 M'' U V →ₗ[ℤ] cechH1 M' U V :=
  TwoCech.δ (appℤ φ U) (appℤ φ V) (appℤ φ (U ⊓ V)) (appℤ ψ U) (appℤ ψ V) (appℤ ψ (U ⊓ V))
    (appℤ_comp_resℤ φ _).symm (appℤ_comp_resℤ φ _).symm (appℤ_comp_resℤ ψ _).symm
    (appℤ_comp_resℤ ψ _).symm hU.2.1 hV.2.1 hUV.2.1 hU.2.2 hV.2.2 hUV.1

/-- `Ȟ⁰(M) → Ȟ⁰(M'') → Ȟ¹(M')` is exact. -/
lemma exact_cechMapH0_cechδ :
    Function.Exact (cechMapH0 U V ψ) (cechδ U V φ ψ hU hV hUV) :=
  TwoCech.exact_mapH0_δ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- `Ȟ⁰(M'') → Ȟ¹(M') → Ȟ¹(M)` is exact. -/
lemma exact_cechδ_cechMapH1 :
    Function.Exact (cechδ U V φ ψ hU hV hUV) (cechMapH1 U V φ) :=
  TwoCech.exact_δ_mapH1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

include hU hV hUV in
/-- `Ȟ¹(M') → Ȟ¹(M) → Ȟ¹(M'')` is exact. -/
lemma exact_cechMapH1 : Function.Exact (cechMapH1 U V φ) (cechMapH1 U V ψ) :=
  TwoCech.exact_mapH1 _ _ _ _ _ _ _ _ _ _ hU.2.2 hV.2.2 hUV.2.1

include hUV in
/-- `Ȟ¹(M) → Ȟ¹(M'')` is surjective: Čech `H²` of a two-set covering vanishes. -/
lemma cechMapH1_surjective : Function.Surjective (cechMapH1 U V ψ) :=
  TwoCech.mapH1_surjective _ _ _ _ _ hUV.2.2

end SES

end AlgebraicGeometry.Scheme.Modules
