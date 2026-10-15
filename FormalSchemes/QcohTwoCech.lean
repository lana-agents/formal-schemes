/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.SchemeTwoCech
import FormalSchemes.QcohSpecSections
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# The Čech sequence of a short exact sequence of quasi-coherent modules

A sequence `M' ⟶ M ⟶ M''` of `𝒪_X`-modules is a short exact sequence of sheaves
(`Scheme.Modules.IsShortExactSheaf`) if it is left exact on all sections and `M ⟶ M''` is
locally surjective. When `M` and `M''` are quasi-coherent, such a sequence is short exact on the
sections over every affine open (`Scheme.Modules.IsShortExactSheaf.shortExactOn`, from
`AlgebraicGeometry.surjective_app_of_isAffineOpen`). So for two affine opens `U`, `V` with affine
intersection — e.g. any two affine opens when `X` has affine diagonal, in particular when `X` is
separated (Stacks, Lemma 30.2.5, Tag 0BDX) — the six-term sequence of
`FormalSchemes.SchemeTwoCech` applies:

`0 → Ȟ⁰(M') → Ȟ⁰(M) → Ȟ⁰(M'') → Ȟ¹(M') → Ȟ¹(M) → Ȟ¹(M'') → 0`.

Since `Ȟ⁰ = Γ(U ∪ V, -)` (`Scheme.Modules.cechH0Equiv`) and the Čech complex of a covering by
affines with affine intersection computes cohomology of quasi-coherent modules (Stacks,
Lemma 30.2.6, Tag 01XD), this is the long exact cohomology sequence of a scheme covered by two
affines, with `H² = 0`. For a curve over a Noetherian base this is the right exactness of `H¹`
used in the Grothendieck existence theorem.
-/

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M' M M'' : X.Modules}

/-- `M' ⟶ M ⟶ M''` is a short exact sequence of sheaves of modules: left exact on the sections over
every open, and locally surjective on the right. -/
structure IsShortExactSheaf (φ : M' ⟶ M) (ψ : M ⟶ M'') : Prop where
  injective (W : X.Opens) : Function.Injective (φ.app W)
  exact (W : X.Opens) : Function.Exact (φ.app W) (ψ.app W)
  isLocallySurjective : TopCat.Presheaf.IsLocallySurjective ψ.mapPresheaf

variable {φ : M' ⟶ M} {ψ : M ⟶ M''}

/-- A short exact sequence of sheaves whose middle and right terms are quasi-coherent is short exact
on the sections over each affine open. -/
lemma IsShortExactSheaf.shortExactOn [M.IsQuasicoherent] [M''.IsQuasicoherent]
    (h : IsShortExactSheaf φ ψ) {W : X.Opens} (hW : IsAffineOpen W) : ShortExactOn φ ψ W :=
  ⟨h.injective W, h.exact W, surjective_app_of_isAffineOpen ψ h.isLocallySurjective hW⟩

section TwoAffines

variable [M.IsQuasicoherent] [M''.IsQuasicoherent] (h : IsShortExactSheaf φ ψ) {U V : X.Opens}
  (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : IsAffineOpen (U ⊓ V))

/-- The connecting map `Ȟ⁰(M'') → Ȟ¹(M')` of a short exact sequence of quasi-coherent modules, for
two affine opens with affine intersection. -/
noncomputable def IsShortExactSheaf.δ : cechH0 M'' U V →ₗ[ℤ] cechH1 M' U V :=
  cechδ U V φ ψ (h.shortExactOn hU) (h.shortExactOn hV) (h.shortExactOn hUV)

include h hU hV in
lemma IsShortExactSheaf.cechMapH0_injective : Function.Injective (cechMapH0 U V φ) :=
  Scheme.Modules.cechMapH0_injective U V φ ψ (h.shortExactOn hU) (h.shortExactOn hV)

include h hU hV hUV in
lemma IsShortExactSheaf.exact_cechMapH0 :
    Function.Exact (cechMapH0 U V φ) (cechMapH0 U V ψ) :=
  Scheme.Modules.exact_cechMapH0 U V φ ψ (h.shortExactOn hU) (h.shortExactOn hV)
    (h.shortExactOn hUV)

lemma IsShortExactSheaf.exact_cechMapH0_δ :
    Function.Exact (cechMapH0 U V ψ) (h.δ hU hV hUV) :=
  Scheme.Modules.exact_cechMapH0_cechδ U V φ ψ _ _ _

lemma IsShortExactSheaf.exact_δ_cechMapH1 :
    Function.Exact (h.δ hU hV hUV) (cechMapH1 U V φ) :=
  Scheme.Modules.exact_cechδ_cechMapH1 U V φ ψ _ _ _

include h hU hV hUV in
lemma IsShortExactSheaf.exact_cechMapH1 :
    Function.Exact (cechMapH1 U V φ) (cechMapH1 U V ψ) :=
  Scheme.Modules.exact_cechMapH1 U V φ ψ (h.shortExactOn hU) (h.shortExactOn hV)
    (h.shortExactOn hUV)

include h hUV in
/-- `Ȟ¹` of a covering by two affines with affine intersection is right exact on quasi-coherent
modules: `H²` vanishes. -/
lemma IsShortExactSheaf.cechMapH1_surjective : Function.Surjective (cechMapH1 U V ψ) :=
  Scheme.Modules.cechMapH1_surjective U V φ ψ (h.shortExactOn hUV)

end TwoAffines

/-- On a scheme with affine diagonal (e.g. a separated scheme), the intersection of two affine opens
is affine (Stacks, Lemma 30.2.5, Tag 0BDX), so the six-term sequence applies to any two affine
opens. -/
lemma isAffineOpen_inf_of_affineDiagonal
    [IsAffineHom (Limits.pullback.diagonal (Limits.terminal.from X))] {U V : X.Opens}
    (hU : IsAffineOpen U) (hV : IsAffineOpen V) : IsAffineOpen (U ⊓ V) :=
  hU.inf hV

end AlgebraicGeometry.Scheme.Modules
