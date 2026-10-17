/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.QcohTwoCech
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Sheaves.AddCommGrpCat
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# Epimorphisms of sheaves of modules are locally surjective

In the abelian category `SheafOfModules R` of sheaves of modules over a sheaf of rings, colimits
are computed by sheafifying the colimit of the underlying presheaves of modules. Since
sheafification commutes with forgetting the module structure, the forgetful functor
`SheafOfModules.toSheaf R` to sheaves of abelian groups preserves colimits
(`SheafOfModules.preservesColimitsOfShape_toSheaf'`), hence epimorphisms. An epimorphism of
sheaves of abelian groups on a topological space is locally surjective
(`TopCat.Sheaf.isLocallySurjective_iff_epi`), so:

* `AlgebraicGeometry.Scheme.Modules.isLocallySurjective_iff_epi`: a morphism of `𝒪_X`-modules is
  an epimorphism of `X.Modules` iff it is locally surjective, i.e. surjective on stalks (the
  surjectivity case of Stacks, Lemma 17.3.1, Tag 01AG: exactness in `Mod(𝒪_X)` is stalkwise);
* `AlgebraicGeometry.Scheme.Modules.IsShortExactSheaf.of_shortExact'`: every short exact sequence
  of the abelian category `X.Modules` is a short exact sequence of sheaves, so the six-term Čech
  sequence of `FormalSchemes.QcohTwoCech` applies to it without any local surjectivity hypothesis.
-/

universe w' w v u' u

open CategoryTheory Limits

namespace SheafOfModules

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})
  [HasSheafify J AddCommGrpCat.{v}] [J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- The forgetful functor from sheaves of modules to sheaves of abelian groups preserves the
colimits which exist for presheaves of modules: a colimit of sheaves of modules is the
sheafification of the colimit of the underlying presheaves, and sheafification commutes with
forgetting the module structure. -/
noncomputable instance preservesColimitsOfShape_toSheaf' (K : Type w) [Category.{w'} K]
    [HasColimitsOfShape K AddCommGrpCat.{v}] :
    PreservesColimitsOfShape K (toSheaf.{v} R) where
  preservesColimit {F} := by
    let adj := PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)
    let L := PresheafOfModules.sheafification.{v} (𝟙 R.obj)
    let c0 := colimit.cocone (F ⋙ forget R)
    have h0 : IsColimit (L.mapCocone c0) := isColimitOfPreserves L (colimit.isColimit _)
    let e : F ⋙ forget R ⋙ L ≅ F := Functor.isoWhiskerLeft F (asIso adj.counit)
    let c := (Cocone.precompose e.inv).obj (L.mapCocone c0)
    have hc : IsColimit c := (IsColimit.precomposeInvEquiv e _).symm h0
    apply preservesColimit_of_preserves_colimit_cocone hc
    haveI : PreservesColimitsOfShape K (L ⋙ toSheaf.{v} R) :=
      preservesColimitsOfShape_of_natIso
        (PresheafOfModules.sheafificationCompToSheaf (𝟙 R.obj)).symm
    have h1 : IsColimit ((L ⋙ toSheaf R).mapCocone c0) :=
      isColimitOfPreserves (L ⋙ toSheaf R) (colimit.isColimit _)
    have h2 : IsColimit ((toSheaf R).mapCocone (L.mapCocone c0)) :=
      h1.ofIsoColimit (Cocone.ext (Iso.refl _))
    exact IsColimit.ofIsoColimit
      ((IsColimit.precomposeInvEquiv (Functor.isoWhiskerRight e (toSheaf R)) _).symm h2)
      (Functor.mapCoconePrecompose (toSheaf R)).symm

/-- The forgetful functor from sheaves of modules to sheaves of abelian groups preserves
epimorphisms. -/
noncomputable instance preservesEpimorphisms_toSheaf' : (toSheaf.{v} R).PreservesEpimorphisms :=
  inferInstance

end SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules}

/-- A morphism of `𝒪_X`-modules is an epimorphism iff it is locally surjective. -/
lemma isLocallySurjective_iff_epi (φ : M ⟶ N) :
    TopCat.Presheaf.IsLocallySurjective φ.mapPresheaf ↔ Epi φ := by
  let F := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  let M' : SheafOfModules.{u} X.ringCatSheaf := M
  let N' : SheafOfModules.{u} X.ringCatSheaf := N
  let φ' : M' ⟶ N' := φ
  have key : TopCat.Presheaf.IsLocallySurjective φ.mapPresheaf ↔ Epi (F.map φ') :=
    TopCat.Sheaf.isLocallySurjective_iff_epi (F.map φ')
  rw [key]
  constructor
  · intro h
    exact F.epi_of_epi_map h
  · intro h
    haveI : Epi φ' := ⟨fun g₁ g₂ hg ↦ h.left_cancellation g₁ g₂ hg⟩
    exact F.map_epi φ'

/-- An epimorphism of `𝒪_X`-modules is locally surjective. -/
lemma isLocallySurjective_of_epi (φ : M ⟶ N) [Epi φ] :
    TopCat.Presheaf.IsLocallySurjective φ.mapPresheaf :=
  (isLocallySurjective_iff_epi φ).2 inferInstance

/-- Every short exact sequence of the abelian category `X.Modules` is a short exact sequence of
sheaves: left exact on all sections and locally surjective on the right. -/
lemma IsShortExactSheaf.of_shortExact' {S : ShortComplex X.Modules} (hS : S.ShortExact) :
    IsShortExactSheaf S.f S.g :=
  haveI := hS.epi_g
  IsShortExactSheaf.of_shortExact hS (isLocallySurjective_of_epi S.g)

end AlgebraicGeometry.Scheme.Modules
