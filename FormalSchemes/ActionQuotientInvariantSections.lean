import FormalSchemes.ActionQuotientSections

set_option linter.style.header false

/-!
# The sections of an action quotient are the invariant sections

`FormalSchemes.ActionQuotientSections` describes the sections of `CategoryTheory.actionQuotient`
as the sections *equalised by the two legs* of the defining coequalizer. That is the shape the
coequalizer hands over, and it is not the shape a geometric argument wants: the common source of
the two legs is the coproduct `∐_{g : G} X`, so "equalised" is a statement about a single section
of a coproduct rather than a family of statements about `X`.

This file turns it into the family. A section of `X` over `π⁻¹ V` descends to the quotient **if
and only if** it is invariant under every `a g`, which is the description the stalk lemma for a
free, properly discontinuous action needs.

## What it takes

Three things, none of them deep and none of them free.

* **The coproduct has its own comparison isomorphism.** `∐_{g : G} X` in `LocallyRingedSpace` is
  no more definitionally the coproduct of the underlying presheafed spaces than the coequalizer
  was, so `sigmaIsoPresheafedSpace` is built the same way, out of the two `preservesColimitIso`s,
  and `ι_comp_sigmaIsoPresheafedSpace_hom` says it carries the coproduct legs to the coproduct
  legs. `sigma_section_ext` then transports
  `AlgebraicGeometry.PresheafedSpace.colimit_section_ext` upstairs: a section of `∐_{g : G} X` is
  determined by its pullbacks along the legs. This is what makes the family of conditions
  equivalent to the single one.
* **The legs read off the action.** `CategoryTheory.ι_actionQuotientLeft` and
  `CategoryTheory.ι_actionQuotientRight` say `Sigma.ι _ g ≫ actionQuotientLeft a = (a g).hom` and
  `Sigma.ι _ g ≫ actionQuotientRight G X = 𝟙 X`, and applying the two forgetful functors and
  `AlgebraicGeometry.PresheafedSpace.congr_app` turns them into
  `ι_c_app_actionQuotientLeft` and `ι_c_app_actionQuotientRight`, which is where the `𝟙` collapses
  and produces the section back.
* **The open is stable.** `eq_preimage_of_preimage_actionQuotient_eq`: pulling the coequalizer
  condition `r⁻¹ W = l⁻¹ W` back along the `g`-th leg gives `W = (a g)⁻¹ W`, which is what lets the
  invariance equation be stated at all. It is not an extra hypothesis — it follows from the one
  the descent criterion already carries.

Every comparison of sections living on two different opens goes through
`AlgebraicGeometry.PresheafedSpace.map_eqToHom_eq_iff`, `map_eqToHom_trans_apply` and
`c_app_map_eqToHom`, the last two proved by `subst` on the equality of opens, which is available
exactly because those opens are universally quantified there and not in the statements that use
them.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.sigmaIsoPresheafedSpace`,
  `ι_comp_sigmaIsoPresheafedSpace_hom`, `sigma_section_ext`: the coproduct comparison isomorphism,
  and extensionality of sections of a coproduct of locally ringed spaces.
* `AlgebraicGeometry.LocallyRingedSpace.c_app_actionQuotientLeft_eq_iff`: the two pullbacks of `s`
  agree if and only if `s` is invariant under every `a g`.
* `CategoryTheory.exists_actionQuotientπ_c_app_eq_iff_forall`: **the headline** — a section of `X`
  over `π⁻¹ V` is the pullback of a section of `X / G` over `V` if and only if it is invariant.

## Why the headline is not vacuous

`bijective_actionQuotientπ_c_app_one` runs it on the trivial action, where every section is
invariant, and gets that `π` is an isomorphism on sections — which is right, the quotient by the
trivial action being `X` itself. That conclusion is reachable independently, since the two legs
of the trivial action are equal and
`AlgebraicGeometry.LocallyRingedSpace.bijective_coequalizer_self_π_c_app` applies; the two routes
agree.

## What this does not do

It does not prove the stalk lemma. What remains of it is the *geometric* step and nothing else:
over an open `U` on which the action is properly discontinuous, `π⁻¹ (π '' V')` is the disjoint
union of the translates `(a g)(V')`, so an invariant section is freely determined by its
restriction to `V'`, and the colimit over `V` of the invariant sections is `X`'s stalk. That is
where `AlgebraicGeometry.LocallyRingedSpace.IsProperlyDiscontinuousOn` enters, and it is the only
part of the argument that is not bookkeeping about comparison isomorphisms.

## References

* [The Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ).
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.PresheafedSpace

theorem map_eqToHom_trans_apply {Z : TopCat.{u}} (F : (Opens Z)ᵒᵖ ⥤ CommRingCat.{u})
    {A B C : Opens Z} (p : A = B) (q : B = C) (x : ToType (F.obj (op A))) :
    (F.map (eqToHom (congrArg op q))) ((F.map (eqToHom (congrArg op p))) x) =
      (F.map (eqToHom (congrArg op (p.trans q)))) x := by
  subst p; subst q; simp

theorem c_app_map_eqToHom {Z Zg : PresheafedSpace.{u} CommRingCat.{u}} (α : Z ⟶ Zg)
    {A B : Opens Zg.carrier} (hAB : A = B) (y : ToType (Zg.presheaf.obj (op A))) :
    (α.c.app (op B)) ((Zg.presheaf.map (eqToHom (congrArg op hAB))) y) =
      (Z.presheaf.map (eqToHom (congrArg op (congrArg (Opens.map α.base).obj hAB))))
        ((α.c.app (op A)) y) := by
  subst hAB; simp

end AlgebraicGeometry.PresheafedSpace

namespace AlgebraicGeometry.LocallyRingedSpace

section Sigma

variable {G : Type u} (X : LocallyRingedSpace.{u}) [Limits.HasCoproduct fun _ : G => X]

def sigmaIsoPresheafedSpace :
    (∐ fun _ : G => X).toPresheafedSpace ≅ ∐ fun _ : G => X.toPresheafedSpace :=
  SheafedSpace.forgetToPresheafedSpace.mapIso
      (preservesColimitIso LocallyRingedSpace.forgetToSheafedSpace
        (Discrete.functor fun _ : G => X)) ≪≫
    preservesColimitIso SheafedSpace.forgetToPresheafedSpace _

set_option linter.style.setOption false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem ι_comp_sigmaIsoPresheafedSpace_hom (g : G) :
    (Sigma.ι (fun _ : G => X) g).toShHom.hom ≫ (sigmaIsoPresheafedSpace X).hom =
      Sigma.ι (fun _ : G => X.toPresheafedSpace) g := by
  change SheafedSpace.forgetToPresheafedSpace.map
      (LocallyRingedSpace.forgetToSheafedSpace.map (Sigma.ι (fun _ : G => X) g)) ≫ _ = _
  rw [sigmaIsoPresheafedSpace, Iso.trans_hom, Functor.mapIso_hom, ← Functor.map_comp_assoc,
    ι_preservesColimitIso_hom, ι_preservesColimitIso_hom]
  rfl

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
theorem exists_map_sigmaIso_hom_base_obj (U : Opens (∐ fun _ : G => X).toTopCat) :
    ∃ U' : Opens (∐ fun _ : G => X.toPresheafedSpace).carrier,
      (Opens.map (sigmaIsoPresheafedSpace X).hom.base).obj U' = U :=
  ⟨(Opens.map (sigmaIsoPresheafedSpace X).inv.base).obj U, by
    rw [← Opens.map_comp_obj, ← PresheafedSpace.comp_base,
      (sigmaIsoPresheafedSpace X).hom_inv_id]
    simp⟩

theorem ι_preimage_sigmaIso (g : G)
    (U' : Opens (∐ fun _ : G => X.toPresheafedSpace).carrier) :
    (Opens.map (Sigma.ι (fun _ : G => X) g).toShHom.hom.base).obj
        ((Opens.map (sigmaIsoPresheafedSpace X).hom.base).obj U') =
      (Opens.map (Sigma.ι (fun _ : G => X.toPresheafedSpace) g).base).obj U' := by
  rw [← Opens.map_comp_obj, ← PresheafedSpace.comp_base, ι_comp_sigmaIsoPresheafedSpace_hom]

set_option linter.style.setOption false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem sigma_section_ext (U : Opens (∐ fun _ : G => X).toTopCat)
    (s t : ToType ((∐ fun _ : G => X).presheaf.obj (op U)))
    (h : ∀ g : G, ((Sigma.ι (fun _ : G => X) g).toShHom.hom.c.app (op U)) s =
      ((Sigma.ι (fun _ : G => X) g).toShHom.hom.c.app (op U)) t) : s = t := by
  obtain ⟨U', rfl⟩ := exists_map_sigmaIso_hom_base_obj X U
  haveI : IsIso ((sigmaIsoPresheafedSpace X).hom.c.app (op U')) :=
    @NatIso.isIso_app_of_isIso _ _ _ _ _ _ (sigmaIsoPresheafedSpace X).hom.c
      (PresheafedSpace.c_isIso_of_iso (sigmaIsoPresheafedSpace X).hom) (op U')
  have hbij : Function.Bijective ((sigmaIsoPresheafedSpace X).hom.c.app (op U')) :=
    ConcreteCategory.bijective_of_isIso _
  obtain ⟨s₀, rfl⟩ := hbij.2 s
  obtain ⟨t₀, rfl⟩ := hbij.2 t
  refine congrArg _ (PresheafedSpace.colimit_section_ext _ U' s₀ t₀ ?_)
  rintro ⟨g⟩
  have hcomp : ∀ x, ((Sigma.ι (fun _ : G => X.toPresheafedSpace) g).c.app (op U')) x =
      (X.presheaf.map (eqToHom (congrArg op (ι_preimage_sigmaIso X g U'))))
        (((Sigma.ι (fun _ : G => X) g).toShHom.hom.c.app
          (op ((Opens.map (sigmaIsoPresheafedSpace X).hom.base).obj U')))
            (((sigmaIsoPresheafedSpace X).hom.c.app (op U')) x)) := by
    intro x
    refine Eq.trans (ConcreteCategory.congr_hom (PresheafedSpace.congr_app
      (ι_comp_sigmaIsoPresheafedSpace_hom X g).symm (op U')) x) ?_
    refine Eq.trans (ConcreteCategory.comp_apply _ _ x) ?_
    exact congrArg _ (ConcreteCategory.comp_apply _ _ x)
  exact (hcomp s₀).trans ((congrArg _ (h g)).trans (hcomp t₀).symm)

end Sigma

section Action

variable {G : Type u} {X : LocallyRingedSpace.{u}} [Limits.HasCoproduct fun _ : G => X]
variable (W : Opens X.toTopCat)

theorem ι_comp_actionQuotientRight_toShHom (g : G) :
    (Sigma.ι (fun _ : G => X) g).toShHom.hom ≫ (actionQuotientRight G X).toShHom.hom =
      𝟙 X.toPresheafedSpace :=
  congrArg (fun m : X ⟶ X => m.toShHom.hom) (ι_actionQuotientRight (X := X) g)

theorem preimage_actionQuotientRight (g : G) :
    (Opens.map (Sigma.ι (fun _ : G => X) g).toShHom.hom.base).obj
        ((Opens.map (actionQuotientRight G X).toShHom.hom.base).obj W) = W := by
  rw [← Opens.map_comp_obj, ← PresheafedSpace.comp_base, ι_comp_actionQuotientRight_toShHom]
  simp

theorem ι_c_app_actionQuotientRight (g : G) (s : ToType (X.presheaf.obj (op W))) :
    ((Sigma.ι (fun _ : G => X) g).toShHom.hom.c.app
        (op ((Opens.map (actionQuotientRight G X).toShHom.hom.base).obj W)))
      (((actionQuotientRight G X).toShHom.hom.c.app (op W)) s) =
      (X.presheaf.map (eqToHom (congrArg op (preimage_actionQuotientRight W g).symm))) s := by
  refine Eq.trans (ConcreteCategory.comp_apply _ _ s).symm ?_
  refine Eq.trans (ConcreteCategory.congr_hom (PresheafedSpace.congr_app
    (ι_comp_actionQuotientRight_toShHom g) (op W)) s) ?_
  refine Eq.trans (ConcreteCategory.comp_apply _ _ s) ?_
  congr 1

variable [Monoid G] (a : G →* Aut X)

theorem ι_comp_actionQuotientLeft_toShHom (g : G) :
    (Sigma.ι (fun _ : G => X) g).toShHom.hom ≫ (actionQuotientLeft a).toShHom.hom =
      (a g).hom.toShHom.hom :=
  congrArg (fun m : X ⟶ X => m.toShHom.hom) (ι_actionQuotientLeft a g)

theorem preimage_actionQuotientLeft (g : G) :
    (Opens.map (Sigma.ι (fun _ : G => X) g).toShHom.hom.base).obj
        ((Opens.map (actionQuotientLeft a).toShHom.hom.base).obj W) =
      (Opens.map (a g).hom.toShHom.hom.base).obj W := by
  rw [← Opens.map_comp_obj, ← PresheafedSpace.comp_base, ι_comp_actionQuotientLeft_toShHom]

theorem ι_c_app_actionQuotientLeft (g : G) (s : ToType (X.presheaf.obj (op W))) :
    ((Sigma.ι (fun _ : G => X) g).toShHom.hom.c.app
        (op ((Opens.map (actionQuotientLeft a).toShHom.hom.base).obj W)))
      (((actionQuotientLeft a).toShHom.hom.c.app (op W)) s) =
      (X.presheaf.map (eqToHom (congrArg op (preimage_actionQuotientLeft W a g).symm)))
        (((a g).hom.toShHom.hom.c.app (op W)) s) := by
  refine Eq.trans (ConcreteCategory.comp_apply _ _ s).symm ?_
  refine Eq.trans (ConcreteCategory.congr_hom (PresheafedSpace.congr_app
    (ι_comp_actionQuotientLeft_toShHom a g) (op W)) s) ?_
  exact ConcreteCategory.comp_apply _ _ s

/-- The open a coequalised section lives on is stable under the action. -/
theorem eq_preimage_of_preimage_actionQuotient_eq
    (h : (Opens.map (actionQuotientRight G X).toShHom.hom.base).obj W =
      (Opens.map (actionQuotientLeft a).toShHom.hom.base).obj W) (g : G) :
    W = (Opens.map (a g).hom.toShHom.hom.base).obj W :=
  (preimage_actionQuotientRight W g).symm.trans
    ((congrArg (Opens.map (Sigma.ι (fun _ : G => X) g).toShHom.hom.base).obj h).trans
      (preimage_actionQuotientLeft W a g))

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
theorem c_app_actionQuotientLeft_eq_iff
    (h : (Opens.map (actionQuotientRight G X).toShHom.hom.base).obj W =
      (Opens.map (actionQuotientLeft a).toShHom.hom.base).obj W)
    (s : ToType (X.presheaf.obj (op W))) :
    ((actionQuotientLeft a).toShHom.hom.c.app (op W)) s =
        ((∐ fun _ : G => X).presheaf.map (eqToHom (congrArg op h)))
          (((actionQuotientRight G X).toShHom.hom.c.app (op W)) s) ↔
      ∀ g : G, ((a g).hom.toShHom.hom.c.app (op W)) s =
        (X.presheaf.map (eqToHom (congrArg op
          (eq_preimage_of_preimage_actionQuotient_eq W a h g)))) s := by
  have key : ∀ g : G,
      (((Sigma.ι (fun _ : G => X) g).toShHom.hom.c.app
          (op ((Opens.map (actionQuotientLeft a).toShHom.hom.base).obj W)))
            (((actionQuotientLeft a).toShHom.hom.c.app (op W)) s) =
        ((Sigma.ι (fun _ : G => X) g).toShHom.hom.c.app
          (op ((Opens.map (actionQuotientLeft a).toShHom.hom.base).obj W)))
            (((∐ fun _ : G => X).presheaf.map (eqToHom (congrArg op h)))
              (((actionQuotientRight G X).toShHom.hom.c.app (op W)) s))) ↔
      (((a g).hom.toShHom.hom.c.app (op W)) s =
        (X.presheaf.map (eqToHom (congrArg op
          (eq_preimage_of_preimage_actionQuotient_eq W a h g)))) s) := by
    intro g
    rw [ι_c_app_actionQuotientLeft, PresheafedSpace.c_app_map_eqToHom _ h,
      ι_c_app_actionQuotientRight, PresheafedSpace.map_eqToHom_trans_apply X.presheaf
        (preimage_actionQuotientRight W g).symm
        (congrArg (Opens.map (Sigma.ι (fun _ : G => X) g).toShHom.hom.base).obj h)]
    exact PresheafedSpace.map_eqToHom_eq_iff X.presheaf
      (preimage_actionQuotientLeft W a g).symm
      ((preimage_actionQuotientRight W g).symm.trans
        (congrArg (Opens.map (Sigma.ι (fun _ : G => X) g).toShHom.hom.base).obj h)) _ _
  constructor
  · exact fun heq g => (key g).mp (congrArg _ heq)
  · exact fun hinv => sigma_section_ext X _ _ _ fun g => (key g).mpr (hinv g)

theorem c_app_eq_of_eq_id {φ : X ⟶ X} (hφ : φ = 𝟙 X)
    (hW : W = (Opens.map φ.toShHom.hom.base).obj W) (s : ToType (X.presheaf.obj (op W))) :
    (φ.toShHom.hom.c.app (op W)) s = (X.presheaf.map (eqToHom (congrArg op hW))) s := by
  subst hφ
  exact ConcreteCategory.congr_hom (PresheafedSpace.id_c_app _ (op W)) s

end Action

end AlgebraicGeometry.LocallyRingedSpace

namespace CategoryTheory

open AlgebraicGeometry

variable {G : Type u} [Monoid G] {X : LocallyRingedSpace.{u}} (a : G →* Aut X)
variable [Limits.HasCoproduct fun _ : G => X]
  [Limits.HasCoequalizer (actionQuotientLeft a) (actionQuotientRight G X)]

theorem preimage_actionQuotientπ_eq (V : Opens (actionQuotient a).toTopCat) (g : G) :
    (Opens.map (actionQuotientπ a).toShHom.hom.base).obj V =
      (Opens.map (a g).hom.toShHom.hom.base).obj
        ((Opens.map (actionQuotientπ a).toShHom.hom.base).obj V) :=
  LocallyRingedSpace.eq_preimage_of_preimage_actionQuotient_eq _ a
    (LocallyRingedSpace.preimage_coequalizer_π_eq _ _ V) g

theorem exists_actionQuotientπ_c_app_eq_iff_forall (V : Opens (actionQuotient a).toTopCat)
    (s : ToType (X.presheaf.obj (op ((Opens.map (actionQuotientπ a).toShHom.hom.base).obj V)))) :
    (∃ t, ((actionQuotientπ a).toShHom.hom.c.app (op V)) t = s) ↔
      ∀ g : G, ((a g).hom.toShHom.hom.c.app
          (op ((Opens.map (actionQuotientπ a).toShHom.hom.base).obj V))) s =
        (X.presheaf.map (eqToHom (congrArg op (preimage_actionQuotientπ_eq a V g)))) s :=
  (LocallyRingedSpace.exists_c_app_eq_iff_c_app_eq _ _ V
      (LocallyRingedSpace.preimage_coequalizer_π_eq _ _ V) s).trans
    (LocallyRingedSpace.c_app_actionQuotientLeft_eq_iff _ a
      (LocallyRingedSpace.preimage_coequalizer_π_eq _ _ V) s)

theorem bijective_actionQuotientπ_c_app_one
    [Limits.HasCoequalizer (actionQuotientLeft (1 : G →* Aut X)) (actionQuotientRight G X)]
    (V : Opens (actionQuotient (1 : G →* Aut X)).toTopCat) :
    Function.Bijective ((actionQuotientπ (1 : G →* Aut X)).toShHom.hom.c.app (op V)) :=
  ⟨LocallyRingedSpace.injective_coequalizer_π_c_app _ _ V, fun s =>
    (exists_actionQuotientπ_c_app_eq_iff_forall _ V s).mpr fun g =>
      LocallyRingedSpace.c_app_eq_of_eq_id (φ := ((1 : G →* Aut X) g).hom) _ rfl
        (preimage_actionQuotientπ_eq (1 : G →* Aut X) V g) s⟩

end CategoryTheory
