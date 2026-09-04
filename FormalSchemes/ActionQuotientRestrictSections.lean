import FormalSchemes.ActionQuotientRestrict
import FormalSchemes.ActionQuotientSectionInjective

set_option linter.style.header false

/-!
# The sections of a quotient, for any presentation, and across a restriction

placeholder
-/

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open AlgebraicGeometry.LocallyRingedSpace

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X Y : LocallyRingedSpace.{u}}

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
/-- **Sections over an open contained in `V` do not change when the space is restricted to `V`.**
`AlgebraicGeometry.PresheafedSpace.IsOpenImmersion.c_iso'` at the open `W`, which is the image of
its own preimage exactly because `W ≤ V`. -/
theorem isIso_ofRestrict_c_app (Y : LocallyRingedSpace.{u}) (V W : Opens Y.toTopCat)
    (h : W ≤ V) :
    IsIso ((Y.ofRestrict V.isOpenEmbedding).c.app (op W)) := by
  refine PresheafedSpace.IsOpenImmersion.c_iso' _ ((Opens.map V.inclusion').obj W) ?_
  ext x
  constructor
  · intro hx
    exact ⟨⟨x, h hx⟩, hx, rfl⟩
  · rintro ⟨⟨y, hy⟩, hy', rfl⟩
    exact hy'

/-- The two ways of pulling an open of `Y` back to `X|_U` — around the two sides of the square
defining `AlgebraicGeometry.LocallyRingedSpace.restrictOpensHom` — give the same open. -/
theorem preimage_restrictOpensHom_eq (f : X ⟶ Y) (U : Opens X.toTopCat) (V : Opens Y.toTopCat)
    (hfUV : f.base '' (U : Set X.toTopCat) ⊆ (V : Set Y.toTopCat)) (W : Opens Y.toTopCat) :
    (Opens.map (X.ofRestrict U.isOpenEmbedding).base).obj ((Opens.map f.base).obj W) =
      (Opens.map (restrictOpensHom f U V hfUV).base).obj
        ((Opens.map (Y.ofRestrict V.isOpenEmbedding).base).obj W) :=
  congrArg (fun m : X.restrict U.isOpenEmbedding ⟶ Y => (Opens.map m.base).obj W)
    (restrictOpensHom_comp_ofRestrict f U V hfUV).symm

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
/-- **The restricted morphism on sections is the original one, conjugated by the two inclusions.**
This is `AlgebraicGeometry.LocallyRingedSpace.restrictOpensHom_comp_ofRestrict` read at `c`, and it
is the only property of `AlgebraicGeometry.LocallyRingedSpace.restrictOpensHom`'s comparison maps
that anything below uses. Both outer maps are isomorphisms when the opens are small enough
(`AlgebraicGeometry.LocallyRingedSpace.isIso_ofRestrict_c_app`), which is what turns this square
into a description of the restricted comparison map. -/
theorem restrictOpensHom_c_app (f : X ⟶ Y) (U : Opens X.toTopCat) (V : Opens Y.toTopCat)
    (hfUV : f.base '' (U : Set X.toTopCat) ⊆ (V : Set Y.toTopCat)) (W : Opens Y.toTopCat) :
    (Y.ofRestrict V.isOpenEmbedding).c.app (op W) ≫
        (restrictOpensHom f U V hfUV).c.app
          (op ((Opens.map (Y.ofRestrict V.isOpenEmbedding).base).obj W)) =
      f.c.app (op W) ≫ (X.ofRestrict U.isOpenEmbedding).c.app (op ((Opens.map f.base).obj W)) ≫
        (X.restrict U.isOpenEmbedding).presheaf.map
          (eqToHom (congrArg op (preimage_restrictOpensHom_eq f U V hfUV W))) := by
  have hsq : (restrictOpensHom f U V hfUV).toShHom.hom ≫
        (Y.ofRestrict V.isOpenEmbedding).toShHom.hom
      = (X.ofRestrict U.isOpenEmbedding).toShHom.hom ≫ f.toShHom.hom :=
    congrArg (fun m : X.restrict U.isOpenEmbedding ⟶ Y => m.toShHom.hom)
      (restrictOpensHom_comp_ofRestrict f U V hfUV)
  have h2 := PresheafedSpace.congr_app hsq (op W)
  rw [PresheafedSpace.comp_c_app, PresheafedSpace.comp_c_app, Category.assoc] at h2
  exact h2

end AlgebraicGeometry.LocallyRingedSpace

namespace CategoryTheory

variable {G : Type v} [Monoid G] [Small.{u} G]
variable {X Q : LocallyRingedSpace.{u}} {a : G →* Aut X} {π : X ⟶ Q}

/-- **A section of `X` over `π⁻¹ V` descends to the quotient exactly when it is invariant**, for
any morphism exhibiting the quotient. -/
theorem IsActionQuotient.exists_c_app_eq_iff_forall (h : IsActionQuotient a π)
    (V : Opens Q.toTopCat)
    (s : ToType (X.presheaf.obj (op ((Opens.map π.base).obj V)))) :
    (∃ t, (π.c.app (op V)) t = s) ↔
      ∀ g : G, ((a g).hom.c.app (op ((Opens.map π.base).obj V))) s =
        (X.presheaf.map (eqToHom (congrArg op
          (isInvariantOpen_preimage h.isInvariant V g).symm))) s := by
  obtain ⟨e, he⟩ : ∃ e : actionQuotient a ≅ Q, actionQuotientπ a ≫ e.hom = π :=
    ⟨h.isoActionQuotient.symm, h.comp_isoActionQuotient_inv⟩
  subst he
  refine Iff.trans (PresheafedSpace.exists_c_app_eq_iff_of_iso (actionQuotientπ a).toShHom.hom
    ((forgetToSheafedSpace ⋙ SheafedSpace.forgetToPresheafedSpace).mapIso e) V s) ?_
  exact exists_actionQuotientπ_c_app_eq_iff_forall a ((Opens.map e.hom.base).obj V) s

end CategoryTheory
