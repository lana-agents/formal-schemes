import FormalSchemes.ActionQuotientRestrict
import FormalSchemes.ActionQuotientSectionInjective

set_option linter.style.header false

/-!
# The sections of an action quotient, for any presentation and across a restriction

`CategoryTheory.exists_actionQuotientπ_c_app_eq_iff_forall`
(`FormalSchemes.ActionQuotientInvariantSections`) describes the sections of an action quotient — a
section of `X` over `π⁻¹ V` is the pullback of a section of `X / G` over `V` **iff** it is
invariant — but only for `CategoryTheory.actionQuotientπ`, the coequalizer projection itself.
`CategoryTheory.IsActionQuotient.injective_c_app` (`FormalSchemes.ActionQuotientSectionInjective`)
already carries the uniqueness half to an arbitrary presentation `π : X ⟶ Q`. This file carries
the existence half, and then carries both across a restriction to an open of the quotient.

The second half is the statement `FormalSchemes.ActionQuotientRestrict` names as the expectation
it does not discharge: *"restricting to `V` does not change sections over sub-opens of `V`, which
is why those two are expected to transfer"*. They do, and the transfer is here.

## Main results

* `CategoryTheory.IsActionQuotient.exists_c_app_eq_iff_forall`: **a section of `X` over `π⁻¹ V`
  descends along any quotient projection exactly when it is invariant.** The coequalizer case
  transported along `CategoryTheory.IsActionQuotient.isoActionQuotient`.
* `AlgebraicGeometry.LocallyRingedSpace.restrictOpensHom_c_app`: **the workhorse.** The comparison
  map of a restricted morphism is the comparison map of the morphism, conjugated by the two
  inclusions of opens.
* `AlgebraicGeometry.LocallyRingedSpace.isIso_ofRestrict_c_app`: those two inclusions are
  isomorphisms on sections, over opens small enough to be seen inside the restriction.
* `AlgebraicGeometry.LocallyRingedSpace.injective_c_app_restrictπ` and
  `AlgebraicGeometry.LocallyRingedSpace.exists_c_app_restrictπ_eq_iff_forall`: **the payoff.** For
  an open `W ≤ V` of the quotient, the sections of `Q|_V` over `W` are exactly the invariant
  sections of `X` over `π⁻¹ W`, and a section determines at most one of them.
* `AlgebraicGeometry.LocallyRingedSpace.existsUnique_c_app_restrictπ_eq_iff_forall`: the two
  halves in one statement.

## What is *not* proved here

**`CategoryTheory.IsActionQuotient` for the restricted projection at
`AlgebraicGeometry.LocallyRingedSpace` level**, which is what row 1618 asks for and what
`FormalSchemes.ActionQuotientRestrict` leaves open. That file proves the statement after
`AlgebraicGeometry.LocallyRingedSpace.forgetToTop`; this one proves the section-level description
the sheaf half was expected to need. Neither of them builds the morphism of locally ringed spaces,
and this file does not shorten that construction by itself.

The route the two files together suggest — and it is a **route, not a theorem, and nothing here
tests it** — is to compare `Q|_V` with the coequalizer `X|_{π⁻¹ V} / G` of the restricted action
(`AlgebraicGeometry.LocallyRingedSpace.restrictAction`) rather than to build a descent by hand: the
comparison morphism exists by the universal property of that coequalizer, its base map is a
continuous bijection by `AlgebraicGeometry.LocallyRingedSpace.base_isQuotientMap_restrictπ` and
`AlgebraicGeometry.LocallyRingedSpace.base_eq_iff_restrictπ`, and the statements here are what a
proof that it is an isomorphism on sections would consume. What is **missing** for that route, and
is not attempted here, is the translation between invariance under
`AlgebraicGeometry.LocallyRingedSpace.restrictAction` and invariance under `a` — every statement
below is phrased in terms of sections of `X` and invariance under `a`, so none of them needs it,
and a proof that compares with the restricted coequalizer would.

## Implementation notes

Every comparison map here is read through
`AlgebraicGeometry.LocallyRingedSpace.restrictOpensHom_c_app`, which is
`AlgebraicGeometry.LocallyRingedSpace.restrictOpensHom_comp_ofRestrict` — the defining property of
the restricted morphism — applied at `c`. The two maps flanking it are isomorphisms only because
the opens are small: `AlgebraicGeometry.LocallyRingedSpace.isIso_ofRestrict_c_app` needs `W ≤ V`,
and on the source side `π⁻¹ W ≤ π⁻¹ V` is what makes the same true there. That is the whole reason
the statements below carry `W ≤ V` rather than an arbitrary open of `Q`.

`G` is only a `Monoid` except where `CategoryTheory.IsActionQuotient.injective_c_app` is used,
which is stated for a group; the statements that combine both halves inherit that.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
* [The Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ).
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

/-- The two ways of pulling an open of `Y` back to `X|_U` — around the two sides of the square that
defines `AlgebraicGeometry.LocallyRingedSpace.restrictOpensHom` — give the same open. -/
theorem preimage_restrictOpensHom_eq (f : X ⟶ Y) (U : Opens X.toTopCat) (V : Opens Y.toTopCat)
    (hfUV : f.base '' (U : Set X.toTopCat) ⊆ (V : Set Y.toTopCat)) (W : Opens Y.toTopCat) :
    (Opens.map (X.ofRestrict U.isOpenEmbedding).base).obj ((Opens.map f.base).obj W) =
      (Opens.map (restrictOpensHom f U V hfUV).base).obj
        ((Opens.map (Y.ofRestrict V.isOpenEmbedding).base).obj W) :=
  congrArg (fun m : X.restrict U.isOpenEmbedding ⟶ Y => (Opens.map m.base).obj W)
    (restrictOpensHom_comp_ofRestrict f U V hfUV).symm

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
/-- **A restricted morphism on sections is the original one, conjugated by the two inclusions.**
This is `AlgebraicGeometry.LocallyRingedSpace.restrictOpensHom_comp_ofRestrict` read at `c`, and it
is the only property of the restricted morphism's comparison maps that anything below uses. The
two flanking maps are isomorphisms when the opens are small enough
(`AlgebraicGeometry.LocallyRingedSpace.isIso_ofRestrict_c_app`), which is what turns this square
into a description of the restricted comparison map rather than a mere compatibility. -/
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
any morphism exhibiting the quotient rather than for the coequalizer projection alone.

`CategoryTheory.exists_actionQuotientπ_c_app_eq_iff_forall` is the case
`π = CategoryTheory.actionQuotientπ a`, and
`CategoryTheory.IsActionQuotient.isoActionQuotient` identifies the two presentations. The transport
is `AlgebraicGeometry.PresheafedSpace.exists_c_app_eq_iff_of_iso`, which is phrased at the
transported open precisely so that the section has the same type on both sides; substituting the
defining property of the identification along `π` puts the goal in that shape, and no rewriting
inside the type of the section is needed.

The invariance condition is stated with
`AlgebraicGeometry.LocallyRingedSpace.isInvariantOpen_preimage`, which says `π⁻¹ V` is invariant
using nothing but invariance of `π`; the corresponding equality of opens for the coequalizer is
`CategoryTheory.preimage_actionQuotientπ_eq`, and the two `eqToHom`s are equal by proof
irrelevance. -/
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

namespace AlgebraicGeometry.LocallyRingedSpace

section Monoid

variable {G : Type v} [Monoid G] [Small.{u} G]
variable {X Q : LocallyRingedSpace.{u}} {a : G →* Aut X} {π : X ⟶ Q}

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
/-- **The sections of `Q|_V` over `W` are the invariant sections of `X` over `π⁻¹ W`.** For an open
`W ≤ V` of the quotient and a section `s` of `X` over `π⁻¹ W`, the transport of `s` to
`X|_{π⁻¹ V}` is the pullback of a section of `Q|_V` over `W` exactly when `s` is invariant — the
same condition, on the same section, as before the restriction.

Both statements are read off
`AlgebraicGeometry.LocallyRingedSpace.restrictOpensHom_c_app` at `W`: its two flanking maps are
isomorphisms because `W ≤ V` and hence `π⁻¹ W ≤ π⁻¹ V`, so the restricted comparison map has the
same image as the unrestricted one, and
`CategoryTheory.IsActionQuotient.exists_c_app_eq_iff_forall` describes that image.

The section is a section of `X`, not of `X|_{π⁻¹ V}`, and the invariance is invariance under `a`,
not under `AlgebraicGeometry.LocallyRingedSpace.restrictAction`. That is deliberate: the transport
between the two notions of invariance is not proved anywhere, and phrasing the statement on `X`
avoids needing it. -/
theorem exists_c_app_restrictπ_eq_iff_forall (h : IsActionQuotient a π) (V W : Opens Q.toTopCat)
    (hW : W ≤ V) (s : ToType (X.presheaf.obj (op ((Opens.map π.base).obj W)))) :
    (∃ t, ((restrictπ π V).c.app
        (op ((Opens.map (Q.ofRestrict V.isOpenEmbedding).base).obj W))) t =
      ((X.restrict ((Opens.map π.base).obj V).isOpenEmbedding).presheaf.map
          (eqToHom (congrArg op (preimage_restrictOpensHom_eq π ((Opens.map π.base).obj V) V
            (by rintro _ ⟨x, hx, rfl⟩; exact hx) W))))
        (((X.ofRestrict ((Opens.map π.base).obj V).isOpenEmbedding).c.app
          (op ((Opens.map π.base).obj W))) s)) ↔
      ∀ g : G, ((a g).hom.c.app (op ((Opens.map π.base).obj W))) s =
        (X.presheaf.map (eqToHom (congrArg op
          (isInvariantOpen_preimage h.isInvariant W g).symm))) s := by
  haveI h1 : IsIso ((Q.ofRestrict V.isOpenEmbedding).c.app (op W)) :=
    isIso_ofRestrict_c_app Q V W hW
  haveI h2 : IsIso ((X.ofRestrict ((Opens.map π.base).obj V).isOpenEmbedding).c.app
      (op ((Opens.map π.base).obj W))) :=
    isIso_ofRestrict_c_app X _ _ (fun x hx => hW hx)
  have hsq := restrictOpensHom_c_app π ((Opens.map π.base).obj V) V
    (by rintro _ ⟨x, hx, rfl⟩; exact hx) W
  have hsurj : Function.Surjective ((Q.ofRestrict V.isOpenEmbedding).c.app (op W)) :=
    (ConcreteCategory.bijective_of_isIso _).2
  refine Iff.trans ?_ (h.exists_c_app_eq_iff_forall W s)
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨t', rfl⟩ := hsurj t
    refine ⟨t', ?_⟩
    have hsq' := ConcreteCategory.congr_hom hsq t'
    simp only [ConcreteCategory.comp_apply] at hsq'
    exact (ConcreteCategory.bijective_of_isIso _).1
      ((ConcreteCategory.bijective_of_isIso _).1 (hsq'.symm.trans ht))
  · rintro ⟨t', rfl⟩
    refine ⟨((Q.ofRestrict V.isOpenEmbedding).c.app (op W)) t', ?_⟩
    have hsq' := ConcreteCategory.congr_hom hsq t'
    simp only [ConcreteCategory.comp_apply] at hsq'
    exact hsq'

end Monoid

section Group

variable {G : Type v} [Group G] [Small.{u} G]
variable {X Q : LocallyRingedSpace.{u}} {a : G →* Aut X} {π : X ⟶ Q}

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
/-- **A section of `Q|_V` is determined by its pullback to `X|_{π⁻¹ V}`.**
`CategoryTheory.IsActionQuotient.injective_c_app` conjugated by the same two inclusions as
`AlgebraicGeometry.LocallyRingedSpace.exists_c_app_restrictπ_eq_iff_forall`: the map on the left of
the square is surjective, so injectivity of the composite is injectivity of the restricted
comparison map. -/
theorem injective_c_app_restrictπ (h : IsActionQuotient a π) (V W : Opens Q.toTopCat)
    (hW : W ≤ V) :
    Function.Injective ((restrictπ π V).c.app
      (op ((Opens.map (Q.ofRestrict V.isOpenEmbedding).base).obj W))) := by
  haveI h1 : IsIso ((Q.ofRestrict V.isOpenEmbedding).c.app (op W)) :=
    isIso_ofRestrict_c_app Q V W hW
  haveI h2 : IsIso ((X.ofRestrict ((Opens.map π.base).obj V).isOpenEmbedding).c.app
      (op ((Opens.map π.base).obj W))) :=
    isIso_ofRestrict_c_app X _ _ (fun x hx => hW hx)
  have hsq := restrictOpensHom_c_app π ((Opens.map π.base).obj V) V
    (by rintro _ ⟨x, hx, rfl⟩; exact hx) W
  have hsurj : Function.Surjective ((Q.ofRestrict V.isOpenEmbedding).c.app (op W)) :=
    (ConcreteCategory.bijective_of_isIso _).2
  intro x y hxy
  obtain ⟨x', rfl⟩ := hsurj x
  obtain ⟨y', rfl⟩ := hsurj y
  refine congrArg _ (h.injective_c_app W ?_)
  have hx := ConcreteCategory.congr_hom hsq x'
  have hy := ConcreteCategory.congr_hom hsq y'
  simp only [ConcreteCategory.comp_apply] at hx hy
  have hkey := hx.symm.trans (hxy.trans hy)
  exact (ConcreteCategory.bijective_of_isIso _).1 ((ConcreteCategory.bijective_of_isIso _).1 hkey)

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
/-- **The two halves together.** Over an open `W ≤ V` of the quotient, an invariant section of `X`
over `π⁻¹ W` is the pullback of exactly one section of `Q|_V` over `W`, and only invariant sections
are pullbacks. This is the form a descent along the restricted projection consumes. -/
theorem existsUnique_c_app_restrictπ_eq_iff_forall (h : IsActionQuotient a π)
    (V W : Opens Q.toTopCat) (hW : W ≤ V)
    (s : ToType (X.presheaf.obj (op ((Opens.map π.base).obj W)))) :
    (∃! t, ((restrictπ π V).c.app
        (op ((Opens.map (Q.ofRestrict V.isOpenEmbedding).base).obj W))) t =
      ((X.restrict ((Opens.map π.base).obj V).isOpenEmbedding).presheaf.map
          (eqToHom (congrArg op (preimage_restrictOpensHom_eq π ((Opens.map π.base).obj V) V
            (by rintro _ ⟨x, hx, rfl⟩; exact hx) W))))
        (((X.ofRestrict ((Opens.map π.base).obj V).isOpenEmbedding).c.app
          (op ((Opens.map π.base).obj W))) s)) ↔
      ∀ g : G, ((a g).hom.c.app (op ((Opens.map π.base).obj W))) s =
        (X.presheaf.map (eqToHom (congrArg op
          (isInvariantOpen_preimage h.isInvariant W g).symm))) s := by
  refine Iff.trans ?_ (exists_c_app_restrictπ_eq_iff_forall h V W hW s)
  constructor
  · rintro ⟨t, ht, -⟩
    exact ⟨t, ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, ht, fun y hy => injective_c_app_restrictπ h V W hW (hy.trans ht.symm)⟩

end Group

end AlgebraicGeometry.LocallyRingedSpace
