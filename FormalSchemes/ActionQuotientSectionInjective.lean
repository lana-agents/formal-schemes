import FormalSchemes.ActionQuotientInvariantSections

set_option linter.style.header false

/-!
# A quotient projection is injective on sections, for any presentation of the quotient

`AlgebraicGeometry.LocallyRingedSpace.injective_coequalizer_π_c_app`
(`FormalSchemes.ActionQuotientSections`) says a section of a coequalizer is determined by its
pullback along the projection, and `CategoryTheory.actionQuotientπ` is a coequalizer projection on
the nose, so the statement is available there. It is **not** available for a hand-built quotient
`π : X ⟶ Q` carrying only a `CategoryTheory.IsActionQuotient` witness, and that is the form every
Tate-quotient statement on this tree is stated in.

This file supplies it. There is no new mathematics:
`CategoryTheory.IsActionQuotient.isoActionQuotient` identifies `Q` with
`CategoryTheory.actionQuotient` compatibly with the two projections, and
`AlgebraicGeometry.PresheafedSpace.injective_c_app_of_iso` transports injectivity across that
identification. What makes it worth naming is that the transport has to happen at the level of
presheafed spaces — the comparison of sections is a statement about `c`-components — so the
locally ringed space isomorphism must first be pushed through
`AlgebraicGeometry.LocallyRingedSpace.forgetToSheafedSpace ⋙
AlgebraicGeometry.SheafedSpace.forgetToPresheafedSpace`, and the open has to be rewritten as a
preimage along that isomorphism before `injective_c_app_of_iso` applies.

## Main result

* `CategoryTheory.IsActionQuotient.injective_c_app`: for `π : X ⟶ Q` exhibiting `Q` as `X / G` and
  any open `V` of `Q`, the map `Γ (Q, V) → Γ (X, π⁻¹ V)` is injective.

Together with `AlgebraicGeometry.LocallyRingedSpace.exists_c_app_eq_iff_c_app_eq` and
`CategoryTheory.exists_actionQuotientπ_c_app_eq_iff_forall` this pins `Γ (Q, V)` as *exactly* the
invariant sections over `π⁻¹ V`, for an arbitrary presentation of the quotient.

## References

* [The Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ).
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
-/

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry CategoryTheory.Limits

namespace CategoryTheory

variable {G : Type u} [Group G] {X : LocallyRingedSpace.{u}} {a : G →* Aut X}
variable [Limits.HasCoproduct fun _ : G => X]
  [Limits.HasCoequalizer (actionQuotientLeft a) (actionQuotientRight G X)]
variable {Q : LocallyRingedSpace.{u}} {π : X ⟶ Q}

/-- **A section of a quotient is determined by its pullback to the source**, for any morphism
exhibiting the quotient and any open of it.

`AlgebraicGeometry.LocallyRingedSpace.injective_coequalizer_π_c_app` is the special case
`π = CategoryTheory.actionQuotientπ a`; this transports it along
`CategoryTheory.IsActionQuotient.isoActionQuotient`, whose defining property
`comp_isoActionQuotient_hom` says exactly that the identification carries `π` to that projection.

The open `V` has to be presented as a preimage before
`AlgebraicGeometry.PresheafedSpace.injective_c_app_of_iso` applies, which is what the `hV` step
does; it is `V = e⁻¹ (e⁻¹ᵢₙᵥ V)` and nothing more. -/
theorem IsActionQuotient.injective_c_app (h : IsActionQuotient a π) (V : Opens Q) :
    Function.Injective (π.toShHom.hom.c.app (op V)) := by
  set e := (LocallyRingedSpace.forgetToSheafedSpace ⋙
    SheafedSpace.forgetToPresheafedSpace).mapIso h.isoActionQuotient with he
  have hcomp : π.toShHom.hom ≫ e.hom = (actionQuotientπ a).toShHom.hom := by
    rw [he]
    exact congrArg (fun φ : X ⟶ actionQuotient a => φ.toShHom.hom)
      h.comp_isoActionQuotient_hom
  have hV : V = (Opens.map e.hom.base).obj ((Opens.map e.inv.base).obj V) := by
    ext x
    change x ∈ V ↔ e.inv.base (e.hom.base x) ∈ V
    rw [show e.inv.base (e.hom.base x) = x from
      congrFun (congrArg (fun φ => ⇑(ConcreteCategory.hom (PresheafedSpace.Hom.base φ)))
        e.hom_inv_id) x]
    exact Iff.rfl
  have key : Function.Injective
      ((actionQuotientπ a).toShHom.hom.c.app (op ((Opens.map e.inv.base).obj V))) :=
    LocallyRingedSpace.injective_coequalizer_π_c_app _ _ _
  rw [hV]
  exact PresheafedSpace.injective_c_app_of_iso _ e _ (hcomp ▸ key)

end CategoryTheory
