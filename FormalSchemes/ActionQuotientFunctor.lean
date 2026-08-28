import FormalSchemes.ActionQuotientColimit
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

set_option linter.style.header false

/-!
# The quotient by a group action is preserved by a functor that preserves its two colimits

`FormalSchemes.ActionQuotientColimit` builds the quotient `X / G` as the coequalizer of the two
legs `∐_{g : G} X ⇉ X`. This file records the consequence that makes that construction usable for
*computing* a quotient rather than only for asserting that one exists: a functor which preserves
the coproduct `∐_{g : G} X` and that coequalizer sends a quotient to a quotient.

The point is that `CategoryTheory.IsActionQuotient` is a universal property, so it transports along
no functor at all by itself; it is the coequalizer presentation that makes the transport available.
Applied to a forgetful functor this turns an abstract quotient object into a concrete one — that is
how `FormalSchemes.ActionQuotientCarrier` identifies the underlying set of the quotient of a
locally ringed space with the orbit set.

## Main definitions

* `CategoryTheory.Functor.mapAction`: the action `a : G →* Aut X` transported to
  `G →* Aut (F.obj X)` along `F`, via `CategoryTheory.Functor.mapAut`.

## Main results

* `CategoryTheory.IsActionInvariant.map`: a functor sends invariant morphisms to invariant
  morphisms. No hypothesis on `F`.
* `CategoryTheory.IsActionQuotient.isColimitCofork`: the universal property of the quotient, read
  as the colimit of the cofork on the two legs. This is the converse of
  `CategoryTheory.isActionQuotient_actionQuotientπ` and is what makes `F` visible to the transport.
* `CategoryTheory.IsActionQuotient.map`: **the transport** — if `F` preserves the coproduct
  `∐_{g : G} X` and the coequalizer of the two legs, then `F.map π` exhibits `F.obj Q` as
  `F.obj X / G` for the transported action.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
-/

noncomputable section

universe v v' u u' w

namespace CategoryTheory

open Category Limits

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable {G : Type w} [Monoid G] {X : C}

/-! ### Transporting an action along a functor -/

/-- **The action transported along a functor.** `F` sends an automorphism of `X` to an automorphism
of `F.obj X` (`CategoryTheory.Functor.mapAut`), and that assignment is a monoid homomorphism, so an
action of `G` on `X` becomes an action of the same `G` on `F.obj X`. -/
def Functor.mapAction (F : C ⥤ D) (a : G →* Aut X) : G →* Aut (F.obj X) :=
  (Functor.mapAut X F).comp a

@[simp]
theorem Functor.mapAction_hom (F : C ⥤ D) (a : G →* Aut X) (g : G) :
    (F.mapAction a g).hom = F.map (a g).hom :=
  rfl

/-- **A functor preserves invariance.** Nothing is assumed of `F`: invariance is an equation
between morphisms, and functors preserve equations. -/
theorem IsActionInvariant.map {a : G →* Aut X} {Z : C} {f : X ⟶ Z}
    (hf : IsActionInvariant a f) (F : C ⥤ D) :
    IsActionInvariant (F.mapAction a) (F.map f) := fun g => by
  rw [F.mapAction_hom, ← F.map_comp, hf g]

/-! ### The quotient as a colimit cofork -/

section Cofork

variable (a : G →* Aut X) [HasCoproduct fun _ : G => X]

/-- The cofork on the two legs determined by an invariant morphism, via
`CategoryTheory.isActionInvariant_iff`. -/
def actionCofork {Q : C} {π : X ⟶ Q} (h : IsActionInvariant a π) :
    Cofork (actionQuotientLeft a) (actionQuotientRight G X) :=
  Cofork.ofπ π ((isActionInvariant_iff a π).mp h)

/-- **An action quotient is a colimit cofork.** The converse direction of
`CategoryTheory.isActionQuotient_actionQuotientπ`: a value of `IsActionQuotient` is exactly the
statement that the projection coequalizes the two legs universally. -/
def IsActionQuotient.isColimitCofork {Q : C} {π : X ⟶ Q} (h : IsActionQuotient a π) :
    IsColimit (actionCofork a h.isInvariant) :=
  Cofork.IsColimit.mk _
    (fun s => h.desc s.π ((isActionInvariant_iff a s.π).mpr s.condition))
    (fun _ => h.fac _ _)
    (fun _ m hm => h.uniq _ _ m hm)

end Cofork

/-! ### The transport -/

section Transport

variable {a : G →* Aut X} [HasCoproduct fun _ : G => X] (F : C ⥤ D)
  [PreservesColimit (Discrete.functor fun _ : G => X) F]

omit [Monoid G] in
/-- Two morphisms out of `F.obj (∐_{g : G} X)` agreeing on every image summand are equal — the
coproduct's `Sigma.hom_ext`, available in `D` because `F` preserves this coproduct. -/
theorem map_sigma_hom_ext {Z : D} {u v : F.obj (∐ fun _ : G => X) ⟶ Z}
    (h : ∀ g : G, F.map (Sigma.ι (fun _ : G => X) g) ≫ u =
      F.map (Sigma.ι (fun _ : G => X) g) ≫ v) : u = v :=
  (isColimitOfPreserves F (coproductIsCoproduct fun _ : G => X)).hom_ext fun g => h g.as

/-- **The image of the coequalizer condition.** A morphism out of `F.obj X` invariant under the
transported action coequalizes the images of the two legs. This is `isActionInvariant_iff` on the
`D` side, except that `F.obj (∐_{g : G} X)` is only a coproduct because `F` preserves one. -/
theorem map_actionQuotientLeft_comp {Z : D} (f : F.obj X ⟶ Z)
    (hf : IsActionInvariant (F.mapAction a) f) :
    F.map (actionQuotientLeft a) ≫ f = F.map (actionQuotientRight G X) ≫ f := by
  refine map_sigma_hom_ext F fun g => ?_
  rw [← assoc, ← assoc, ← F.map_comp, ← F.map_comp, ι_actionQuotientLeft, ι_actionQuotientRight,
    F.map_id, id_comp]
  exact hf g

variable [PreservesColimit (parallelPair (actionQuotientLeft a) (actionQuotientRight G X)) F]

/-- **The image cofork is a colimit.** `isColimitCoforkMapOfIsColimit` at the cofork of
`IsActionQuotient.isColimitCofork`; named so that the three fields of `IsActionQuotient.map` can
refer to one colimit rather than to three syntactically distinct copies of it. -/
def isColimitMapActionCofork {Q : C} {π : X ⟶ Q} (h : IsActionQuotient a π) :
    IsColimit (Cofork.ofπ (F.map π)
        (by rw [← F.map_comp, ← F.map_comp, (isActionInvariant_iff a π).mp h.isInvariant]) :
      Cofork (F.map (actionQuotientLeft a)) (F.map (actionQuotientRight G X))) :=
  isColimitCoforkMapOfIsColimit F _ h.isColimitCofork

/-- **The transported quotient is a quotient.** If `F` preserves the coproduct `∐_{g : G} X` and
the coequalizer of the two legs, then `F.map π` exhibits `F.obj Q` as the quotient of `F.obj X` by
the transported action.

Both hypotheses are needed and neither is about `π`: the coequalizer one carries the universal
property across, and the coproduct one is what makes the *condition* on the `D` side equivalent to
invariance. -/
def IsActionQuotient.map {Q : C} {π : X ⟶ Q} (h : IsActionQuotient a π) :
    IsActionQuotient (F.mapAction a) (F.map π) where
  isInvariant := h.isInvariant.map F
  desc f hf :=
    (isColimitMapActionCofork F h).desc (Cofork.ofπ f (map_actionQuotientLeft_comp F f hf))
  fac _ _ := Cofork.IsColimit.π_desc (isColimitMapActionCofork F h)
  uniq f hf _ hm :=
    Cofork.IsColimit.hom_ext (isColimitMapActionCofork F h)
      (hm.trans (Cofork.IsColimit.π_desc
        (t := Cofork.ofπ f (map_actionQuotientLeft_comp F f hf))
        (isColimitMapActionCofork F h)).symm)

end Transport

end CategoryTheory
