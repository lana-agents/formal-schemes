import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory

set_option linter.style.header false

/-!
# Gluing sections over a pairwise-disjoint family of opens

Mathlib's `TopCat.Sheaf.existsUnique_gluing` asks for a *compatible* family of sections: the
restrictions of `sf i` and `sf j` to `U i ⊓ U j` must agree. When the family is **pairwise
disjoint** that hypothesis is vacuous — the two restrictions live in the sections over `⊥`, which
is a terminal object of `CommRingCat` and therefore a subsingleton — so an *arbitrary* family of
sections glues, and glues uniquely.

That is the form the quotient of a locally ringed space by a free, properly discontinuous action
needs: over a separating open `U`, the preimage of `π '' V'` is the *disjoint* union of the
translates of `V' ≤ U`, and a section of the quotient is built by prescribing one translate of a
given section on each piece with no compatibility to check.

## Main results

* `TopCat.Sheaf.subsingleton_sections_of_eq_bot`: the sections of a sheaf over an open equal to `⊥`
  form a subsingleton.
* `TopCat.Sheaf.isCompatible_of_pairwise_disjoint`: every family of sections over a pairwise
  disjoint family of opens is compatible.
* `TopCat.Sheaf.existsUnique_gluing_of_disjoint`, `existsUnique_gluing_of_disjoint'`: hence it has
  a unique gluing.
The uniqueness half — two sections over the supremum of the family agreeing on each piece are
equal — is *not* restated here: it needs no disjointness and is already
`TopCat.Sheaf.eq_of_locally_eq'`, which downstream callers use directly.
-/

universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace TopCat.Sheaf

variable {X : TopCat.{u}} (F : Sheaf CommRingCat.{u} X)

/-- **The sections over an empty open form a subsingleton.** `isTerminalOfEqEmpty` says that
component of the sheaf is terminal, and the forgetful functor of `CommRingCat` preserves terminal
objects, so its underlying type is a singleton. -/
theorem subsingleton_sections_of_eq_bot {U : Opens X} (hU : U = ⊥) :
    Subsingleton (ToType (F.1.obj (op U))) :=
  letI := Limits.Concrete.uniqueOfTerminalOfPreserves _ (F.isTerminalOfEqEmpty hU)
  inferInstance

variable {ι : Type v} (U : ι → Opens X)

/-- **A family of sections over pairwise disjoint opens is automatically compatible.** For `i = j`
the two restriction maps are literally the same morphism; for `i ≠ j` both restrictions live over
`U i ⊓ U j = ⊥`, where there is only one section. -/
theorem isCompatible_of_pairwise_disjoint (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (sf : ∀ i : ι, ToType (F.1.obj (op (U i)))) : Presheaf.IsCompatible F.1 U sf := by
  intro i j
  by_cases hij : i = j
  · subst hij; rfl
  · haveI := subsingleton_sections_of_eq_bot F (U := U i ⊓ U j) (disjoint_iff.mp (hdisj i j hij))
    exact Subsingleton.elim _ _

/-- **An arbitrary family of sections over a pairwise disjoint family of opens glues, uniquely.**
No compatibility hypothesis: `isCompatible_of_pairwise_disjoint` supplies it. -/
theorem existsUnique_gluing_of_disjoint (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (sf : ∀ i : ι, ToType (F.1.obj (op (U i)))) :
    ∃! s : ToType (F.1.obj (op (iSup U))), Presheaf.IsGluing F.1 U sf s :=
  F.existsUnique_gluing U sf (isCompatible_of_pairwise_disjoint F U hdisj sf)

/-- The same, with the ambient open and the inclusions given explicitly, which is what a caller
that already has `V = ⨆ i, U i` in some other form wants. -/
theorem existsUnique_gluing_of_disjoint' (V : Opens X) (iUV : ∀ i : ι, U i ⟶ V)
    (hcover : V ≤ iSup U) (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (sf : ∀ i : ι, ToType (F.1.obj (op (U i)))) :
    ∃! s : ToType (F.1.obj (op V)), ∀ i : ι, F.1.map (iUV i).op s = sf i :=
  F.existsUnique_gluing' U V iUV hcover sf (isCompatible_of_pairwise_disjoint F U hdisj sf)

end TopCat.Sheaf
