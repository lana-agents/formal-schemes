import FormalSchemes.ActionInvariantExtension

set_option linter.style.header false

/-!
# Transporting an injectivity-and-invariant-image statement along an equality of opens

`AlgebraicGeometry.LocallyRingedSpace.injective_and_exists_congr` moves the pair of conditions

> `f` is injective, and every invariant section over `U` is a value of `f`

for a ring homomorphism `f : A →+* Γ(X, U)` across an equality of opens `U = V`, by composing `f`
with the presheaf's `eqToHom` and retyping the invariant sections.

## Why this file exists, and why it is this low

The two conditions are the shape hypothesis 4 of
`AlgebraicGeometry.exists_formalScheme_of_adicSections` takes after
`FormalSchemes.TateInvNodeChartDescentBasicOpen` is applied, and the open they are read over is a
preimage that `FormalSchemes.TateInvNodeChartBasicOpenPreimage` rewrites. The transport is **not**
free: the two opens there are equal by `TopologicalSpace.Opens.ext` of a set-level argument, not by
`rfl`, so a substitution has to be made rather than a `rfl`-substitution taken. Once the equality
is a hypothesis binder, `subst` reduces `eqToHom` to the identity and `simp` closes it — but that
is a lemma, and this is where it lives.

Nothing in it is about formal schemes, group actions of any particular group, or the Tate curve:
the only project declaration it names is
`AlgebraicGeometry.LocallyRingedSpace.IsInvariantSection`, which is declared in
`FormalSchemes/ActionInvariantExtension.lean` (forward closure 78, reverse closure 65). This leaf
over it has forward closure **79**, and reverse closure **5**, all five of them in the Tate
node-chart cluster; the alternative, adding it to
`FormalSchemes/ActionInvariantExtension.lean`, re-elaborates 65 modules for a two-line proof.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.injective_and_exists_congr`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
-/

noncomputable section

universe u v w

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.LocallyRingedSpace

variable {G : Type v} [Group G] {X : LocallyRingedSpace.{u}} (a : G →* Aut X)

/-- **Injectivity together with "the image is the invariant sections" transports along an equality
of opens.** For `h : U = V` the presheaf's `eqToHom` is an isomorphism, so composing with it
changes neither the injectivity of `f : A →+* Γ(X, U)` nor which sections are hit; and
`AlgebraicGeometry.LocallyRingedSpace.IsInvariantSection` takes its open from the type of the
section, so the invariance condition follows the retyping.

The proof is `subst h` — after which `eqToHom` is the identity and the two statements are the same
one — so the content is that the substitution is legitimate, not that anything is computed. -/
theorem injective_and_exists_congr {A : Type w} [CommRing A]
    {U V : Opens X.toTopCat} (h : U = V) (f : A →+* X.presheaf.obj (op U)) :
    (Function.Injective ((X.presheaf.map (eqToHom (congrArg op h))).hom.comp f) ∧
        ∀ t, IsInvariantSection a t →
          ∃ r, (X.presheaf.map (eqToHom (congrArg op h))).hom.comp f r = t) ↔
      (Function.Injective f ∧ ∀ t, IsInvariantSection a t → ∃ r, f r = t) := by
  subst h
  simp

end AlgebraicGeometry.LocallyRingedSpace

end
