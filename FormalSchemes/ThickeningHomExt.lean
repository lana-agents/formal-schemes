import FormalSchemes.Thickenings
import FormalSchemes.StructureSheafSections

set_option linter.style.header false

/-!
# A morphism out of `Spf R` is determined by its restrictions to the thickenings

`FormalSchemes/IndSchemeThickening.lean` proves this for an **affine** target
(`FormalSpectrum.hom_ext_thickeningMap`), by transporting the question along `specHomEquiv` to a
statement about ring homomorphisms and finishing with Hausdorffness of the `I`-adic topology. That
route is unavailable for a target that is not the `Spec` of a ring, and a target that is not the
`Spec` of a ring is exactly what umbrella 59 needs: the morphisms `Spf R{1/r} ⟶ X` built in
`FormalSchemes/ThickeningChartSpfHom.lean` land in an arbitrary locally ringed space, and comparing
two of them is the first step of the gluing.

This file proves the statement for an arbitrary target, and the proof is shorter than the affine
one because it uses the *definitions* rather than the theory:

* `structureSheaf I` **is** `limit (structureSheafFunctor I)` (`StructureSheaf.lean`), and
  `sectionsLimitIso` (`StructureSheafSections.lean`) turns that into a limit description of the
  sections over any fixed open;
* the sheaf component of `thickeningMap I n` **is** `limit.π (structureSheafFunctor I) ⟨n⟩`
  (`Thickenings.lean`), definitionally.

So "the thickenings are jointly epi" is `limit.hom_ext` on sections, and the only real work is
getting the two morphisms into a form where their sheaf components can be compared at all.

## The `subst` trick, which is what makes this short

A morphism of locally ringed spaces is a base map together with a sheaf map *whose type mentions
the base map*. The two morphisms here have equal base maps, but only propositionally, so their
sheaf components live in types that are equal rather than identical, and `PresheafedSpace.ext`
consequently states the goal as `g₁.c ≫ whiskerRight (eqToHom _) _ = g₂.c` — an `eqToHom` that
then has to be pushed through every subsequent step and reconciled with the *other* `eqToHom` that
`PresheafedSpace.congr_app` produces on the `Spec` side.

None of that is necessary. **Destructuring both morphisms into `⟨⟨base, c⟩, prop⟩` first turns the
base equality into an equation between two local variables, so `subst` applies**, after which
every transport is `eqToHom rfl` and the goal is literally `c₁ = c₂`.

The base equality itself is free: `(thickeningMap I n).base` is `(thickeningTopIso I n).inv`, an
isomorphism of topological spaces, so level `0` of the tower already determines it by `cancel_epi`.

## Main results

* `FormalSpectrum.hom_ext_thickeningMap_lrs`: **the general statement.** Two morphisms
  `Spf R ⟶ X`, for `X` an arbitrary locally ringed space, that agree after restriction to every
  infinitesimal thickening are equal. The `_lrs` suffix follows the tree's convention of marking
  the locally-ringed-space layer (`chartIsoLRS`, `chartStepLRS_comp_chartIsoLRS`); the unprimed
  `hom_ext_thickeningMap` keeps its affine-target statement and is not touched, though the
  `example` at the bottom of this file checks that it is now a special case.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6 (10.6.3, 10.6.7).
* [The Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] {I : Ideal R} [IsAdicRing I]

omit [TopologicalSpace R] [IsAdicRing I] in
set_option linter.style.setOption false in
-- The `rw [← cancel_mono …]` below rewrites under `(structureSheaf I).presheaf.obj`, whose
-- argument is spelled as an object of `TopCat.Presheaf` in one place and of the plain functor
-- category in the other. The two are `rfl` but not at `instances` transparency, which is where
-- `rw` builds its motive; without this the rewrite reports "Did not find an occurrence of the
-- pattern". Same accommodation, same reason, as `ThickeningCocone.lean`.
set_option backward.isDefEq.respectTransparency false in
/-- **A morphism out of `Spf R` into an arbitrary locally ringed space is determined by its
restrictions to the infinitesimal thickenings.** This is the uniqueness half of the description of
`Spf R` as the colimit of the `Spec (R ⧸ I ^ (n + 1))` (EGA I, 10.6.3), with no affineness
hypothesis on the target — which is what distinguishes it from `hom_ext_thickeningMap`.

The base maps agree already at level `0`, because `thickeningMap`'s base map is an isomorphism of
spaces; the sheaf maps agree because `O_{Spf R}` is a limit and `thickeningMap`'s sheaf component
is its projection. -/
theorem hom_ext_thickeningMap_lrs {X : LocallyRingedSpace.{u}}
    (g₁ g₂ : locallyRingedSpaceObj I ⟶ X)
    (h : ∀ n : ℕ, thickeningMap I n ≫ g₁ = thickeningMap I n ≫ g₂) :
    g₁ = g₂ := by
  -- The base maps agree, from level `0` alone: `thickeningMap`'s base map is an isomorphism.
  have hbase : g₁.base = g₂.base := by
    have h0 := congrArg
      (fun m : Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (0 + 1))) ⟶ X => m.base) (h 0)
    simp only [LocallyRingedSpace.comp_base, thickeningMap_base] at h0
    exact (cancel_epi ((thickeningTopIso I 0).inv)).mp h0
  -- Destructure before using `hbase`, so that it becomes an equation between local variables and
  -- `subst` fires; this is what removes every `eqToHom` from the rest of the proof.
  obtain ⟨⟨b₁, c₁⟩, p₁⟩ := g₁
  obtain ⟨⟨b₂, c₂⟩, p₂⟩ := g₂
  subst hbase
  suffices hc : c₁ = c₂ by subst hc; rfl
  refine NatTrans.ext (funext fun V => ?_)
  -- Sections of `O_{Spf R}` over an open are a limit, so two maps into them agree as soon as they
  -- agree after every projection.
  rw [← cancel_mono (sectionsLimitIso I (op ((Opens.map b₁).obj V.unop))).hom]
  refine limit.hom_ext fun j => ?_
  obtain ⟨n⟩ := j
  simp only [Category.assoc, sectionsLimitIso_hom_π]
  -- `PresheafedSpace.comp_c_app` is `rfl`, so the hypothesis is already in the required form:
  -- restricting along `thickeningMap I n` *is* postcomposing with the `n`-th projection.
  have key := PresheafedSpace.congr_app
    (congrArg (fun m : Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X =>
      m.toHom) (h n)) V
  simp only [eqToHom_refl, CategoryTheory.Functor.map_id] at key
  exact key

/-- The affine-target statement `hom_ext_thickeningMap` is a special case, checked rather than
asserted. It is left where it is: rewriting a landed module to derive it from this is a separate
deduplication, and its own proof records a different argument (Hausdorffness of the `I`-adic
topology) that is worth keeping on the tree. -/
example {B : Type u} [CommRing B]
    (g₁ g₂ : locallyRingedSpaceObj I ⟶ Spec.locallyRingedSpaceObj (CommRingCat.of B))
    (h : ∀ n : ℕ, thickeningMap I n ≫ g₁ = thickeningMap I n ≫ g₂) :
    g₁ = g₂ :=
  hom_ext_thickeningMap_lrs g₁ g₂ h

end FormalSpectrum

end
