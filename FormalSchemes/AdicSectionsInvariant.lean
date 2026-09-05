import FormalSchemes.ActionQuotientRestrict
import FormalSchemes.AdicSectionsOverlap
import FormalSchemes.AdicSectionsRestrictOpen

set_option linter.style.header false

/-!
# Invariance of the morphism built from a `ψ`-adic neighbourhood basis

`AlgebraicGeometry.FormalScheme.homOfGlobalSectionsHomOfAdicSections`
(`FormalSchemes.AdicSectionsChart`) builds a morphism `k : X ⟶ Spf R` out of
`ψ : R →+* Γ(X, 𝒪_X)` and a witness of `AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG`.
If a monoid acts on `X`, one may ask whether `k` is invariant. This file answers that, and the
answer is that the question never reaches the charts.

## The morphism is invariant exactly when `ψ` is

`AlgebraicGeometry.FormalScheme.isActionInvariant_homOfGlobalSectionsHomOfAdicSections_iff`:

> `k` is `CategoryTheory.IsActionInvariant` under `a` **iff**
> `(a g)ᵀ ∘ ψ = ψ` for every `g`, where `(a g)ᵀ` is the action of `a g` on `Γ(X, 𝒪_X)`.

The right-hand side is `AlgebraicGeometry.FormalScheme.IsInvariantSectionsHom`, and it mentions
no chart, no `AlgebraicGeometry.FormalScheme.AffineChart` and no `Classical.choice`. That matters
because `AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.chart` **is** `Classical.choice`: a
condition on the charts `k` was built from could not be checked at any named family, whereas this
one is a condition on `ψ` and the action alone.

Both directions are cheap, and neither is a merge. Forwards, apply
`FormalSpectrum.globalSectionsHom` to `(a g).hom ≫ k = k` and use
`AlgebraicGeometry.FormalScheme.globalSectionsHom_homOfGlobalSectionsHomOfAdicSections`.
Backwards, `FormalSpectrum.hom_ext_of_globalSectionsHom` compares the two morphisms at the charts
the witness supplies; the continuity hypothesis it asks of `(a g).hom ≫ k` is the one it asks of
`k`, because — this is the observation `FormalSchemes.AdicSectionsOverlap` turns on —
`FormalSpectrum.globalSectionsMap I J (c ≫ s)` sees `s` only through
`FormalSpectrum.globalSectionsHom I _ s`
(`FormalSpectrum.globalSectionsMap_comp_eq_of_globalSectionsHom_eq`).

## Where an invariant `ψ` comes from

The other half of the file is the source of such a `ψ`. If `π : X ⟶ Q` is invariant and
`V : Opens Q`, then the section map of `π` at `V`, read on the global sections of `X|_{π⁻¹ V}`,
is invariant for the restricted action — because the morphism it is the section map *of*,
`X|_{π⁻¹ V} ⟶ X ⟶ Q`, is itself invariant
(`AlgebraicGeometry.LocallyRingedSpace.isActionInvariant_ofRestrict_comp`), and
`AlgebraicGeometry.LocallyRingedSpace.sectionsMapOfRangeSubset_comp` turns invariance of a
morphism into invariance of its section map with nothing else in between.

No quotient is used: `π` is only assumed invariant, not assumed to exhibit `Q` as the quotient.

## Main definitions and results

* `AlgebraicGeometry.FormalScheme.IsInvariantSectionsHom`: `ψ` is fixed by the action of every
  `a g` on global sections.
  `AlgebraicGeometry.FormalScheme.isInvariantSectionsHom_iff_forall_apply` is the pointwise
  reading; `AlgebraicGeometry.LocallyRingedSpace.IsInvariantSection` is the tree's element-level
  predicate of the same shape and is not used, for the reason that lemma's docstring gives.
* `FormalSpectrum.globalSectionsMap_comp_eq_of_globalSectionsHom_eq`: the continuity condition at a
  chart depends on the base morphism only through its global-sections homomorphism.
* `AlgebraicGeometry.FormalScheme.isActionInvariant_homOfGlobalSectionsHomOfAdicSections_iff`:
  **the equivalence.**
* `AlgebraicGeometry.LocallyRingedSpace.sectionsMapOfRangeSubset_comp_c_app_of_invariant`: the
  section map of an invariant morphism is invariant on global sections.
* `AlgebraicGeometry.LocallyRingedSpace.isActionInvariant_ofRestrict_comp`: an invariant morphism
  restricted to the preimage of an open is invariant for the restricted action.

## What is *not* proved here

**No witness of `AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG` is produced**, and no `ψ`
is proved invariant on any particular formal scheme. Everything below is conditional.

**Nothing here says the morphism descends.** Invariance is one of the two hypotheses of
`CategoryTheory.IsActionQuotient.desc`'s use in this cluster; that the descended morphism is an
isomorphism is a separate statement and is untouched.

**The equivalence is not an equivalence of the *existence* statements.** It compares invariance of
the morphism built from a *given* witness with invariance of `ψ`; it says nothing about a morphism
`X ⟶ Spf R` that was not built this way, for which `FormalSpectrum.hom_ext_of_globalSectionsHom`'s
continuity hypotheses are not available.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4 (10.4.6).
-/

noncomputable section

universe v u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry CategoryTheory.Limits
open FormalSpectrum

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X Q : LocallyRingedSpace.{u}}

variable {G : Type v} [Monoid G]

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
/-- **The section map of an invariant morphism is invariant on global sections.** If
`f : W ⟶ Q` is invariant under `b` and its range lies in `U`, then reading a section of `Q` over
`U` on `Γ(W, 𝒪_W)` gives a section fixed by the action.

This is `AlgebraicGeometry.LocallyRingedSpace.sectionsMapOfRangeSubset_comp` at `g := (b k).hom`,
whose left-hand side is the section map of `(b k).hom ≫ f = f`. Nothing else is used; in
particular `b` is an arbitrary monoid action and `f` need not be a quotient projection. -/
theorem sectionsMapOfRangeSubset_comp_c_app_of_invariant {W : LocallyRingedSpace.{u}}
    {b : G →* Aut W} (f : W ⟶ Q) (hf : IsActionInvariant b f) (U : Opens Q)
    (h : Set.range f.base ⊆ (U : Set Q)) (k : G) :
    sectionsMapOfRangeSubset f U h ≫ (b k).hom.c.app (op ⊤) = sectionsMapOfRangeSubset f U h := by
  have hrange : Set.range (((b k).hom ≫ f).base) ⊆ (U : Set Q) := by rw [hf k]; exact h
  rw [← sectionsMapOfRangeSubset_comp (b k).hom f U h hrange]
  congr 1
  exact hf k

variable {a : G →* Aut X} {π : X ⟶ Q}

/-- The composite `X|_{π⁻¹ V} ⟶ X ⟶ Q` lands in `V`, by the definition of the preimage. -/
theorem range_ofRestrict_comp_subset (π : X ⟶ Q) (V : Opens Q) :
    Set.range (X.ofRestrict ((Opens.map π.base).obj V).isOpenEmbedding ≫ π).base
      ⊆ (V : Set Q) := by
  rintro _ ⟨x, rfl⟩
  exact x.2

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
/-- **An invariant morphism, read on the preimage of an open, is invariant for the restricted
action.** `AlgebraicGeometry.LocallyRingedSpace.isActionInvariant_restrictπ` says the same of
`AlgebraicGeometry.LocallyRingedSpace.restrictπ`, which lands in `Q|_V`; this lands in `Q` itself,
which is the form a section map over `V` is taken of. -/
theorem isActionInvariant_ofRestrict_comp (hπ : IsActionInvariant a π) (V : Opens Q) :
    IsActionInvariant (restrictAction a _ (isInvariantOpen_preimage hπ V))
      (X.ofRestrict ((Opens.map π.base).obj V).isOpenEmbedding ≫ π) := by
  intro k
  have hfac := restrictOpensHom_comp_ofRestrict (a k).hom ((Opens.map π.base).obj V)
    ((Opens.map π.base).obj V) ((isInvariantOpen_preimage hπ V).image_hom_subset k)
  rw [restrictAction_hom, ← Category.assoc, hfac, Category.assoc, hπ k]

end AlgebraicGeometry.LocallyRingedSpace

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable {S : Type u} [CommRing S] [TopologicalSpace S] (J : Ideal S) [IsAdicRing J]

/-- **The continuity condition at a chart depends on the base morphism only through its
global-sections homomorphism.** `FormalSpectrum.globalSectionsMap_eq_globalSectionsHom` and
`FormalSpectrum.globalSectionsHom_comp` are both `rfl`, so `globalSectionsMap I J (c ≫ s)` is
`globalSectionsHom I Y s` with two fixed maps around it.

This is the step `AlgebraicGeometry.FormalScheme.pair_of_globalSectionsHom_eq`
(`FormalSchemes.AdicSectionsOverlap`) makes inline; it is stated here without an
`AlgebraicGeometry.FormalScheme.AffineChart` in it, because the use below is not at a chart of a
neighbourhood basis but at a chart of a supplied family. -/
theorem globalSectionsMap_comp_eq_of_globalSectionsHom_eq {Y : LocallyRingedSpace.{u}}
    (c : locallyRingedSpaceObj J ⟶ Y) (s t : Y ⟶ locallyRingedSpaceObj I)
    (h : globalSectionsHom I Y s = globalSectionsHom I Y t) :
    globalSectionsMap I J (c ≫ s) = globalSectionsMap I J (c ≫ t) := by
  rw [globalSectionsMap_eq_globalSectionsHom, globalSectionsMap_eq_globalSectionsHom,
    globalSectionsHom_comp, globalSectionsHom_comp, h]

end FormalSpectrum

namespace AlgebraicGeometry.FormalScheme

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable {X : FormalScheme.{u}} {G : Type v} [Monoid G]

/-- **`ψ` is invariant under the action, on global sections**: every `a g` fixes it, where an
automorphism of `X` acts on `Γ(X, 𝒪_X)` through its comparison map at `⊤`.

The target of `(a g).hom.c.app (op ⊤)` is `Γ(X, (a g)⁻¹ ⊤)`, which is `Γ(X, ⊤)` definitionally, so
the composition is stated with no transport — the same convention as
`FormalSpectrum.globalSectionsHom`. -/
def IsInvariantSectionsHom (a : G →* Aut X.toLocallyRingedSpace)
    (ψ : R →+* X.presheaf.obj (op (⊤ : Opens X))) : Prop :=
  ∀ g : G, ((a g).hom.c.app (op (⊤ : Opens X))).hom.comp ψ = ψ

variable (a : G →* Aut X.toLocallyRingedSpace)
variable (ψ : R →+* X.presheaf.obj (op (⊤ : Opens X)))

omit [TopologicalSpace R] in
/-- **What the predicate quantifies over**, written out: one equation of sections for each `g` and
each `r`, with no chart and no open other than `⊤` in it.

`AlgebraicGeometry.LocallyRingedSpace.IsInvariantSection`
(`FormalSchemes.ActionInvariantExtension`) is the tree's element-level predicate of the same
shape, but it is stated over an arbitrary open with a transport along `W = (a k)⁻¹ W` and under
`[Group G]`; at `⊤` under `[Monoid G]` neither is needed, so it is not used here. -/
theorem isInvariantSectionsHom_iff_forall_apply :
    IsInvariantSectionsHom a ψ ↔
      ∀ (g : G) (r : R), ((a g).hom.c.app (op (⊤ : Opens X))) (ψ r) = ψ r := by
  constructor
  · intro h g r
    exact congrFun (congrArg (fun φ : R →+* _ => (φ : R → _)) (h g)) r
  · intro h g
    ext r
    exact h g r

variable (hX : AdicSectionsLocallyFG I ψ) (hI : I.FG) (hov : hX.OverlapAdic ψ)

set_option linter.style.setOption false in
set_option backward.isDefEq.respectTransparency false in
/-- **The morphism a `ψ`-adic neighbourhood basis builds is invariant exactly when `ψ` is.**

Forwards is `FormalSpectrum.globalSectionsHom` applied to `(a g).hom ≫ k = k`, with
`AlgebraicGeometry.FormalScheme.globalSectionsHom_homOfGlobalSectionsHomOfAdicSections` on the
right; `FormalSpectrum.globalSectionsHom_comp` is `rfl`, so nothing else enters.

Backwards is `FormalSpectrum.hom_ext_of_globalSectionsHom` at the charts the witness supplies. Its
two continuity hypotheses are the *same* hypothesis: by
`FormalSpectrum.globalSectionsMap_comp_eq_of_globalSectionsHom_eq` the bound at a chart depends on
the base morphism only through its global-sections homomorphism, and the two homomorphisms agree
by the assumption. So the bound for `(a g).hom ≫ k` is
`AlgebraicGeometry.FormalScheme.continuous_homOfGlobalSectionsHomOfAdicSections` and no bound is
asked at a chart this file chose.

**The right-hand side names no chart.** That is the whole point: the left-hand side quantifies over
a morphism built from `AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.chart`, which is
`Classical.choice` and which nothing can name, while the right-hand side is a condition on `ψ` and
the action. -/
theorem isActionInvariant_homOfGlobalSectionsHomOfAdicSections_iff :
    IsActionInvariant a (homOfGlobalSectionsHomOfAdicSections ψ hX hI hov) ↔
      IsInvariantSectionsHom a ψ := by
  constructor
  · intro h g
    have hc := congrArg (globalSectionsHom I X.toLocallyRingedSpace) (h g)
    rw [globalSectionsHom_comp, globalSectionsHom_homOfGlobalSectionsHomOfAdicSections] at hc
    exact hc
  · intro h g
    have hgs : globalSectionsHom I X.toLocallyRingedSpace
          ((a g).hom ≫ homOfGlobalSectionsHomOfAdicSections ψ hX hI hov) =
        globalSectionsHom I X.toLocallyRingedSpace
          (homOfGlobalSectionsHomOfAdicSections ψ hX hI hov) := by
      rw [globalSectionsHom_comp, globalSectionsHom_homOfGlobalSectionsHomOfAdicSections]
      exact h g
    refine hom_ext_of_globalSectionsHom I hX.chart hX.fg_chart hI _ _ ?_
      (continuous_homOfGlobalSectionsHomOfAdicSections ψ hX hI hov) hgs
    intro x
    rw [globalSectionsMap_comp_eq_of_globalSectionsHom_eq I (hX.chart x).I _ _ _ hgs]
    exact continuous_homOfGlobalSectionsHomOfAdicSections ψ hX hI hov x

end AlgebraicGeometry.FormalScheme

end
