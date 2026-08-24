import FormalSchemes.IndSchemeColimitEquiv
import FormalSchemes.IndSchemeLimitComponents

set_option linter.style.header false

/-!
# The two presentations of the colimit property agree (EGA I, 10.6.7)

After `FormalSchemes/IndSchemeColimitEquiv.lean` the tree carries **two** bijections out of
`Spf R ⟶ Spec B`, built independently, whose right-hand sides are the same mathematical object in
two different presentations:

* `specHomLimitEquiv I B` (`IndSchemeLimit.lean`) lands in `lim_n (B →+* R ⧸ Iⁿ)`, an honest
  `CategoryTheory.limit`;
* `thickeningRestrictionEquiv I B` (`IndSchemeColimitEquiv.lean`) lands in `ThickeningFamily I B`,
  a subtype of families of morphisms of locally ringed spaces.

Both are equivalences with `Spf R ⟶ Spec B`, so they are abstractly equivalent to each other — but
that goes through a third object and says nothing about *components*, which is what a consumer
holds. This file supplies the identification and its component rule.

## What has to be crossed

Two things, and both are where a mistake would hide.

**The indexing shift.** `specHomLimitEquiv`'s cone is indexed by `n` with components landing in
`R ⧸ Iⁿ`, starting at `R ⧸ I⁰`; `ThickeningFamily`'s families are indexed by `n` with components at
`R ⧸ I ^ (n + 1)`. So `f.1 n` pairs with `limit.π _ ⟨n + 1⟩`, and the level-`0` component of the
cone is matched by nothing. It carries no information — `subsingleton_quotient_pow_zero` — and that
fact is used, in `limit_π_zero_eq`, rather than asserted in a comment.

**`CommRingCat` versus `LocallyRingedSpace`.** The cone's components are ring homomorphisms; the
family's are morphisms of locally ringed spaces. `Spec.locallyRingedSpaceMap` crosses that, and
`Spec.toLocallyRingedSpace`'s faithfulness crosses back — which is what
`eq_thickeningFamilyLimitEquiv` needs.

## The definition is a composite, and why that is not a problem here

`thickeningFamilyLimitEquiv` is defined as `(thickeningRestrictionEquiv I B).symm.trans
(specHomLimitEquiv I B)`. That is honest and cheap — the triangle already commutes on the nose,
because `thickeningMap_comp_eq_limit_π` (`IndSchemeLimitComponents.lean`) *is* the comparison one
component at a time and `thickeningRestrictionEquiv_apply` is `rfl`. Building `toFun` by hand out
of `specPreimage` and a cone lift would produce the same function and cost considerably more.

The real objection to a composite definition is that it is **opaque**: a reader cannot see the
correspondence "family ↔ cone" without unfolding through `Spf R ⟶ Spec B`. That is answered here
not by rebuilding the definition but by pinning it down from outside:

* `limit_π_thickeningFamilyLimitEquiv` computes every component, and
* `eq_thickeningFamilyLimitEquiv` says those components **determine** the element — anything with
  the same components at `⟨n + 1⟩` *is* `thickeningFamilyLimitEquiv I B f`.

Together those two characterise the equivalence completely, so nothing downstream ever has to
unfold it.

## Main definitions and results

* `FormalSpectrum.homTower`: abbreviation for the functor `n ↦ (B →+* R ⧸ Iⁿ)` whose limit is
  `specHomLimitEquiv`'s target.
* `FormalSpectrum.thickeningFamilyLimitEquiv`: **the identification** `ThickeningFamily I B ≃
  lim_n (B →+* R ⧸ Iⁿ)`.
* `FormalSpectrum.limit_π_thickeningFamilyLimitEquiv`: its component rule, with the index shift.
* `FormalSpectrum.limit_ext_succ`: an element of the limit is determined by its components at
  `⟨n + 1⟩` — the level-`0` component is free.
* `FormalSpectrum.eq_thickeningFamilyLimitEquiv`: the characterisation by components.
* `FormalSpectrum.thickeningFamilyLimitEquiv_specFamily` and
  `FormalSpectrum.limit_π_thickeningFamilyLimitEquiv_specFamily`: **all three bijections agree** on
  the family attached to a ring homomorphism `ψ : B →+* R`, whose cone is reduction of `ψ`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6 (10.6.7).
* [The Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable (B : Type u) [CommRing B]

/-- The functor `n ↦ (B →+* R ⧸ Iⁿ)` whose limit is the right-hand side of `specHomLimitEquiv`.
An `abbrev`, so that the lemmas of `FormalSchemes/IndSchemeLimitComponents.lean` — which spell the
composite out — apply to goals stated with this name and conversely. -/
abbrev homTower : ℕᵒᵖ ⥤ Type u :=
  AdicCompletion.quotientTower I ⋙ coyoneda.obj (op (CommRingCat.of B))

/-- **The two presentations of the colimit property agree** (EGA I, 10.6.7): a compatible family of
morphisms out of the infinitesimal thickenings is the same datum as a point of
`lim_n Hom(Spec (R ⧸ Iⁿ), Spec B)`.

Defined as a composite of the two known bijections; it is pinned down from outside by
`limit_π_thickeningFamilyLimitEquiv` and `eq_thickeningFamilyLimitEquiv`, which between them
determine it, so no consumer needs to unfold this definition. -/
def thickeningFamilyLimitEquiv :
    ThickeningFamily I B ≃ (limit (homTower I B) : Type u) :=
  (thickeningRestrictionEquiv I B).symm.trans (specHomLimitEquiv I B)

/-- **Component rule**: the `(n + 1)`-st leg of the cone attached to a compatible family `f` is,
after `Spec`, the family's `n`-th member. The shift is the one discussed in the module docstring —
`quotientTower` has level `n` equal to `R ⧸ Iⁿ`, while `f` starts at `R ⧸ I¹`. -/
theorem limit_π_thickeningFamilyLimitEquiv (f : ThickeningFamily I B) (n : ℕ) :
    Spec.locallyRingedSpaceMap (limit.π (homTower I B) ⟨n + 1⟩
      (thickeningFamilyLimitEquiv I B f)) = f.1 n := by
  rw [thickeningFamilyLimitEquiv, Equiv.trans_apply,
    ← thickeningMap_comp_eq_limit_π I B ((thickeningRestrictionEquiv I B).symm f) n]
  exact thickeningMap_comp_thickeningRestrictionEquiv_symm I B f n

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The level-`0` leg of the cone carries no information**: it lands in `B →+* R ⧸ I⁰`, and
`R ⧸ I⁰` is the zero ring (`subsingleton_quotient_pow_zero`). This is exactly why the index shift
above loses nothing. -/
theorem limit_π_zero_eq (u v : (limit (homTower I B) : Type u)) :
    limit.π (homTower I B) ⟨0⟩ u = limit.π (homTower I B) ⟨0⟩ v := by
  haveI : Subsingleton ((AdicCompletion.quotientTower I).obj (op 0)) :=
    subsingleton_quotient_pow_zero I
  exact CommRingCat.hom_ext (RingHom.ext fun _ => Subsingleton.elim _ _)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **An element of `lim_n (B →+* R ⧸ Iⁿ)` is determined by its components at `⟨n + 1⟩`.** The
level-`0` obligation of `Types.limit_ext` is discharged by `limit_π_zero_eq`. -/
theorem limit_ext_succ {u v : (limit (homTower I B) : Type u)}
    (h : ∀ n : ℕ, limit.π (homTower I B) ⟨n + 1⟩ u = limit.π (homTower I B) ⟨n + 1⟩ v) :
    u = v := by
  refine Types.limit_ext _ u v fun j => ?_
  induction j using Opposite.rec with
  | op n =>
    cases n with
    | zero => exact limit_π_zero_eq I B u v
    | succ m => exact h m

/-- **The component rule characterises `thickeningFamilyLimitEquiv`**: any point of the limit whose
legs restrict, after `Spec`, to the members of `f` *is* the point attached to `f`. Together with
`limit_π_thickeningFamilyLimitEquiv` this determines the equivalence without unfolding it, which is
what makes the composite definition above harmless.

The step from an equality of `Spec`-images back to an equality of ring homomorphisms is
faithfulness of `Spec.toLocallyRingedSpace`; note `Functor.preimage`-style reasoning lands in
`CommRingCatᵒᵖ`, whence the `Quiver.Hom.op_inj`. -/
theorem eq_thickeningFamilyLimitEquiv (f : ThickeningFamily I B)
    (u : (limit (homTower I B) : Type u))
    (h : ∀ n : ℕ, Spec.locallyRingedSpaceMap (limit.π (homTower I B) ⟨n + 1⟩ u) = f.1 n) :
    u = thickeningFamilyLimitEquiv I B f := by
  refine limit_ext_succ I B fun n => Quiver.Hom.op_inj
    (Spec.toLocallyRingedSpace.map_injective ?_)
  change Spec.locallyRingedSpaceMap (limit.π (homTower I B) ⟨n + 1⟩ u) =
    Spec.locallyRingedSpaceMap (limit.π (homTower I B) ⟨n + 1⟩ (thickeningFamilyLimitEquiv I B f))
  rw [h n, limit_π_thickeningFamilyLimitEquiv]

/-- **All three bijections agree on a ring homomorphism.** The cone attached to the canonical family
of `ψ : B →+* R` is the cone `specHomLimitEquiv` attaches to the morphism `specHomEquiv` attaches to
`ψ`. -/
theorem thickeningFamilyLimitEquiv_specFamily (ψ : B →+* R) :
    thickeningFamilyLimitEquiv I B (specFamily I B ψ) =
      specHomLimitEquiv I B ((specHomEquiv I B).symm ψ) := by
  rw [thickeningFamilyLimitEquiv, Equiv.trans_apply,
    ← thickeningRestrictionEquiv_specHomEquiv_symm I B ψ, Equiv.symm_apply_apply]

/-- The same, read on components: the cone attached to the canonical family of `ψ` is reduction of
`ψ` modulo the powers of `I`. Note this holds at **every** level, including `0`, since it is read
off `limit_π_specHomLimitEquiv` rather than off the shifted rule. -/
theorem limit_π_thickeningFamilyLimitEquiv_specFamily (ψ : B →+* R) (n : ℕ) :
    limit.π (homTower I B) ⟨n⟩ (thickeningFamilyLimitEquiv I B (specFamily I B ψ)) =
      CommRingCat.ofHom ((Ideal.Quotient.mk (I ^ n)).comp ψ) := by
  rw [thickeningFamilyLimitEquiv_specFamily, limit_π_specHomLimitEquiv, Equiv.apply_symm_apply]

/-! ### A concrete witness

`[IsAdicRing I]` holds vacuously at `I = ⊥`, where every thickening is `Spec R` and both
presentations collapse. The shared `2`-adic witness rules that out. -/

section Nonvacuity

attribute [local instance] isAdicRing_twoAdicIdeal

/-- **At the `2`-adic integers, the cone attached to `ℤ → ℤ^` is reduction modulo `2ⁿ`.** -/
example (n : ℕ) :
    limit.π (homTower twoAdicIdeal ℤ) ⟨n⟩
        (thickeningFamilyLimitEquiv twoAdicIdeal ℤ (specFamily twoAdicIdeal ℤ
          (algebraMap ℤ (AdicCompletion (Ideal.span {(2 : ℤ)}) ℤ)))) =
      CommRingCat.ofHom ((Ideal.Quotient.mk (twoAdicIdeal ^ n)).comp
        (algebraMap ℤ (AdicCompletion (Ideal.span {(2 : ℤ)}) ℤ))) :=
  limit_π_thickeningFamilyLimitEquiv_specFamily twoAdicIdeal ℤ _ n

end Nonvacuity

end FormalSpectrum

end
