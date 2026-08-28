import FormalSchemes.ThickeningCocone
import FormalSchemes.TwoAdicWitness

set_option linter.style.header false

/-!
# A compatible family out of the thickenings has a single base map (EGA I, 10.6.10)

`FormalSchemes/IndScheme.lean` and its successors describe morphisms out of `Spf R` **into an
affine scheme**: `specHomEquiv`, `existsUnique_thickeningMap_comp_of_specHom` and
`hom_ext_thickeningMap` all fix the target at `Spec B`, and all of them are proved through the
`Γ ⊣ Spec` adjunction, so none of them says anything when the target is a general locally ringed
space. That case — EGA I 10.6.10, `Hom(Spf R, X) ≃ limₙ Hom(Spec (R ⧸ Iⁿ⁺¹), X)` for arbitrary
`X` — is still open.

This file settles its **topological** half, which is independent of all the sheaf-theoretic
difficulty.

## The point

The infinitesimal thickenings all have the *same underlying space*: `thickeningTopIso I n` is an
isomorphism `|Spf R| ≅ |Spec (R ⧸ I ^ (n + 1))|` for every `n`, and the transition maps of the
tower are compatible with it
(`FormalSpectrum.thickeningTopIso_hom_comp_topMap_stepRingHom`). So a family

```
f n : Spec (R ⧸ I ^ (n + 1)) ⟶ X
```

compatible with the tower has no `n`-dependent topological content: pulling `(f n).base` back
along `thickeningTopIso I n` gives a continuous map `|Spf R| ⟶ |X|` that is **the same for every
`n`** (`FormalSpectrum.commonBase_eq`). Any morphism `Spf R ⟶ X` restricting to the family is
therefore forced to have that base map, and — going the other way — `commonBase` of the
restrictions of a morphism `g` recovers `g.base` exactly
(`FormalSpectrum.commonBase_comp_thickeningMap`).

Concretely this is what an eventual construction of `Spf R ⟶ X` will start from: without a single
well-defined map to `|X|` there is no way to pull back an affine open cover of `X` to a cover of
`|Spf R|` and run the affine case chart by chart.

## Main definitions and results

* `FormalSpectrum.base_step_of_compatible`: consecutive members of a compatible family induce the
  same map out of `|Spf R|`.
* `FormalSpectrum.commonBase`: that map, defined at level `0`.
* `FormalSpectrum.commonBase_eq`: it is computed by **every** level, not just level `0`. This is
  the theorem; the definition on its own says nothing.
* `FormalSpectrum.commonBase_comp_thickeningMap`: consistency with the existing theory — the
  restrictions of a morphism `g : Spf R ⟶ X` have `g.base` as their common base map.

## Implementation notes

Two things that are easy to get wrong here, both about *how* the step equation is derived rather
than about the mathematics.

**Do not use `congrArg` over a lambda in the morphism.** The obvious term

```lean
(congrArg (fun m : Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X =>
  (thickeningTopIso I n).hom ≫ m.base) (hf n)).symm
```

elaborates and then dies in the **kernel** with `(kernel) deterministic timeout`: checking it
forces the motive's type, which mentions the underlying space of `Spec` of a quotient ring, to be
unfolded. The tactic form `conv_lhs => rw [← hf n]` rewrites `f n` in place and costs nothing.

**The `Category.assoc` that follows needs a `change`, not a transparency bump.** After
`LocallyRingedSpace.comp_base` the middle factor is `(Spec.locallyRingedSpaceMap (stepRingHom I
n)).base`, whose type Lean spells `↑(Spec.locallyRingedSpaceObj _).toPresheafedSpace` where
`Spec.topMap` wants `Spec.topObj _`. The two are definitionally equal, `rw` will not see it, and
the error carries the familiar *"not type-correct under the `instances` transparency level"*
note. Naming the factor with `change` fixes it; `set_option backward.isDefEq.respectTransparency
false` is not needed and this file sets no options beyond the header linter.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6 (10.6.3, 10.6.10).
* [The Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable {X : LocallyRingedSpace.{u}}

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Consecutive members of a compatible family induce the same map out of `|Spf R|`.** Both
sides are `(f n).base` and `(f (n + 1)).base` read on `|Spf R|` through the identification of the
thickenings' spaces; they agree because the tower's transition map is that identification
(`thickeningTopIso_hom_comp_topMap_stepRingHom`). -/
theorem base_step_of_compatible
    (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X)
    (hf : ∀ n : ℕ, Spec.locallyRingedSpaceMap (stepRingHom I n) ≫ f (n + 1) = f n) (n : ℕ) :
    (thickeningTopIso I n).hom ≫ (f n).base =
      (thickeningTopIso I (n + 1)).hom ≫ (f (n + 1)).base := by
  conv_lhs => rw [← hf n]
  -- `rw` cannot reassociate here: `Spec.topObj` and the underlying space of
  -- `Spec.locallyRingedSpaceObj` are definitionally equal but not syntactically so.
  change (thickeningTopIso I n).hom ≫ Spec.topMap (stepRingHom I n) ≫ (f (n + 1)).base = _
  rw [← Category.assoc, thickeningTopIso_hom_comp_topMap_stepRingHom]

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The continuous map `|Spf R| ⟶ |X|` underlying a family of morphisms out of the
thickenings**, read off at level `0`. For a *compatible* family every other level gives the same
map (`commonBase_eq`), which is what makes this the right definition; no compatibility hypothesis
is needed to write it down. -/
def commonBase
    (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X) :
    TopCat.of (FormalSpectrum I) ⟶ X.toTopCat :=
  (thickeningTopIso I 0).hom ≫ (f 0).base

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **A compatible family out of the thickenings has one base map**, computed by any level of the
tower: the topological half of the colimit property (EGA I, 10.6.10) for an **arbitrary** locally
ringed space target. -/
theorem commonBase_eq
    (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X)
    (hf : ∀ n : ℕ, Spec.locallyRingedSpaceMap (stepRingHom I n) ≫ f (n + 1) = f n) (n : ℕ) :
    commonBase I f = (thickeningTopIso I n).hom ≫ (f n).base := by
  induction n with
  | zero => rfl
  | succ m ih => exact ih.trans (base_step_of_compatible I f hf m)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Consistency with the morphisms that already exist**: restricting `g : Spf R ⟶ X` to the
`n`-th thickening and reading the result on `|Spf R|` gives back `g.base`. Together with
`commonBase_eq` this says that the base map of a morphism out of `Spf R` is exactly the common
base map of its restrictions — so `commonBase` is the only candidate for the topological part of
an inverse to restriction. -/
theorem commonBase_comp_thickeningMap (g : locallyRingedSpaceObj I ⟶ X) (n : ℕ) :
    (thickeningTopIso I n).hom ≫ (thickeningMap I n ≫ g).base = g.base := by
  change (thickeningTopIso I n).hom ≫ (thickeningTopIso I n).inv ≫ g.base = g.base
  rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-! ### A concrete witness

The statements above are equations, so the risk of vacuity is not that they are unprovable but
that `[IsAdicRing I]` is only ever instantiated at `I = ⊥`, where every thickening is `Spec R`
and the tower is constant. The `2`-adic integers rule that out, by
`FormalSpectrum.twoAdicIdeal_ne_bot` (`FormalSchemes/TwoAdicWitness.lean`). The family used is the
tautological one — the thickening morphisms themselves, compatible by `thickeningMap_comp` — whose
common base map is the identity of `|Spf ℤ^|`, which is the only value it could have and is worth
pinning down. -/

section Nonvacuity

attribute [local instance] isAdicRing_twoAdicIdeal

/-- **The thickening morphisms of `Spf ℤ^` are a compatible family, and their common base map is
the identity.** -/
example : commonBase twoAdicIdeal (thickeningMap twoAdicIdeal) =
    𝟙 (TopCat.of (FormalSpectrum twoAdicIdeal)) :=
  (commonBase_eq twoAdicIdeal (thickeningMap twoAdicIdeal)
    (thickeningMap_comp twoAdicIdeal) 0).trans (Iso.hom_inv_id _)

end Nonvacuity

end FormalSpectrum

end
