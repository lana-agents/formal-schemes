import FormalSchemes.SpfTargetSurjective

set_option linter.style.header false

/-!
# Being a target of the colimit property, as a property of one space

`FormalSchemes/SpfTargetColimit.lean` records that, for an arbitrary target `X`, the colimit
property of `Spf R` is **exactly** surjectivity of `FormalSpectrum.restrictToThickeningsLRS`,
because injectivity holds unconditionally (`injective_restrictToThickeningsLRS`). Two classes of
target are now known to have it:

* `Spec B`, for any commutative ring `B` — `surjective_restrictToThickeningsLRS`, the
  affine-target theorem of umbrella 59;
* `Spf L`, for a finitely generated ideal of definition `L` — issue 62m's goal 2,
  `surjective_restrictToThickeningsLRS_spf`.

Nothing on the tree lets a construction quantify over *both*. Every statement of the
chart-and-glue chain that runs from `ThickeningChartSpfHom.lean` to `SpfHomOfFamily.lean` takes
the affine datum `(B, e : X|_U ≅ Spec B)` in its **statement**, so the `Spf`-shaped cover of
issue 62m cannot be fed to any of them.

This file introduces the one predicate that lets them be stated once:

```lean
FormalSpectrum.IsThickeningColimitTarget Y :=
  ∀ (J : Ideal S) [IsAdicRing J], J.FG → Function.Surjective (restrictToThickeningsLRS J Y)
```

and proves that `Spec B` and `Spf L` (with `L.FG`) both satisfy it.

## Why the predicate quantifies over the adic ring

A chart of the source is `Spf R{1/r}`, so the ideal a chart morphism is built at is
`awayCompletionIdeal I r` and not `I`. The gluing step chooses one `r` per point of `|Spf R|`,
inside the proof, so a hypothesis fixed at a single adic ring cannot be supplied at the call site.
Quantifying over all of them costs nothing: both instances below are proved for an arbitrary adic
ring already.

## Why `J.FG` is a hypothesis and not a mistake

`surjective_restrictToThickeningsLRS` needs `hI : I.FG` — the affine-target proof refines the
pullback of the cover by basic opens and needs each `R{1/r}` to be adic, which is
`isAdicRing_awayCompletionIdeal` and needs it. So `Spec B` does **not** satisfy the hypothesis-free
form of this predicate as far as this tree knows, and the predicate is stated at the strength both
instances actually have. The `Spf` instance is stronger — `surjective_restrictToThickeningsLRS_spf`
has no hypothesis on the *source* ideal at all — and simply ignores the argument.

## Main definitions

* `FormalSpectrum.IsThickeningColimitTarget`: the property.

## Main results

* `FormalSpectrum.isThickeningColimitTarget_spec`: `Spec B` has it.
* `FormalSpectrum.isThickeningColimitTarget_spf`: `Spf L` has it, for `L.FG`.
* `FormalSpectrum.IsThickeningColimitTarget.of_iso`: it transports along an isomorphism.
* `FormalSpectrum.IsThickeningColimitTarget.restrict`: **every open subspace of such a target is
  one** — a producer that hands back neither a formal spectrum nor a cover by them.
* `FormalSpectrum.isThickeningColimitTarget_of_isOpenImmersion`: the same, for an open immersion
  in place of an `Opens`.
* `FormalSpectrum.thickeningRestrictionEquivOfColimitTarget`: the colimit property of `Spf R` at
  such a target, as a bijection — injectivity is free, so the predicate is the whole of it.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6 (10.6.10).
* [The Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace FormalSpectrum

/-- **`Y` is a target of the colimit property of formal spectra**: for every adic ring with a
finitely generated ideal of definition, restriction to the infinitesimal thickenings is surjective
onto the compatible families.

Together with `injective_restrictToThickeningsLRS`, which holds for every target whatsoever, this
says that `Hom(Spf S, Y)` *is* the set of compatible families — see
`thickeningRestrictionEquivOfColimitTarget`. It is stated as surjectivity rather than as a
bijection so that the two known instances, which are surjectivity statements, satisfy it without
repackaging. -/
def IsThickeningColimitTarget (Y : LocallyRingedSpace.{u}) : Prop :=
  ∀ {S : Type u} [CommRing S] [TopologicalSpace S] (J : Ideal S) [IsAdicRing J], J.FG →
    Function.Surjective (restrictToThickeningsLRS J Y)

/-- **An affine scheme is such a target** (EGA I, 10.6.10 at an affine target). This is
`surjective_restrictToThickeningsLRS` at the one-piece cover `⊤`, whose affine identification is
`LocallyRingedSpace.restrictTopIso`. -/
theorem isThickeningColimitTarget_spec (B : Type u) [CommRing B] :
    IsThickeningColimitTarget (Spec.locallyRingedSpaceObj (CommRingCat.of B)) := by
  intro S _ _ J _ hJ
  exact surjective_restrictToThickeningsLRS J _ hJ (fun _ : PUnit.{u + 1} => ⊤) iSup_const
    (fun _ => B) fun _ => (Spec.locallyRingedSpaceObj (CommRingCat.of B)).restrictTopIso

/-- **A formal affine is such a target**, for a finitely generated ideal of definition — issue
62m's goal 2, `surjective_restrictToThickeningsLRS_spf`.

Note the asymmetry with `isThickeningColimitTarget_spec`: the finite generation needed here is of
the *target's* ideal `L`, and the predicate's hypothesis on the source ideal `J` is discarded. -/
theorem isThickeningColimitTarget_spf {C : Type u} [CommRing C] [TopologicalSpace C] (L : Ideal C)
    [IsAdicRing L] (hL : L.FG) : IsThickeningColimitTarget (locallyRingedSpaceObj L) := by
  intro S _ _ J _ _
  exact surjective_restrictToThickeningsLRS_spf J L hL

/-- **The property transports along an isomorphism of the target.** A compatible family into `X`
becomes one into `Y` by postcomposition with `e.hom`, and the morphism out of `Spf S` that `Y`
supplies is carried back by `e.inv`.

It is needed because every *supply* of the property on this tree is stated at a named space
(`Spec B`, `Spf L`) while every *consumer* — `isThickeningColimitTarget_of_cover` and the chart
data of `FormalSchemes.SpfHomColimitTarget` — asks for it at a restriction `X|_U`, and the two are
related by an isomorphism rather than by equality. -/
theorem IsThickeningColimitTarget.of_iso {X Y : LocallyRingedSpace.{u}}
    (hY : IsThickeningColimitTarget Y) (e : X ≅ Y) : IsThickeningColimitTarget X := by
  intro S _ _ J _ hJ F
  obtain ⟨g, hg⟩ := hY J hJ ⟨fun n => F.1 n ≫ e.hom, fun n => by rw [← Category.assoc, F.2 n]⟩
  refine ⟨g ≫ e.inv, Subtype.ext (funext fun n => ?_)⟩
  have hn := congrFun (congrArg Subtype.val hg) n
  simp only [restrictToThickeningsLRS] at hn ⊢
  rw [← Category.assoc, hn, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- **An open subspace of a target of the colimit property is one.** No hypothesis on `X` beyond
the property itself, and none at all on the open.

The argument is that `|Spf S|` is the space of the *first* thickening. The base map of
`thickeningMap S 0` is the homeomorphism `thickeningTopIso` — that is
`FormalSpectrum.commonBase_comp_thickeningMap` — so a morphism `g : Spf S ⟶ X` has the same image
as the level-`0` member of the family it restricts to. Here that member factors through
`X.ofRestrict V.isOpenEmbedding` by construction, so `g`'s image lies in `V` and
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift` produces the factorisation. That the
factorisation restricts to the given family is then forced by the inclusion being a monomorphism,
so no uniqueness clause is used.

Note the direction: `isThickeningColimitTarget_of_cover` (`FormalSchemes.SpfHomColimitTarget`)
assembles the property *upwards* from a cover, and this takes it *downwards* to a single open;
together they say the property is local, which is
`FormalSpectrum.isThickeningColimitTarget_iff_forall_exists_mem`. -/
theorem IsThickeningColimitTarget.restrict {X : LocallyRingedSpace.{u}}
    (hX : IsThickeningColimitTarget X) (V : Opens X.toTopCat) :
    IsThickeningColimitTarget (X.restrict V.isOpenEmbedding) := by
  intro S _ _ J _ hJ F
  obtain ⟨g, hg⟩ := hX J hJ ⟨fun n => F.1 n ≫ X.ofRestrict V.isOpenEmbedding, fun n => by
    rw [← Category.assoc, F.2 n]⟩
  have hgn : ∀ n, thickeningMap J n ≫ g = F.1 n ≫ X.ofRestrict V.isOpenEmbedding :=
    fun n => congrFun (congrArg Subtype.val hg) n
  have hrange : Set.range g.base ⊆ Set.range (X.ofRestrict V.isOpenEmbedding).base := by
    rw [← commonBase_comp_thickeningMap J g 0, hgn 0]
    rintro _ ⟨y, rfl⟩
    exact ⟨_, rfl⟩
  refine ⟨LocallyRingedSpace.IsOpenImmersion.lift _ g hrange, Subtype.ext (funext fun n => ?_)⟩
  simp only [restrictToThickeningsLRS]
  rw [← cancel_mono (X.ofRestrict V.isOpenEmbedding), Category.assoc,
    LocallyRingedSpace.IsOpenImmersion.lift_fac]
  exact hgn n

/-- **The source of an open immersion into such a target is one**: `restrict` at the range of the
immersion, read back along
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoRestrictOpensRange`
(`FormalSchemes.OpenImmersionIsoOfRangeEq`). This is the form the property is consumed in when the
open arrives as the range of a morphism rather than as an `Opens`. -/
theorem isThickeningColimitTarget_of_isOpenImmersion {X Y : LocallyRingedSpace.{u}}
    (hY : IsThickeningColimitTarget Y) (j : X ⟶ Y) [LocallyRingedSpace.IsOpenImmersion j] :
    IsThickeningColimitTarget X :=
  IsThickeningColimitTarget.of_iso
    (IsThickeningColimitTarget.restrict hY (LocallyRingedSpace.IsOpenImmersion.opensRange j))
    (LocallyRingedSpace.IsOpenImmersion.isoRestrictOpensRange j).symm

variable {S : Type u} [CommRing S] [TopologicalSpace S] (J : Ideal S) [IsAdicRing J]

/-- **The colimit property at such a target, as a bijection.** Injectivity is
`injective_restrictToThickeningsLRS` and needs no hypothesis, so the predicate carries the whole
content. Compare `thickeningRestrictionEquivLRS`, which obtains surjectivity from a `Spec`-shaped
cover of the target, and `thickeningRestrictionEquivSpf`, which takes it as a bare argument. -/
def thickeningRestrictionEquivOfColimitTarget {Y : LocallyRingedSpace.{u}}
    (hY : IsThickeningColimitTarget Y) (hJ : J.FG) :
    (locallyRingedSpaceObj J ⟶ Y) ≃ ThickeningFamilyLRS J Y :=
  Equiv.ofBijective _ ⟨injective_restrictToThickeningsLRS J Y, hY J hJ⟩

/-- **Computation rule.** The forward map is restriction to the thickenings, as for every other
member of this family of bijections. -/
theorem thickeningRestrictionEquivOfColimitTarget_apply {Y : LocallyRingedSpace.{u}}
    (hY : IsThickeningColimitTarget Y) (hJ : J.FG) (g : locallyRingedSpaceObj J ⟶ Y) (n : ℕ) :
    (thickeningRestrictionEquivOfColimitTarget J hY hJ g).1 n = thickeningMap J n ≫ g :=
  rfl

end FormalSpectrum

end
