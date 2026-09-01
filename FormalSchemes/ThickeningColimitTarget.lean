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
