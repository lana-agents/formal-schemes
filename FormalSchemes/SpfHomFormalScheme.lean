import FormalSchemes.LocallyFG
import FormalSchemes.SpfHomColimitTarget

set_option linter.style.header false

/-!
# EGA I, 10.6.10 at a formal-scheme target

`FormalSchemes/SpfHomScheme.lean` discharges the cover arguments of
`FormalSpectrum.existsUnique_hom_thickeningMap` for `X : Scheme`, using `Scheme.local_affine`.
This file does the same for `X : FormalScheme`, using `FormalScheme.LocallyFG` — the two
statements are the `Spec`-side and the `Spf`-side of one theorem, and the `Spf` side became
available only with `FormalSpectrum.IsThickeningColimitTarget`
(`FormalSchemes.ThickeningColimitTarget`, issue 1336).

## Why `FormalScheme.LocallyFG` and not `FormalScheme.local_affine`

`FormalScheme` asks for charts `X|_U ≅ Spf I` with `IsAdicRing I` and **nothing else**;
`FormalSpectrum.isThickeningColimitTarget_spf` needs `I.FG`, because the affine-target theorem it
rests on refines the pullback of the cover by basic opens and `FormalSpectrum.basicOpenChart` is
an open immersion only for a finitely generated ideal. So the hypothesis here is
`AlgebraicGeometry.FormalScheme.LocallyFG` (`FormalSchemes.LocallyFG`), which is exactly
`FormalScheme.local_affine` with `I.FG` added, and not the structure field. Whether the field
alone suffices is not settled here and nothing below assumes it does.

## Main results

* `FormalSpectrum.existsUnique_hom_thickeningMap_of_isThickeningColimitTarget`: the colimit
  property in `∃!` form, from the predicate alone. The two landed `∃!` statements of this cluster
  reach it through a cover; this is the direct route, and it is the one a *space* known to have
  the property needs.
* `FormalSpectrum.isThickeningColimitTarget_formalScheme`: **a locally finitely generated formal
  scheme is a target of the colimit property.**
* `FormalSpectrum.existsUnique_hom_thickeningMap_formalScheme` and
  `FormalSpectrum.thickeningRestrictionEquivFormalScheme`: EGA I 10.6.10 at such a target, as an
  `∃!` and as a bijection, with `hI : I.FG` and `hX : X.LocallyFG` the only hypotheses.

The general theorem is applied at a target that is genuinely glued — neither `Spec` nor `Spf` of
anything — in `FormalSchemes.TateChainInvColimitTarget`. At `Spf I` itself it reproduces
`FormalSpectrum.isThickeningColimitTarget_spf`, and issue 1479 deleted the consumerless theorem
that recorded that: the two statements are definitionally equal, so the tree keeps one.

## What is *not* proved

Nothing here is about a locally ringed space that is not already known to be a formal scheme. In
particular the quotient `T_inv/⟨σ⟩` of issue 1197 is out of reach: the theorem's hypothesis is
what that issue is trying to establish, so applying it there would be circular in exactly the way
`FormalSchemes.TateInvNodeChartHomExt` records.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6 (10.6.10).
* [The Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace FormalSpectrum

open LocallyRingedSpace.IsOpenImmersion

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]

section General

variable {X : LocallyRingedSpace.{u}}
variable (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X)
    (hf : ∀ n : ℕ, Spec.locallyRingedSpaceMap (stepRingHom I n) ≫ f (n + 1) = f n)

include hf in
/-- **The colimit property in `∃!` form, from the predicate alone.** Surjectivity of
`FormalSpectrum.restrictToThickeningsLRS` is existence and
`FormalSpectrum.injective_restrictToThickeningsLRS` is uniqueness, so this is
`FormalSpectrum.thickeningRestrictionEquivOfColimitTarget` read as a statement about one family.

The two landed `∃!` statements — `FormalSpectrum.existsUnique_hom_thickeningMap` and
`FormalSpectrum.ColimitTarget.existsUnique_hom_thickeningMap` — take a cover of the target and
produce the predicate on the way. A space already known to have the property does not need to
re-supply one. -/
theorem existsUnique_hom_thickeningMap_of_isThickeningColimitTarget
    (hX : IsThickeningColimitTarget X) (hI : I.FG) :
    ∃! g : locallyRingedSpaceObj I ⟶ X, ∀ n : ℕ, thickeningMap I n ≫ g = f n := by
  obtain ⟨g, hg⟩ := hX I hI ⟨f, hf⟩
  refine ⟨g, fun n => congrFun (congrArg Subtype.val hg) n, fun g' hg' => ?_⟩
  exact injective_restrictToThickeningsLRS I X ((Subtype.ext (funext hg')).trans hg.symm)

end General

section FormalSchemeTarget

variable (X : FormalScheme.{u}) (hX : X.LocallyFG)

include hX in
/-- **A locally finitely generated formal scheme is a target of the colimit property**, i.e. EGA I
10.6.10 holds with `X` on the right.

The cover is indexed by the points of `X`: `AlgebraicGeometry.FormalScheme.LocallyFG` supplies at
each `x` an open immersion `Spf (L x) ⟶ X` whose range contains `x` and whose ideal of definition
is finitely generated, `IsOpenImmersion.isoRestrictOpensRange` turns it into the chart datum
`X|_{range} ≅ Spf (L x)` that `FormalSpectrum.isThickeningColimitTarget_of_cover` asks for, and
each piece has the property by `FormalSpectrum.isThickeningColimitTarget_spf`. The cover condition
holds for the cheapest possible reason: `x` lies in its own piece. -/
theorem isThickeningColimitTarget_formalScheme :
    IsThickeningColimitTarget X.toLocallyRingedSpace := by
  choose C hC hT L hA c hLfg hmem hc using hX
  letI := hC
  letI := hT
  letI := hA
  letI := hc
  have hcov : (⨆ x, opensRange (c x)) = ⊤ := by
    refine Opens.ext (Set.eq_univ_of_forall fun x => ?_)
    rw [Opens.coe_iSup]
    exact Set.mem_iUnion.2 ⟨x, hmem x⟩
  intro S _ _ J _ hJ
  exact isThickeningColimitTarget_of_cover (fun x => opensRange (c x)) hcov
    (fun x => locallyRingedSpaceObj (L x)) (fun x => isoRestrictOpensRange (c x))
    (fun x => isThickeningColimitTarget_spf (L x) (hLfg x)) J hJ

variable {X}
variable (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶
    X.toLocallyRingedSpace)
    (hf : ∀ n : ℕ, Spec.locallyRingedSpaceMap (stepRingHom I n) ≫ f (n + 1) = f n)

include hf hX in
/-- **`Spf R` is the colimit of its infinitesimal thickenings, for a locally finitely generated
formal scheme** (EGA I, 10.6.10): a compatible family `Spec (R ⧸ Iⁿ⁺¹) ⟶ X` comes from a unique
`Spf R ⟶ X`.

This is the `Spf`-side companion of `FormalSpectrum.existsUnique_hom_thickeningMap_scheme`, and
like it leaves `hI : I.FG` — together with `hX` — as the only hypotheses. -/
theorem existsUnique_hom_thickeningMap_formalScheme (hI : I.FG) :
    ∃! g : locallyRingedSpaceObj I ⟶ X.toLocallyRingedSpace,
      ∀ n : ℕ, thickeningMap I n ≫ g = f n :=
  existsUnique_hom_thickeningMap_of_isThickeningColimitTarget I f hf
    (isThickeningColimitTarget_formalScheme X hX) hI

/-- **The same, as a bijection**: restriction to the thickenings is a bijection from
`Spf R ⟶ X` onto the compatible families. Compare
`FormalSpectrum.thickeningRestrictionEquivScheme`, which is this at a scheme. -/
def thickeningRestrictionEquivFormalScheme (hI : I.FG) :
    (locallyRingedSpaceObj I ⟶ X.toLocallyRingedSpace) ≃ ThickeningFamilyLRS I
      X.toLocallyRingedSpace :=
  thickeningRestrictionEquivOfColimitTarget I (isThickeningColimitTarget_formalScheme X hX) hI

/-- **Computation rule.** The forward map is restriction to the thickenings. -/
theorem thickeningRestrictionEquivFormalScheme_apply (hI : I.FG)
    (g : locallyRingedSpaceObj I ⟶ X.toLocallyRingedSpace) (n : ℕ) :
    (thickeningRestrictionEquivFormalScheme I hX hI g).1 n = thickeningMap I n ≫ g :=
  rfl

end FormalSchemeTarget

end FormalSpectrum
