import FormalSchemes.TateInvNodeChartSpfNonempty
import FormalSchemes.ThickeningHomExt

set_option linter.style.header false

/-!
# The node chart morphism is determined by its thickenings

Issue 1197's residue is a single morphism out of the node chart's formal spectrum,

```
f : Spf (tateInvNodeChartAwayIdeal …) ⟶ T_inv/⟨σ⟩
```

required to be an open immersion covering the node. This file settles its **uniqueness**, and
does so with no hypothesis at all on the target: two such morphisms agreeing on every
infinitesimal thickening of the source are equal.

## Main results

* `AlgebraicGeometry.hom_ext_tateInvNodeChartSpf` and
  `AlgebraicGeometry.injective_thickeningRestriction_tateInvNodeChartSpf`: a morphism out of
  `Spf` of the node chart ring into an **arbitrary** locally ringed space is determined by the
  family of its restrictions to the thickenings `Spec (S ⧸ Jⁿ⁺¹)`.
  `AlgebraicGeometry.hom_ext_tateInvNodeChartSpf_actionQuotient` is that at
  `CategoryTheory.actionQuotient` itself, which is issue 1197's residual morphism proved unique.
* `AlgebraicGeometry.nonempty_thickening_tateInvNodeChart`: for `I ≠ ⊤` every one of those
  thickenings is a **nonempty** scheme, so the family the results above are about is not a family
  of morphisms out of empty spaces. `AlgebraicGeometry.nonempty_hom_tateInvNodeChartSpf` is the
  matching guard on the other side: the type the injectivity is stated about is inhabited.

## Why this is worth a name

They are one-line instantiations of `FormalSpectrum.hom_ext_thickeningMap_lrs`
(`FormalSchemes.ThickeningHomExt`), which is the uniqueness half of EGA I 10.6.3 and whose binders
are `{R} [CommRing R] {I : Ideal R} {X : LocallyRingedSpace}` — **no `IsAdicRing`, no `Ideal.FG`,
no cover, and no hypothesis on the target**. What the instantiation buys is a change in what issue
1197 is asking. Its residue is stated as "build a morphism `Spf (chart ring) ⟶ T_inv/⟨σ⟩`"; with
uniqueness settled, the residue is exactly

> exhibit a compatible family `Spec (S ⧸ Jⁿ⁺¹) ⟶ T_inv/⟨σ⟩`

— an existence question about morphisms **out of schemes**, with nothing left to decide about the
morphism it determines.

## A correction: the tree's mapping-out machinery, surveyed

`FormalSchemes.TateInvNodeChartSpf` records that *no construction on this tree produces a morphism
out of a formal spectrum into a general locally ringed space*, and
`FormalSchemes.TateInvNodeChartSpfNonempty` cited that forward until this file's commit corrected
it. **The claim is false**, and the following are all on the tree:

* `FormalSpectrum.hom_ext_thickeningMap_lrs` — the uniqueness half, arbitrary target, no
  hypotheses. This file's input.
* `FormalSpectrum.existsUnique_hom_thickeningMap` (`FormalSchemes.SpfHomOfFamily`) — **EGA I
  10.6.10**: a compatible family `Spec (R ⧸ Iⁿ⁺¹) ⟶ X` comes from a unique `Spf R ⟶ X`, for `X` a
  bare locally ringed space carrying a cover by opens equipped with isomorphisms to `Spec (B i)`.
  The morphism is `FormalSpectrum.spfHomOfFamily`; `FormalSpectrum.thickeningRestrictionEquivLRS`
  (`FormalSchemes.IndSchemeColimitEquivLRS`) is the same statement as an `Equiv`, and
  `FormalSpectrum.existsUnique_hom_thickeningMap_scheme` (`FormalSchemes.SpfHomScheme`) is it for
  `X : Scheme` with `Ideal.FG` the only hypothesis.
* `AdicRingCat.spfHomEquiv` (`FormalSchemes.SpfFullyFaithful`) — full faithfulness of `Spf` onto
  the continuous morphisms, for a formal-spectrum target.

The two candidates that survey *rejected* were rejected correctly:
`AlgebraicGeometry.FormalScheme.OpenCover.glueHomOfGlobalSectionsHom` needs a formal scheme for its
source and points into a formal spectrum, and `FormalSpectrum.locallyRingedSpaceMap` has a formal
spectrum for its target. What it missed is the `IndScheme*` / `SpfHom*` layer.

## What is *not* proved here, and what the block actually is

**No morphism `f` is built.** `existsUnique_hom_thickeningMap` needs the target covered by opens
isomorphic to `Spec` of a ring, and `T_inv/⟨σ⟩`'s charts are formal-affine. So the honest
statement of the obstruction is not that the construction is missing but that

> every mapping-out property of `Spf` on this tree needs the target to carry affine charts
> already, and the quotient's only missing chart is the one being built — applying them there is
> **circular, not impossible**.

The `Spf`-target analogue of `existsUnique_hom_thickeningMap` (the same theorem with
`X.restrict _ ≅ Spf (B i)`) is not on the tree and is not attempted here. Only step three of
`FormalSchemes.SpfHomOfFamily`'s five-step construction is `Spec`-specific, so it has a model to
imitate; whether it would break the circularity for `T_inv/⟨σ⟩` is unexamined.

**Nothing here says a compatible family exists.** The uniqueness is unconditional precisely
because it says nothing about existence.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6 (10.6.3, 10.6.10).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum TopologicalSpace
open Opposite

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)

/-- **A morphism out of `Spf` of the node chart ring is determined by its thickenings.** This is
`FormalSpectrum.hom_ext_thickeningMap_lrs` at `AlgebraicGeometry.tateInvNodeChartAwayIdeal`; the
target `Q` is an arbitrary locally ringed space and there is no hypothesis on it, so this applies
verbatim to `T_inv/⟨σ⟩` for any presentation of the quotient. -/
theorem hom_ext_tateInvNodeChartSpf {Q : LocallyRingedSpace.{u}}
    (g₁ g₂ : FormalSpectrum.locallyRingedSpaceObj (tateInvNodeChartAwayIdeal R I q hq hI) ⟶ Q)
    (h : ∀ n : ℕ, FormalSpectrum.thickeningMap (tateInvNodeChartAwayIdeal R I q hq hI) n ≫ g₁ =
      FormalSpectrum.thickeningMap (tateInvNodeChartAwayIdeal R I q hq hI) n ≫ g₂) :
    g₁ = g₂ :=
  FormalSpectrum.hom_ext_thickeningMap_lrs g₁ g₂ h

/-- **The restriction-to-thickenings map is injective**, at the node chart ring and an arbitrary
target. The `Function.Injective` form of `AlgebraicGeometry.hom_ext_tateInvNodeChartSpf`: it is
what says issue 1197's residue is an *existence* question about compatible families
`Spec (S ⧸ Jⁿ⁺¹) ⟶ Q`, the morphism they determine being unique. -/
theorem injective_thickeningRestriction_tateInvNodeChartSpf {Q : LocallyRingedSpace.{u}} :
    Function.Injective fun
        g : FormalSpectrum.locallyRingedSpaceObj (tateInvNodeChartAwayIdeal R I q hq hI) ⟶ Q =>
      fun n : ℕ => FormalSpectrum.thickeningMap (tateInvNodeChartAwayIdeal R I q hq hI) n ≫ g :=
  fun _ _ h => hom_ext_tateInvNodeChartSpf R I q hq hI _ _ (fun n => congrFun h n)

/-- **The same at the quotient itself**, so a consumer working with `CategoryTheory.actionQuotient`
does not have to instantiate the general statement. This is issue 1197's residual morphism `f`
proved unique: two morphisms `Spf (chart ring) ⟶ T_inv/⟨σ⟩` with the same restrictions to the
thickenings are equal, whether or not either is an open immersion. -/
theorem hom_ext_tateInvNodeChartSpf_actionQuotient
    (g₁ g₂ : FormalSpectrum.locallyRingedSpaceObj (tateInvNodeChartAwayIdeal R I q hq hI) ⟶
      actionQuotient (tateInvPeriodAction R I q hq hI))
    (h : ∀ n : ℕ, FormalSpectrum.thickeningMap (tateInvNodeChartAwayIdeal R I q hq hI) n ≫ g₁ =
      FormalSpectrum.thickeningMap (tateInvNodeChartAwayIdeal R I q hq hI) n ≫ g₂) :
    g₁ = g₂ :=
  hom_ext_tateInvNodeChartSpf R I q hq hI g₁ g₂ h

/-- **The type the injectivity above is about is not empty.** `Function.Injective` is vacuously
true on an empty domain, so the identity is recorded as a witness that morphisms out of
`Spf` of the node chart ring exist at *some* target. It says nothing about the target issue 1197
needs, which is exactly what is open. -/
theorem nonempty_hom_tateInvNodeChartSpf :
    Nonempty (FormalSpectrum.locallyRingedSpaceObj (tateInvNodeChartAwayIdeal R I q hq hI) ⟶
      FormalSpectrum.locallyRingedSpaceObj (tateInvNodeChartAwayIdeal R I q hq hI)) :=
  ⟨𝟙 _⟩

/-- **The thickenings of the node chart are nonempty**, for `I ≠ ⊤`, so the families the two
results above are about are families of morphisms out of nonempty schemes.

`AlgebraicGeometry.ne_top_tateInvNodeChartAwayIdeal` gives `J ≠ ⊤`, powers of a proper ideal are
proper because `Ideal.pow_le_self` puts them below it, and
`FormalSpectrum.nonempty_iff_ne_top` converts. -/
theorem nonempty_thickening_tateInvNodeChart (hItop : I ≠ ⊤) (n : ℕ) :
    Nonempty (FormalSpectrum (tateInvNodeChartAwayIdeal R I q hq hI ^ (n + 1))) :=
  (FormalSpectrum.nonempty_iff_ne_top _).2 fun htop =>
    ne_top_tateInvNodeChartAwayIdeal R I q hq hI hItop
      (eq_top_iff.2 (htop ▸ Ideal.pow_le_self n.succ_ne_zero))

end AlgebraicGeometry
