import FormalSchemes.OpenFormalSubscheme
import FormalSchemes.ThreeChartCoverOpenImmersion
import FormalSchemes.ThreeChartCoverOverBase
import FormalSchemes.ThreeChartCoverSeparatedScheme
import FormalSchemes.ThreeChartCoverTopFiniteType

set_option linter.style.header false

/-!
# The three-chart cover, chart-free: `D(f₀) ∪ D(f₁) ∪ D(f₂)` as an open formal subscheme

This file closes the gap the last four PRs on this chain each recorded in their own docstring.

`FormalSchemes.ThreeChartCoverOpenImmersion` (issue 864) proves that `gluedXToBase` is an open
immersion with range `D(f₀) ∪ D(f₁) ∪ D(f₂)`, which says `gluedX` *is* an open formal subscheme of
`Spf A`. But it could not say so about an **object**, because the tree had no construction of the
open formal subscheme cut out by an open subset — only `basicOpenChart`, for a single basic open.
Consequently the two EGA properties of the cover,

* `gluedX_isSeparatedOverSpf` (§10.15, issue 852) and
* `gluedX_isRelativelyTopFiniteType` (§10.13, issue 858),

were stated about `gluedX I f B hI`, an object built from a presentation: three chart algebras, a
transition system, and the auxiliary algebra `B`. `FormalSchemes.OpenFormalSubscheme` supplies the
missing object, and this file restates both properties about it. Neither restatement mentions `B`,
a chart, a transition, or a glue datum — only `A`, the three elements `f₀, f₁, f₂`, and the ideal.

## The statements

```
FormalScheme.IsSeparatedOverSpf hI (coverSubscheme I f hI) (coverSubschemeStructMap I f hI)
FormalScheme.IsRelativelyTopFiniteType R I (coverSubschemeStructHom I f hI)
```

where `coverSubscheme I f hI` is `Spf A` restricted to `D(f₀) ⊔ D(f₁) ⊔ D(f₂)` and the structural
morphism is the inclusion followed by `ambientStructMap I : Spf A ⟶ Spf R`. The presentation has
moved entirely into the *proof*, which is where EGA leaves it.

## Why the presentation drops out, and where it does not

`gluedXIsoCoverSubscheme` is `restrictOpenSchemeIso` at `gluedXToBase`; the two properties then move
along it by `isSeparatedOverSpf_of_iso` and `IsRelativelyTopFiniteType.of_iso`, which already exist.
The only real obligation is the compatibility over the base, and it is exactly
`gluedXToBase_comp_ambientStructMap` (issue 862) composed with the triangle
`restrictOpenIso_hom_comp`. That is why this file is short: every ingredient was delivered by a
previous issue on the chain, and what was missing was the target object.

What does *not* drop out is the hypothesis `hI : I.FG`, which the open subscheme needs twice over —
once for `locallyFG_Spf`, which is what makes the restriction a formal scheme at all, and once
inside the cover. `Spf A` for a non-finitely-generated ideal of definition has no reason to admit
small affine charts (`FormalSchemes.LocallyFG`), so the object here genuinely requires it; this is
not an artefact of the proof.

The two halves read the structural morphism through different wrappers — `IsSeparatedOverSpf` takes
the locally-ringed-space morphism, `IsRelativelyTopFiniteType` its `FormalScheme.Hom.mk` — for the
same reason recorded in `FormalSchemes.ThreeChartCoverTopFiniteType`. They are the same morphism.

## Main definitions and results

* `AlgebraicGeometry.ThreeChartCover.coverOpen`: `D(f₀) ⊔ D(f₁) ⊔ D(f₂)` as an open of `Spf A`.
* `AlgebraicGeometry.ThreeChartCover.coverSubscheme`: the open formal subscheme it cuts out.
* `AlgebraicGeometry.ThreeChartCover.gluedXIsoCoverSubscheme`: `gluedX ≅ coverSubscheme`, over
  `Spf A`.
* `AlgebraicGeometry.ThreeChartCover.coverSubscheme_isSeparatedOverSpf` and
  `coverSubscheme_isRelativelyTopFiniteType`: **the two EGA properties, without a presentation.**

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6, §10.13, §10.15.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum TopologicalSpace

universe u

namespace AlgebraicGeometry

namespace ThreeChartCover

variable {R : Type u} [CommRing R] (I : Ideal R) [TopologicalSpace R] [IsAdicRing I]
variable {A : Type u} [CommRing A] [Algebra R A]
variable (f : ULift.{u} (Fin 3) → A)
variable [TopologicalSpace A] [IsAdicRing (I.map (algebraMap R A))]

/-! ### The open subset and the object it cuts out -/

omit [TopologicalSpace R] [IsAdicRing I] in
/-- `Spf A` is locally finitely generated, which is what makes its open subsets formal schemes.
This is `locallyFG_Spf` at the ideal the charts are built at. -/
theorem ambient_locallyFG (hI : I.FG) :
    (FormalScheme.Spf (I.map (algebraMap R A))).LocallyFG :=
  FormalScheme.locallyFG_Spf (hI.map (algebraMap R A))

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The union of the three basic opens**, as an open subset of `Spf A`. This is the only datum in
the statements below: three elements of `A`. -/
def coverOpen : Opens (FormalScheme.Spf (I.map (algebraMap R A))) :=
  basicOpen (I.map (algebraMap R A)) (f ⟨0⟩) ⊔ basicOpen (I.map (algebraMap R A)) (f ⟨1⟩) ⊔
    basicOpen (I.map (algebraMap R A)) (f ⟨2⟩)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The open formal subscheme `D(f₀) ∪ D(f₁) ∪ D(f₂) ⊆ Spf A`.** No presentation appears: it is
`Spf A` restricted to an open subset, and `Spf A` is `LocallyFG` because `I` is finitely
generated. -/
def coverSubscheme (hI : I.FG) : FormalScheme.{u} :=
  (FormalScheme.Spf (I.map (algebraMap R A))).restrictOpen (ambient_locallyFG I hI)
    (coverOpen I f)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The open subscheme is again locally finitely generated, so the construction can be iterated. -/
theorem coverSubscheme_locallyFG (hI : I.FG) : (coverSubscheme I f hI).LocallyFG :=
  FormalScheme.restrictOpen_locallyFG _ _ _

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The inclusion `D(f₀) ∪ D(f₁) ∪ D(f₂) ↪ Spf A`**, as a morphism of locally ringed spaces. -/
def coverSubschemeι (hI : I.FG) :
    (coverSubscheme I f hI).toLocallyRingedSpace ⟶
      locallyRingedSpaceObj (I.map (algebraMap R A)) :=
  FormalScheme.restrictOpenι (FormalScheme.Spf (I.map (algebraMap R A)))
    (ambient_locallyFG I hI) (coverOpen I f)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The range of the inclusion is `D(f₀) ∪ D(f₁) ∪ D(f₂)`**, which is the sense in which the
object deserves its name. -/
@[simp]
theorem range_coverSubschemeι_base (hI : I.FG) :
    Set.range (coverSubschemeι I f hI).base =
      (coverOpen I f : Set (FormalScheme.Spf (I.map (algebraMap R A)))) :=
  FormalScheme.range_restrictOpenι_base _ _ _

/-- **The structural morphism of the open subscheme over `Spf R`**: include into `Spf A`, then map
down by `ambientStructMap`. -/
def coverSubschemeStructMap (hI : I.FG) :
    (coverSubscheme I f hI).toLocallyRingedSpace ⟶ locallyRingedSpaceObj I :=
  coverSubschemeι I f hI ≫ ambientStructMap I

/-- The structural morphism as a morphism of formal schemes, which is the wrapper
`IsRelativelyTopFiniteType` consumes. -/
def coverSubschemeStructHom (hI : I.FG) :
    coverSubscheme I f hI ⟶ FormalScheme.Spf I :=
  FormalScheme.Hom.mk (coverSubschemeStructMap I f hI)

/-! ### The comparison with the glued cover -/

variable (B : Type u) [CommRing B] [Algebra R B]

/-- **`gluedXToBase` is an open immersion, at the `FormalScheme.Spf` spelling of its target.**

`isOpenImmersion_gluedXToBase` (issue 864) states this with target `locallyRingedSpaceObj (I·A)`,
which is `(FormalScheme.Spf (I·A)).toLocallyRingedSpace` by `rfl` but **not** at the transparency
instance synthesis uses: `FormalScheme.Spf` is a plain `def`. Supplying the theorem as an instance
therefore does not discharge `restrictOpenSchemeIso`'s open-immersion argument, whose type is
spelled through `X.toLocallyRingedSpace`. Restating it once here, at the spelling the consumer
needs, is cheaper than an ascription at each of the three call sites below. -/
theorem isOpenImmersion_gluedXToBase_spf (hI : I.FG) :
    LocallyRingedSpace.IsOpenImmersion
      (show (gluedX I f B hI).toLocallyRingedSpace ⟶
        (FormalScheme.Spf (I.map (algebraMap R A))).toLocallyRingedSpace from
        gluedXToBase I f B hI) :=
  isOpenImmersion_gluedXToBase I f B hI

/-- **`gluedX` is the open formal subscheme `D(f₀) ∪ D(f₁) ∪ D(f₂)` of `Spf A`.** The cover map is
an open immersion (issue 864) with range that union, so `restrictOpenSchemeIso` applies. -/
def gluedXIsoCoverSubscheme (hI : I.FG) : gluedX I f B hI ≅ coverSubscheme I f hI :=
  letI := isOpenImmersion_gluedXToBase_spf I f B hI
  FormalScheme.restrictOpenSchemeIso (FormalScheme.Spf (I.map (algebraMap R A)))
    (ambient_locallyFG I hI) (coverOpen I f) (gluedX I f B hI) (gluedXToBase I f B hI)
    (range_gluedXToBase_base_sup I f B hI)

/-- **The comparison is an isomorphism over `Spf A`**: composed with the inclusion it is the cover
map `gluedXToBase`. -/
@[reassoc]
theorem gluedXIsoCoverSubscheme_hom_comp (hI : I.FG) :
    (gluedXIsoCoverSubscheme I f B hI).hom.toLRSHom ≫ coverSubschemeι I f hI =
      gluedXToBase I f B hI :=
  letI := isOpenImmersion_gluedXToBase_spf I f B hI
  (FormalScheme.restrictOpenSchemeIso_hom_toLRSHom (FormalScheme.Spf (I.map (algebraMap R A)))
    (ambient_locallyFG I hI) (coverOpen I f) (gluedX I f B hI) (gluedXToBase I f B hI)
    (range_gluedXToBase_base_sup I f B hI)) ▸
      FormalScheme.restrictOpenIso_hom_comp (FormalScheme.Spf (I.map (algebraMap R A)))
        (ambient_locallyFG I hI) (coverOpen I f) (gluedXToBase I f B hI)
        (range_gluedXToBase_base_sup I f B hI)

/-- The same triangle for the inverse, which is the direction the transports below consume. -/
@[reassoc]
theorem gluedXIsoCoverSubscheme_inv_comp (hI : I.FG) :
    (gluedXIsoCoverSubscheme I f B hI).inv.toLRSHom ≫ gluedXToBase I f B hI =
      coverSubschemeι I f hI :=
  letI := isOpenImmersion_gluedXToBase_spf I f B hI
  (FormalScheme.restrictOpenSchemeIso_inv_toLRSHom (FormalScheme.Spf (I.map (algebraMap R A)))
    (ambient_locallyFG I hI) (coverOpen I f) (gluedX I f B hI) (gluedXToBase I f B hI)
    (range_gluedXToBase_base_sup I f B hI)) ▸
      FormalScheme.restrictOpenIso_inv_comp (FormalScheme.Spf (I.map (algebraMap R A)))
        (ambient_locallyFG I hI) (coverOpen I f) (gluedXToBase I f B hI)
        (range_gluedXToBase_base_sup I f B hI)

/-- **The comparison is an isomorphism over `Spf R`.** This is the obligation both transports below
consume, and it is `gluedXToBase_comp_ambientStructMap` (issue 862) after the triangle over
`Spf A`. -/
theorem gluedXIsoCoverSubscheme_hom_comp_structMap (hI : I.FG) :
    (gluedXIsoCoverSubscheme I f B hI).hom.toLRSHom ≫ coverSubschemeStructMap I f hI =
      (datumX I f B hI).xStructMap := by
  rw [coverSubschemeStructMap, ← Category.assoc, gluedXIsoCoverSubscheme_hom_comp,
    gluedXToBase_comp_ambientStructMap]

/-- The `FormalScheme`-level form: the comparison identifies the two structural morphisms. -/
theorem gluedXIsoCoverSubscheme_symm_hom_comp_structHom (hI : I.FG) :
    (gluedXIsoCoverSubscheme I f B hI).symm.hom ≫
        FormalScheme.Hom.mk (X := gluedX I f B hI) (Y := FormalScheme.Spf I)
          (datumX I f B hI).xStructMap =
      coverSubschemeStructHom I f hI := by
  refine FormalScheme.forgetToLocallyRingedSpace.map_injective ?_
  change (gluedXIsoCoverSubscheme I f B hI).inv.toLRSHom ≫ (datumX I f B hI).xStructMap =
    coverSubschemeStructMap I f hI
  rw [coverSubschemeStructMap, ← gluedXIsoCoverSubscheme_inv_comp I f B hI, Category.assoc,
    gluedXToBase_comp_ambientStructMap]

/-! ### The two EGA properties, without a presentation

Both are proved by transporting the corresponding statement about `gluedX` along
`gluedXIsoCoverSubscheme`, with the auxiliary base-change algebra taken to be `R` itself.

That choice is free: `B` enters `gluedX I f B hI = (datumX I f B hI).xGlued` only through the
*type* `AffineChartedFibreDatumX R I hI B` of the datum, never through the chart algebras, the
overlaps or the transitions, so every `B` presents the same open subscheme. Instantiating it here
rather than carrying it is what makes these two statements mention no algebra other than `A`. -/

/-- **The open formal subscheme `D(f₀) ∪ D(f₁) ∪ D(f₂)` of `Spf A` is separated over `Spf R`**
(EGA I §10.15).

Compare `gluedX_isSeparatedOverSpf`, which says the same thing about a glued object built from
three chart algebras, a transition system and an auxiliary algebra `B`. Here the statement names
only `A`, `f₀`, `f₁`, `f₂` and `I`; the presentation survives only in the proof. -/
theorem coverSubscheme_isSeparatedOverSpf (hI : I.FG) :
    FormalScheme.IsSeparatedOverSpf hI (coverSubscheme I f hI)
      (coverSubschemeStructMap I f hI) :=
  FormalScheme.isSeparatedOverSpf_of_iso hI
    (FormalScheme.forgetToLocallyRingedSpace.mapIso (gluedXIsoCoverSubscheme I f R hI))
    (gluedXIsoCoverSubscheme_hom_comp_structMap I f R hI)
    (gluedX_isSeparatedOverSpf I f R hI)

/-- **The open formal subscheme `D(f₀) ∪ D(f₁) ∪ D(f₂)` of `Spf A` is topologically of finite type
over `Spf R`** when `A` is (EGA I §10.13), stated with no presentation.

Only this half consumes `hA`; separatedness holds for every `A`. -/
theorem coverSubscheme_isRelativelyTopFiniteType (hI : I.FG) {L : Ideal A}
    (hA : IsTopologicallyFiniteType R I A L) :
    FormalScheme.IsRelativelyTopFiniteType R I (coverSubschemeStructHom I f hI) := by
  rw [← gluedXIsoCoverSubscheme_symm_hom_comp_structHom I f R hI]
  exact (gluedX_isRelativelyTopFiniteType I f R hI hA).of_iso
    (gluedXIsoCoverSubscheme I f R hI).symm

end ThreeChartCover

end AlgebraicGeometry

end
