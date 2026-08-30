import FormalSchemes.RelativeTopFiniteType
import FormalSchemes.TopFiniteTypeTrans

set_option linter.style.header false

/-!
# Composition of topologically-finite-type morphisms over an affine base

`IsTopologicallyFiniteType.trans` (`FormalSchemes.TopFiniteTypeTrans`, issue
1147) composes tf-type *algebras*. It landed without a consumer, and its own delivery note said so:
the declaration that would want it is the composition law for the morphism-level notion, which did
not exist. This file is that law.

## What is proved, and in what generality

`AlgebraicGeometry.FormalScheme.IsRelativelyTopFiniteType R I f` is **base-affine** — `f` runs into
`FormalScheme.Spf I` — so the only composite it can state is

```
X ⟶ Spf L ⟶ Spf I
```

with the second arrow the structural morphism of a tf-type `(R, I)`-algebra `A` with ideal of
definition `L`. `IsRelativelyTopFiniteType.comp_structHom` is exactly that, and it is **everything
the notion admits**, not a special case of a general law being deferred: a composite
`X ⟶ Y ⟶ Z` with `Y` and `Z` arbitrary formal schemes cannot even be *stated* with this predicate.

The bridge that makes it work is that `trans` and composition of structural morphisms agree:
`structHom_trans` says the two structural morphisms compose to the structural morphism of the
transitive tf-type structure. **That identity is also the coherence check**, and it is why no
separate one is stated below — the two routes to `IsRelativelyTopFiniteType R I (structHom hB ≫
structHom hA)` are equal as propositions by proof irrelevance, so the content is entirely in the
morphism identity, and a `Prop`-level restatement would be a duplicate under a new name.

## What is *not* proved, and what blocks it

The general notion at a non-affine target — issue 62's item (1) — is landed, but not here:
`AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHom` (`FormalSchemes.TopFiniteTypeHom`). Of the
two theorems that justify it, only the second is still open:

* **Composition at a non-affine target** is proved, and this bullet no longer names a blocker.
  `AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHom.trans`
  (`FormalSchemes.TopFiniteTypeHomTrans`) is EGA I 10.13's composition law with no hypothesis
  relating the two witnesses. What it needed was one *shared* affine chart of the middle formal
  scheme, and it constructs one at each point: the two witnesses present a neighbourhood of a
  point of `Y` as two unrelated formal spectra, which the proof refines to a common basic open
  before transporting one witness onto the other's ring, up to cofinality of the two ideals of
  definition. It does **not** run through
  `AlgebraicGeometry.FormalScheme.IsRelativelyTopFiniteType.exists_refinement`
  (`FormalSchemes.RelativeTopFiniteTypeBasis`) or through its non-affine analogue
  `AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHom.exists_refinement`
  (`FormalSchemes.TopFiniteTypeHom`) — both of those refine a cover of the *source* while keeping
  the cover of the target fixed, and the shrink the composition law needs is over a refined chart
  of `Y`, which is a chart of neither given cover.
* **Conservativity** at `Y = Spf I` needs an *arbitrary* affine open of `Spf I` to be tf-type over
  `(R, I)`. The adic analogue of the algebra theorem "if `g₁, …, gₙ` generate the unit ideal and
  each localisation `S_{gᵢ}` is of finite type over `R`, then so is `S`" — which this bullet used
  to name as the missing ingredient — is, since issue 1202,
  `AlgebraicGeometry.IsTopologicallyFiniteType.of_span_awayCompletion`
  (`FormalSchemes.TopFiniteTypeAffineLocal`), on top of the basic-open case
  `AlgebraicGeometry.IsTopologicallyFiniteType.awayCompletion`
  (`FormalSchemes.AwayTopFiniteType`). Issue 1207 then assembled the affine-open statement itself,
  `AlgebraicGeometry.IsTopologicallyFiniteType.of_openImmersion_of_isCofinal`
  (`FormalSchemes.AffineOpenTopFiniteType`), including the identification of the two chart
  presentations of a basic open `D(f)` of an affine open `V` — which does hold only up to an
  equivalent ideal of definition, and is `FormalSpectrum.spfAlgEquivOfComm`
  (`FormalSchemes.SpfIsoOverBase`). What is still missing is that hypothesis: that an affine open
  immersion of formal spectra is adic *up to cofinality*.

Conservativity is still open, so nothing here should be read as saying EGA I 10.13 is finished.

## A namespace warning, because it is not a mistake to be fixed

`IsTopologicallyFiniteType` and its API — `IsTopologicallyFiniteType.map_eq`,
`IsTopologicallyFiniteType.structMap`, `IsTopologicallyFiniteType.trans` — live at the **root**,
because `FormalSchemes.TopFiniteType` declares them there.
`AlgebraicGeometry.IsTopologicallyFiniteType.structHom` lives one namespace in, because
`FormalSchemes.RelativeTopFiniteType` declares it inside `AlgebraicGeometry`. The lemmas below
follow their subjects: `IsTopologicallyFiniteType.structMap_comp` is at root and
`AlgebraicGeometry.IsTopologicallyFiniteType.structHom_trans` is not. A
`#check @AlgebraicGeometry.IsTopologicallyFiniteType.structMap` reports the constant as unknown
when it is perfectly present.

## Main results

* `IsTopologicallyFiniteType.structMap_comp`: the structural morphisms of a tower compose to the
  structural morphism of the composite, as locally ringed spaces.
* `AlgebraicGeometry.IsTopologicallyFiniteType.structHom_trans`: the same one level up, for
  `structHom` and `trans`.
* `AlgebraicGeometry.FormalScheme.IsRelativelyTopFiniteType.comp_structHom`: **the headline** —
  EGA I 10.13's composition law in the generality the base-affine notion admits.
* `AlgebraicGeometry.FormalScheme.IsAffineTopFiniteType.trans`,
  `AlgebraicGeometry.FormalScheme.IsLocallyTopFiniteType.trans`: the object-level companions.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.13.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
-/

noncomputable section

open CategoryTheory

universe u

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {A : Type u} [CommRing A] [Algebra R A] {L : Ideal A}
variable {B : Type u} [CommRing B] [Algebra A B] {M : Ideal B}
variable [Algebra R B] [IsScalarTower R A B]

section StructMap

variable [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace A] [IsAdicRing L]
variable [TopologicalSpace B] [IsAdicRing M]

/-- **The structural morphisms of a tower compose.** `Spf M ⟶ Spf L ⟶ Spf I` is the structural
morphism `Spf M ⟶ Spf I` of the composite algebra structure, because all three are
`FormalSpectrum.locallyRingedSpaceMap` of the respective `algebraMap`s and
`algebraMap R B = (algebraMap A B).comp (algebraMap R A)` in a scalar tower. No finiteness is
involved: this is the functor law of `Spf` (issue 60) read off at algebra maps. -/
theorem IsTopologicallyFiniteType.structMap_comp (h₁ : Ideal.map (algebraMap R A) I = L)
    (h₂ : Ideal.map (algebraMap A B) L = M) (h₃ : Ideal.map (algebraMap R B) I = M) :
    IsTopologicallyFiniteType.structMap h₂ ≫ IsTopologicallyFiniteType.structMap h₁ =
      IsTopologicallyFiniteType.structMap h₃ := by
  unfold IsTopologicallyFiniteType.structMap
  rw [FormalSpectrum.locallyRingedSpaceMap_congr I M (algebraMap R B)
      ((algebraMap A B).comp (algebraMap R A)) _
      (by rw [← IsScalarTower.algebraMap_eq]; exact Ideal.map_le_iff_le_comap.mp h₃.le)
      (IsScalarTower.algebraMap_eq R A B),
    FormalSpectrum.locallyRingedSpaceMap_comp I L M (algebraMap R A) (algebraMap A B)]

namespace AlgebraicGeometry

/-- **`trans` and composition of structural morphisms agree.** The tf-type structure that
`IsTopologicallyFiniteType.trans` produces on `B` over `(R, I)` has as its
structural morphism the composite of the two given ones.

This is a `congrArg` and not a functoriality argument because `FormalScheme`'s category structure
is literally `comp f g := Hom.mk (f.toLRSHom ≫ g.toLRSHom)` (`FormalSchemes.FormalScheme`), so the
statement *is* `structMap_comp` under `AlgebraicGeometry.FormalScheme.Hom.mk`.

It is also the coherence check for `IsRelativelyTopFiniteType.comp_structHom` below: applied to
`IsTopologicallyFiniteType.isRelativelyTopFiniteType`, that theorem lands on
`structHom hB ≫ structHom hA`, and this identity is what says the object it lands on is the one
the affine theory already had. -/
theorem IsTopologicallyFiniteType.structHom_trans (hI : I.FG)
    (hA : IsTopologicallyFiniteType R I A L) (hB : IsTopologicallyFiniteType A L B M) :
    IsTopologicallyFiniteType.structHom hB ≫ IsTopologicallyFiniteType.structHom hA =
      IsTopologicallyFiniteType.structHom (hA.trans hI hB) :=
  congrArg FormalScheme.Hom.mk
    (IsTopologicallyFiniteType.structMap_comp hA.map_eq hB.map_eq (hA.trans hI hB).map_eq)

end AlgebraicGeometry

end StructMap

namespace AlgebraicGeometry.FormalScheme

/-! ### The composition law -/

section Relative

variable [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace A] [IsAdicRing L]

/-- **EGA I 10.13, composition, in the generality a base-affine notion admits.** If `f : X ⟶ Spf L`
is topologically of finite type over `(A, L)` and `A` is a tf-type `(R, I)`-algebra, then
`f` followed by the structural morphism `Spf L ⟶ Spf I` is topologically of finite type over
`(R, I)`.

**The cover is not refined**: the very cover witnessing `f` witnesses the composite, with each
piece's identification `𝒰.obj j ≅ Spf M` carried over unchanged and only the tf-type witness
replaced by `IsTopologicallyFiniteType.trans`. That is the whole reason the affine-target case is
cheap while the general one is not.

The one step that is not bookkeeping: `IsRelativelyTopFiniteType` supplies an `Algebra A B` and
nothing tying `B` to `R`, while `trans` needs `[Algebra R B]` and `[IsScalarTower R A B]`. Those
are *constructed* from the composite ring map — legitimately, since the conclusion's own
existential is what they are supplied to — so an attempt that reaches for `inferInstance` here
fails, and the failure reads like a missing hypothesis rather than a missing construction. -/
theorem IsRelativelyTopFiniteType.comp_structHom (hI : I.FG)
    (hA : IsTopologicallyFiniteType R I A L) {X : FormalScheme.{u}}
    {f : X ⟶ FormalScheme.Spf L} (hf : IsRelativelyTopFiniteType A L f) :
    IsRelativelyTopFiniteType R I (f ≫ IsTopologicallyFiniteType.structHom hA) := by
  obtain ⟨𝒰, h𝒰⟩ := hf
  refine ⟨𝒰, fun j => ?_⟩
  obtain ⟨B', _, _, _, M', _, hB, e, hcomp⟩ := h𝒰 j
  letI : Algebra R B' := ((algebraMap A B').comp (algebraMap R A)).toAlgebra
  haveI : IsScalarTower R A B' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  refine ⟨B', inferInstance, inferInstance, inferInstance, M', inferInstance,
    hA.trans hI hB, e, ?_⟩
  rw [← Category.assoc, hcomp, Category.assoc,
    IsTopologicallyFiniteType.structHom_trans hI hA hB]

end Relative

/-! ### The object-level companions

No topology is needed here: `IsAffineTopFiniteType` and `IsLocallyTopFiniteType` are stated for a
bare `CommRing` base, and only the morphism-level notion needs `Spf` to exist. -/

/-- **An affine tf-type formal scheme over a tf-type base is affine tf-type over the deeper
base.** The identification `Y ≅ Spf M` is reused; only the algebra structure on `M`'s ring is
rebuilt and its tf-type witness replaced by `IsTopologicallyFiniteType.trans`. -/
theorem IsAffineTopFiniteType.trans (hI : I.FG) (hA : IsTopologicallyFiniteType R I A L)
    {Y : FormalScheme.{u}} (hY : IsAffineTopFiniteType A L Y) :
    IsAffineTopFiniteType R I Y := by
  obtain ⟨B', _, _, _, M', _, hB, ⟨e⟩⟩ := hY
  letI : Algebra R B' := ((algebraMap A B').comp (algebraMap R A)).toAlgebra
  haveI : IsScalarTower R A B' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ⟨B', inferInstance, inferInstance, inferInstance, M', inferInstance,
    hA.trans hI hB, ⟨e⟩⟩

/-- **Locally tf-type is transitive.** The cover is unchanged; every piece is upgraded by
`IsAffineTopFiniteType.trans`. -/
theorem IsLocallyTopFiniteType.trans (hI : I.FG) (hA : IsTopologicallyFiniteType R I A L)
    {X : FormalScheme.{u}} (hX : IsLocallyTopFiniteType A L X) :
    IsLocallyTopFiniteType R I X := by
  obtain ⟨𝒰, h𝒰⟩ := hX
  exact ⟨𝒰, fun j => (h𝒰 j).trans hI hA⟩

end AlgebraicGeometry.FormalScheme
