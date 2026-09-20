import FormalSchemes.GeneralSeparatedBaseChange
import FormalSchemes.GeneralSeparatedScheme
import FormalSchemes.AwayBaseChangeGluedX

set_option linter.style.header false

/-!
# Separatedness over `Spf R` descends to a basic open of the base (EGA I §10.15)

`AlgebraicGeometry.FormalScheme.IsSeparatedOverSpf` is existential over a presentation, so it
transports along an isomorphism for free and changes its base ring only at a price: an isomorphism
carries the witnessing `AlgebraicGeometry.AffineChartedFibreDatumX` across unchanged, and the
moment the base ring moves that datum has to be rebuilt. Until this file, every declaration on this
tree that moved an `AlgebraicGeometry.FormalScheme.IsSeparatedOverSpf` moved it along an
isomorphism **over the same base**, and
`AlgebraicGeometry.FormalScheme.chart_clause_of_nested` — whose conclusion does existentially
quantify a fresh base — supplies the very `R`, `I` it was handed.

**This file is the first statement that changes the base**, at `R' = R{1/f}`, `I' = I·R{1/f}`: the
case a refinement of a presentation actually produces, since shrinking `Spf R` to a basic open
replaces the base by the completed localization.

## The statement, and what a caller owes

The input is an `(R, I)`-presentation in the smart-constructor vocabulary — a chart family `A`,
an away family `g`, transitions `τ` and `σ` with their three identities — together with the two
things the away base itself asks for: that `f` is a unit in every chart, and that the
`R{1/f}`-algebra structure each chart carries is the universal one,
`FormalSpectrum.awayCompletionLift`. **Nothing primed is asked for**: the primed transitions, their
three identities, their two `HEq`s and the primed adicity are all produced by
`FormalSchemes.AwayBaseChangeGluedX`.

**None of that is asked of the caller of the presentation-free form.**
`AlgebraicGeometry.FormalScheme.isSeparatedOverSpf_awayBase_of_factorsThrough` takes separatedness
over `Spf R` and a factorisation of the structural morphism through `Spf R{1/f}`, and derives the
presentation, the unit and the algebra structure from them — the presentation from
`AlgebraicGeometry.AffineChartedFibreDatumX.eq_ofAlgebraData`, the other two from the
factorisation, chart by chart. What it gives up in exchange is named in
*What is not proved here*.

## The argument, in three steps

1. **Down to the datum.** `AlgebraicGeometry.FormalScheme.isSeparatedOverSpf_iff` turns the
   existential hypothesis into separatedness of *this* presentation, because every presentation of
   `X` over `s` computes the predicate. At the glued object of the datum itself the witnessing
   isomorphism is `CategoryTheory.Iso.refl` and the base compatibility is
   `CategoryTheory.Category.id_comp`.

2. **Across the base.**
   `AlgebraicGeometry.BothChartedFibreDatumXY.isSeparated_of_isSeparated_baseChange`
   (`FormalSchemes.GeneralSeparatedBaseChange`) descends separatedness of the datum along the
   glued base change. It asks for `I' = I·R'`, the agreement of the induced ideal families, and
   the agreement of the two transition families *as functions* — and **nothing about the glue**,
   which is what issues 2068, 2074 and 2086 removed from it. Here all four inputs are theorems:
   `I' = I·R'` holds by `rfl` at this base, the ideal families agree by
   `Ideal.map_algebraMap_family_eq_of_tower`, and the two `HEq`s are
   `AlgebraicGeometry.AffineChartedFibreDatumX.awayBaseTransition_coe_heq` and
   `AlgebraicGeometry.AffineChartedFibreDatumX.awayBaseOverlap_coe_heq`, which hold because the
   primed data are built from the unprimed data by transports that leave the underlying function
   alone.

3. **Back up to the scheme.**
   `AlgebraicGeometry.FormalScheme.isSeparatedOverSpf_of_isSeparated` re-enters the existential at
   the primed datum's own glued object and structural morphism.

**The space does not move.**
`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_eq_awayBase'` is an *equality* of
formal schemes, not an isomorphism, so the conclusion can be read back at the unprimed glued
object; only the structural morphism changes, and it changes to a morphism to `Spf R{1/f}`. That
is `AlgebraicGeometry.AffineChartedFibreDatumX.isSeparatedOverSpf_awayBase_xGlued`, and the
`CategoryTheory.eqToHom` in its statement is the transport along that equality and nothing else.

## Why `R{1/f}` and not a general `(R', I')`

Because at a general `(R', I')` the statement is **refuted**, not open. The induced ideal families
need not agree — `FormalSpectrum.cofinalSpfIso` (`FormalSchemes.CofinalSheafComparisonIso`)
presents one adic ring at two ideals of definition at once — and
`FormalSchemes.AdicOnSections` records the refutation of the general adicity statement it rests on
(issue 460). `Ideal.IsCofinal` is what survives there and the transports it would need are not
built; `FormalSchemes.AwayBaseChangeGluedX`'s own *Why `I' = I·R'` and not an arbitrary
`(R', I')`* section is the longer version of this paragraph, reached independently from the
chart side.

Within `I' = I·R'` the away base is the further restriction, and it is the one this file takes
because the primed transition data are only constructed there: enlarging an `R`-algebra
equivalence of chart rings to an `R{1/f}`-algebra equivalence is rigidity of the away completion
as a source (`FormalSpectrum.awayCompletion_hom_ext'`), which is a statement about `R{1/f}` and
about no other `R'`.

## What is not proved here

**The refinement direction of §10.15 is still open**, and so are the composition law and the hard
direction of conservativity. `FormalSchemes/GeneralSeparatedHomLocal.lean` names what the
refinement direction requires — that `AlgebraicGeometry.FormalScheme.IsSeparatedOverSpf` restrict
to an open subscheme *over an open of the affine base* — and this file supplies that only when the
open of the base is a **basic** open. Getting from an arbitrary open subscheme of an arbitrary
formal scheme to that shape is the residue, and it is not done here.

**The structural morphism of the presentation-free statement is existentially quantified.**
`AlgebraicGeometry.FormalScheme.isSeparatedOverSpf_awayBase_of_factorsThrough` produces *some*
morphism into `Spf R{1/f}` over which the source is separated, and it is the one the away-base
presentation carries. That it is the factorisation the caller supplied holds chart by chart —
`AlgebraicGeometry.AffineChartedFibreDatumX.ι_comp_eq_of_factorsThrough` — and the two morphisms
are then compared across glue data whose pieces agree only along the transport
`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_eq_awayBase'`. Carrying that
transport down to the glue inclusions is what remains, and it is not done here. The uniqueness
statement `AlgebraicGeometry.AffineChartedFibreDatumX.factorsThrough_awayBase_unique` says that
whichever morphism the comparison eventually names, there is no choice about it.

`FormalSchemes.GeneralSeparatedHom`'s not-proved list is therefore left exactly as it stands.
`FormalSchemes.GeneralSeparatedHomLocal`'s said that the required statement *is nowhere on the
tree*; that clause is the one sentence this module falsifies, and it is repaired there to name
this module and to say in the same breath that the arbitrary open it needs is still missing.
**No list is weakened and no direction is claimed.**

**No datum is constructed and no presentation is produced.** The `(R, I)`-presentation is an input
on every statement below; nothing here says that a formal scheme admits one, and
`AlgebraicGeometry.FormalScheme.IsSeparatedOverSpf` is false — not merely unproved — for a formal
scheme that does not.

**The converse is not proved.** Separatedness over `Spf R{1/f}` does not obviously give
separatedness over `Spf R`, and nothing below is an `Iff`.

## Placement

A leaf over `FormalSchemes.GeneralSeparatedBaseChange`, `FormalSchemes.GeneralSeparatedScheme` and
`FormalSchemes.AwayBaseChangeGluedX`: forward closure **201**, reverse closure **0**.

The three parents are pairwise import-incomparable — `FormalSchemes.GeneralSeparatedBaseChange`
has forward closure **185**, `FormalSchemes.GeneralSeparatedScheme` **178** and
`FormalSchemes.AwayBaseChangeGluedX` **93**, and no one of the three is in another's closure — so
the statement costs either two import edges or a module of its own. The edges were rejected:
`FormalSchemes.GeneralSeparatedBaseChange` was itself a leaf until this module, and an edge into
`FormalSchemes.GeneralSeparatedScheme` would put the whole `FormalSchemes.AwayBaseChangeGluedX`
subtree into the environment of every consumer of `FormalSchemes.GeneralSeparatedScheme`.
`FormalSchemes.GeneralSeparatedScheme`'s reverse closure is **13**, and none of the twelve besides
this module is about a change of base.

A leaf leaves all three subjects alone and moves no forward closure anywhere, at the price of the
reverse closure of every module it imports moving by one.

The two sections added below for the basic-open factorisation are here for the same reason read
the other way round. `FormalSpectrum.globalSectionsMap`, `FormalSpectrum.awayCompletionLift`,
`FormalSpectrum.awayCompletion_hom_ext'` and
`AlgebraicGeometry.AffineChartedFibreDatumX.xStructMap` are all imported, transitively, by this
module already, so stating them here adds no import edge and moves no import figure anywhere on
the tree; stating each beside its own subject would add an edge into a module whose dependents
would all be rebuilt.

## Main results

* `AlgebraicGeometry.AffineChartedFibreDatumX.isSeparatedOverSpf_awayBase`: separatedness of a
  smart-constructor presentation over `Spf R` gives separatedness of the away-base presentation
  over `Spf R{1/f}`.
* `AlgebraicGeometry.AffineChartedFibreDatumX.isSeparatedOverSpf_awayBase_xGlued`: the same
  conclusion read at the **unprimed** glued object, which
  `AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_eq_awayBase'` says is the same
  formal scheme.
* `AlgebraicGeometry.AffineChartedFibreDatumX.isSeparatedOverSpf_awayBase_of_presentation`: the
  same statement about an arbitrary formal scheme presented by that datum, on both sides.
* `FormalSpectrum.isUnit_algebraMap_of_factorsThrough`: a chart whose structural morphism factors
  through the basic open of the base has the localising element inverted.
* `FormalSpectrum.globalSectionsMap_eq_awayCompletionLift` and
  `FormalSpectrum.eq_locallyRingedSpaceMap_awayCompletionLift`: that factorisation is `Spf` of
  `FormalSpectrum.awayCompletionLift`, both as a ring map and as a morphism of formal spectra.
* `AlgebraicGeometry.AffineChartedFibreDatumX.factorsThrough_awayBase_unique`: a structural
  morphism factors through the basic open of its base in at most one way.
* `AlgebraicGeometry.FormalScheme.isSeparatedOverSpf_exists_ofAlgebraData`: a caller holding an
  `AlgebraicGeometry.FormalScheme.IsSeparatedOverSpf` holds a smart-constructor presentation.
* `AlgebraicGeometry.FormalScheme.isSeparatedOverSpf_awayBase_of_factorsThrough`: **the
  presentation-free form** — separatedness over `Spf R` plus a factorisation of the structural
  morphism through `Spf R{1/f}` gives separatedness over `Spf R{1/f}`, with no presentation in the
  statement and neither of the two chart hypotheses above it asked of the caller.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.12, §10.15.
* [The Stacks Project, Tag 01KJ](https://stacks.math.columbia.edu/tag/01KJ).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum Topology
open CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace FormalSpectrum

/-!
### A factorisation through the basic open of the base, and what it forces

`AlgebraicGeometry.AffineChartedFibreDatumX.isSeparatedOverSpf_awayBase` asks its caller for two
things about the chart family: that `f` be a unit in every chart, and that the `R{1/f}`-algebra
structure each chart carries be `FormalSpectrum.awayCompletionLift`. **Neither is extra data.** A
morphism `Spf A ⟶ Spf R{1/f}` over `Spf R` forces both, and this section is the proof.

Taking global sections turns such a morphism into a ring map `R{1/f} →+* A` under `R`
(`FormalSpectrum.globalSectionsMap`, whose definition takes no continuity hypothesis — that is the
*other* direction, `FormalSpectrum.locallyRingedSpaceMap`, and the warning attached to it does not
bite here). Since `f` is a unit of `R{1/f}`, its image is a unit of `A`; and rigidity of the away
completion as a source (`FormalSpectrum.awayCompletion_hom_ext'`) identifies the recovered ring map
with the lift. The round trip `FormalSpectrum.locallyRingedSpaceMap_globalSectionsMap` then turns
that identification back into one of morphisms of formal spectra, which says that the factorisation
is **unique** and is `Spf` of the lift.

Everything here is about a single chart. It is stated in this file rather than beside the rest of
the `FormalSpectrum.awayCompletion` API for the reason
`FormalSpectrum.isUnit_algebraMap_awayCompletionBase` gives for itself: the modules that own those
names are deep in the import graph, the move down rebuilds all of their dependents, and this tree's
disposition is to pay that once a second module asks for the statement and not before.
-/

section AwayBaseFactorisation

variable {R : Type u} [CommRing R] (I : Ideal R) (f : R)
variable [TopologicalSpace R] [IsAdicRing I]
variable {A : Type u} [CommRing A] [Algebra R A] [TopologicalSpace A]
variable [isAdicA : IsAdicRing (I.map (algebraMap R A))]
variable [IsAdicRing (I.map (algebraMap R (awayCompletion I f)))]

/-- **The basic open `Spf R{1/f} ⟶ Spf R` of the base**, the map of formal spectra induced by the
structural map of the away completion.

`FormalSpectrum.basicOpenChart` is the same `FormalSpectrum.locallyRingedSpaceMap` at the
`FormalSpectrum.awayCompletionIdeal` spelling of the ideal of definition and the
`FormalSpectrum.awayCompletionHom` spelling of the ring map. This file, like
`FormalSchemes.AwayBaseChangeGluedX`, states everything at `I.map (algebraMap R (awayCompletion I
f))`, because that is the ideal
`AlgebraicGeometry.AffineChartedFibreDatumX.isSeparatedOverSpf_awayBase` draws its conclusion at;
naming the morphism here keeps a transport out of every statement below. -/
abbrev awayBaseChart : locallyRingedSpaceObj (I.map (algebraMap R (awayCompletion I f))) ⟶
    locallyRingedSpaceObj I :=
  locallyRingedSpaceMap I (I.map (algebraMap R (awayCompletion I f)))
    (algebraMap R (awayCompletion I f)) Ideal.le_comap_map

/-- **Global sections of a factorisation through the basic open is a map under the base.** For a
morphism `Spf A ⟶ Spf R{1/f}` whose composite with `FormalSpectrum.awayBaseChart` is the structural
morphism of `Spf A`, the recovered ring map `R{1/f} →+* A` composed with `R → R{1/f}` is `R → A`.

Both identifications are `FormalSpectrum.globalSectionsMap_locallyRingedSpaceMap`, applied on the
two sides of the image of the hypothesis under
`FormalSpectrum.globalSectionsMap_comp`. -/
theorem comp_globalSectionsMap_of_factorsThrough
    (u : locallyRingedSpaceObj (I.map (algebraMap R A)) ⟶
      locallyRingedSpaceObj (I.map (algebraMap R (awayCompletion I f))))
    (hu : u ≫ awayBaseChart I f =
      locallyRingedSpaceMap I (I.map (algebraMap R A)) (algebraMap R A) Ideal.le_comap_map) :
    (globalSectionsMap (I.map (algebraMap R (awayCompletion I f))) (I.map (algebraMap R A)) u).comp
      (algebraMap R (awayCompletion I f)) = algebraMap R A := by
  have h2 := congrArg (globalSectionsMap I (I.map (algebraMap R A))) hu
  rwa [globalSectionsMap_comp, awayBaseChart, globalSectionsMap_locallyRingedSpaceMap,
    globalSectionsMap_locallyRingedSpaceMap] at h2

/-- **A chart over the basic open has the localising element inverted.** If the structural morphism
of `Spf A` factors through `FormalSpectrum.awayBaseChart`, then `f` is a unit in `A`.

`f` is a unit of `R{1/f}` by `FormalSpectrum.isUnit_awayCompletionHom_of_basicOpen_le` at `g = f`,
where the hypothesis is `le_rfl`; a ring homomorphism carries units forward; and
`FormalSpectrum.comp_globalSectionsMap_of_factorsThrough` says which element of `A` the image is.

**This is the hypothesis `hf` of
`AlgebraicGeometry.AffineChartedFibreDatumX.isSeparatedOverSpf_awayBase`,** and it is the reason
that hypothesis is not a restriction on the theorem's reach. -/
theorem isUnit_algebraMap_of_factorsThrough (hI : I.FG)
    (u : locallyRingedSpaceObj (I.map (algebraMap R A)) ⟶
      locallyRingedSpaceObj (I.map (algebraMap R (awayCompletion I f))))
    (hu : u ≫ awayBaseChart I f =
      locallyRingedSpaceMap I (I.map (algebraMap R A)) (algebraMap R A) Ideal.le_comap_map) :
    IsUnit (algebraMap R A f) := by
  have hu' : IsUnit (algebraMap R (awayCompletion I f) f) := by
    rw [← awayCompletionHom_eq_algebraMap]
    exact isUnit_awayCompletionHom_of_basicOpen_le I f f hI le_rfl
  have hmap := hu'.map (globalSectionsMap (I.map (algebraMap R (awayCompletion I f)))
    (I.map (algebraMap R A)) u)
  rwa [← RingHom.comp_apply, comp_globalSectionsMap_of_factorsThrough I f u hu] at hmap

omit [TopologicalSpace R] [IsAdicRing I]
  [IsAdicRing (I.map (algebraMap R (awayCompletion I f)))] in
/-- **The lift is continuous for the two ideals of definition**, which is what
`FormalSpectrum.locallyRingedSpaceMap` asks of it. The extension of `I·R{1/f}` along the lift is
the extension of `I` along `R → R{1/f} → A`, and that composite is `R → A`
(`FormalSpectrum.awayCompletionLift_comp_awayCompletionHom`). -/
theorem le_comap_awayCompletionLift (hfu : IsUnit (algebraMap R A f)) :
    letI := isAdicA.toIsAdicComplete
    I.map (algebraMap R (awayCompletion I f)) ≤
      (I.map (algebraMap R A)).comap (awayCompletionLift I f hfu) := by
  letI := isAdicA.toIsAdicComplete
  rw [← Ideal.map_le_iff_le_comap, Ideal.map_map, ← awayCompletionHom_eq_algebraMap,
    awayCompletionLift_comp_awayCompletionHom]

/-- **The recovered ring map is the lift the universal property produces.** Rigidity of `R{1/f}` as
a source (`FormalSpectrum.awayCompletion_hom_ext'`) compares the two maps `R{1/f} →+* A`: both are
continuous for the ideals of definition, and both restrict to `R → A` over the base.

**This is the hypothesis `halg` of
`AlgebraicGeometry.AffineChartedFibreDatumX.isSeparatedOverSpf_awayBase`** for the algebra
structure `RingHom.toAlgebra` of the lift — at which that hypothesis is `rfl` — and it says that
no *other*
`R{1/f}`-algebra structure compatible with the geometry is available. -/
theorem globalSectionsMap_eq_awayCompletionLift (hI : I.FG)
    (u : locallyRingedSpaceObj (I.map (algebraMap R A)) ⟶
      locallyRingedSpaceObj (I.map (algebraMap R (awayCompletion I f))))
    (hu : u ≫ awayBaseChart I f =
      locallyRingedSpaceMap I (I.map (algebraMap R A)) (algebraMap R A) Ideal.le_comap_map)
    (hfu : IsUnit (algebraMap R A f)) :
    letI := isAdicA.toIsAdicComplete
    globalSectionsMap (I.map (algebraMap R (awayCompletion I f))) (I.map (algebraMap R A)) u =
      awayCompletionLift I f hfu := by
  letI := isAdicA.toIsAdicComplete
  have hsq : (globalSectionsMap (I.map (algebraMap R (awayCompletion I f)))
      (I.map (algebraMap R A)) u).comp (awayCompletionHom I f) = algebraMap R A := by
    rw [awayCompletionHom_eq_algebraMap]
    exact comp_globalSectionsMap_of_factorsThrough I f u hu
  refine awayCompletion_hom_ext' (L := I.map (algebraMap R A)) I f hI ?_ ?_ ?_
  · rw [← Ideal.map_le_iff_le_comap, ← map_awayCompletionHom I f, Ideal.map_map, hsq]
  · rw [← Ideal.map_le_iff_le_comap, ← map_awayCompletionHom I f, Ideal.map_map,
      awayCompletionLift_comp_awayCompletionHom]
  · rw [hsq, awayCompletionLift_comp_awayCompletionHom]

/-- **A factorisation through the basic open of the base is `Spf` of the lift, and there is only
one.** The ring-level identification
`FormalSpectrum.globalSectionsMap_eq_awayCompletionLift` becomes an identification of morphisms of
formal spectra through the round trip `FormalSpectrum.locallyRingedSpaceMap_globalSectionsMap`,
whose continuity hypothesis is `FormalSpectrum.le_comap_awayCompletionLift` transported along that
identification.

Since the right-hand side mentions the factorisation only through a proof of a proposition, two
factorisations of the same structural morphism are equal. -/
theorem eq_locallyRingedSpaceMap_awayCompletionLift (hI : I.FG)
    (u : locallyRingedSpaceObj (I.map (algebraMap R A)) ⟶
      locallyRingedSpaceObj (I.map (algebraMap R (awayCompletion I f))))
    (hu : u ≫ awayBaseChart I f =
      locallyRingedSpaceMap I (I.map (algebraMap R A)) (algebraMap R A) Ideal.le_comap_map)
    (hfu : IsUnit (algebraMap R A f)) :
    letI := isAdicA.toIsAdicComplete
    u = locallyRingedSpaceMap (I.map (algebraMap R (awayCompletion I f)))
      (I.map (algebraMap R A)) (awayCompletionLift I f hfu)
      (le_comap_awayCompletionLift I f hfu) := by
  letI := isAdicA.toIsAdicComplete
  have key := globalSectionsMap_eq_awayCompletionLift I f hI u hu hfu
  refine Eq.symm (Eq.trans ?_ (locallyRingedSpaceMap_globalSectionsMap
    (I.map (algebraMap R (awayCompletion I f))) (I.map (algebraMap R A)) (hI.map _) (hI.map _) u
    (key ▸ le_comap_awayCompletionLift I f hfu)))
  exact locallyRingedSpaceMap_congr _ _ _ _ _ _ key.symm

end AwayBaseFactorisation

end FormalSpectrum

namespace AlgebraicGeometry

namespace AffineChartedFibreDatumX

variable {R : Type u} [CommRing R] {I : Ideal R} (hI : I.FG) (f : R)
variable [TopologicalSpace R] [IsAdicRing I]
variable {B : Type u} [CommRing B] [Algebra R B]
variable {B' : Type u} [CommRing B'] [Algebra (awayCompletion I f) B']
variable {J : Type u} (A : J → Type u) [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
variable [topology : ∀ i : J, TopologicalSpace (A i)]
variable [isAdicA : ∀ i : J, IsAdicRing (I.map (algebraMap R (A i)))]
variable (hf : ∀ i, IsUnit (algebraMap R (A i) f))
variable [∀ i, Algebra (awayCompletion I f) (A i)]
variable (g : ∀ (i : J), J → A i)
variable
  (halg : ∀ i, letI := (isAdicA i).toIsAdicComplete
    algebraMap (awayCompletion I f) (A i) = awayCompletionLift I f (hf i))
  (τ : ∀ (i j : J), i ≠ j →
    (awayCompletion (I.map (algebraMap R (A i))) (g i j) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (A j))) (g j i)))
  (τ_symm : ∀ (i j : J) (h : i ≠ j), τ j i h.symm = (τ i j h).symm)
  (σ : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
    (awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (A j))) (g j k * g j i)))
  (hστ : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
    (σ i j k hij hik hjk).symm.toAlgHom.comp (furtherLocSnd I (g j k) (g j i) hI) =
      (furtherLocFst I (g i j) (g i k) hI).comp (τ i j hij).symm.toAlgHom)
  (hσc : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
    (σ i j k hij hik hjk).trans ((σ j k i hjk hij.symm hik.symm).trans
      (σ k i j hik.symm hjk.symm hij)) =
      AlgEquiv.refl (R := R)
        (A₁ := awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k)))

/-- **Separatedness over `Spf R` descends to the basic open `Spf R{1/f}` of the base.** The
presentation over `(R, I)` is the caller's; the presentation over `(R{1/f}, I·R{1/f})` is the one
`FormalSchemes.AwayBaseChangeGluedX` builds from it, and **the caller supplies nothing primed at
all** — not the transitions, not their identities, not the adicity of the primed chart ideals.

The proof is the three steps of this file's header: down to the datum by
`AlgebraicGeometry.FormalScheme.isSeparatedOverSpf_iff` at the identity isomorphism, across the
base by `AlgebraicGeometry.BothChartedFibreDatumXY.isSeparated_of_isSeparated_baseChange`, and
back up by `AlgebraicGeometry.FormalScheme.isSeparatedOverSpf_of_isSeparated`. Every input of the
middle step is discharged here: `rfl` for `I' = I·R'`,
`Ideal.map_algebraMap_family_eq_of_tower` for the ideal families, and
`AlgebraicGeometry.AffineChartedFibreDatumX.awayBaseTransition_coe_heq` together with
`AlgebraicGeometry.AffineChartedFibreDatumX.awayBaseOverlap_coe_heq` for the transitions.

*Reach for* `AlgebraicGeometry.AffineChartedFibreDatumX.isSeparatedOverSpf_awayBase_xGlued`
*instead* if what you want is the statement about the formal scheme you started with: the two
glued objects are **equal**, and that one says so. -/
theorem isSeparatedOverSpf_awayBase
    (hsep : FormalScheme.IsSeparatedOverSpf hI
      (ofAlgebraData (B := B) hI A g τ τ_symm σ hστ hσc).xGlued
      (ofAlgebraData (B := B) hI A g τ τ_symm σ hστ hσc).xStructMap) :
    letI tower := isScalarTower_of_algebraMap_eq_awayCompletionLift f A hf halg
    letI : ∀ i, IsAdicRing ((I.map (algebraMap R (awayCompletion I f))).map
        (algebraMap (awayCompletion I f) (A i))) :=
      isAdicRing_awayBaseChartIdeal f A hf halg
    haveI : IsAdicRing (I.map (algebraMap R (awayCompletion I f))) :=
      map_awayCompletionHom I f ▸ isAdicRing_awayCompletionIdeal I f hI
    FormalScheme.IsSeparatedOverSpf (hI.map (algebraMap R (awayCompletion I f)))
      (ofAlgebraData (B := B') (hI.map (algebraMap R (awayCompletion I f))) A g
        (awayBaseTransition hI f A tower g τ)
        (awayBaseTransition_symm hI f A tower g τ τ_symm)
        (awayBaseOverlap hI f A tower g σ)
        (awayBaseOverlap_transition hI f A tower g τ σ hστ)
        (awayBaseOverlap_cocycle hI f A tower g σ hσc)).xGlued
      (ofAlgebraData (B := B') (hI.map (algebraMap R (awayCompletion I f))) A g
        (awayBaseTransition hI f A tower g τ)
        (awayBaseTransition_symm hI f A tower g τ τ_symm)
        (awayBaseOverlap hI f A tower g σ)
        (awayBaseOverlap_transition hI f A tower g τ σ hστ)
        (awayBaseOverlap_cocycle hI f A tower g σ hσc)).xStructMap := by
  letI tower := isScalarTower_of_algebraMap_eq_awayCompletionLift f A hf halg
  letI : ∀ i, IsAdicRing ((I.map (algebraMap R (awayCompletion I f))).map
      (algebraMap (awayCompletion I f) (A i))) :=
    isAdicRing_awayBaseChartIdeal f A hf halg
  haveI : IsAdicRing (I.map (algebraMap R (awayCompletion I f))) :=
    map_awayCompletionHom I f ▸ isAdicRing_awayCompletionIdeal I f hI
  have key := BothChartedFibreDatumXY.isSeparated_of_isSeparated_baseChange hI
    (hI.map (algebraMap R (awayCompletion I f))) A g τ τ_symm σ hστ hσc
    (awayBaseTransition hI f A tower g τ)
    (awayBaseTransition_symm hI f A tower g τ τ_symm)
    (awayBaseOverlap hI f A tower g σ)
    (awayBaseOverlap_transition hI f A tower g τ σ hστ)
    (awayBaseOverlap_cocycle hI f A tower g σ hσc)
    (BX := B) (BX' := B')
    rfl (Ideal.map_algebraMap_family_eq_of_tower A I)
    (fun i j h => awayBaseTransition_coe_heq hI f A tower g τ i j h)
    (fun i j k hij hik hjk => awayBaseOverlap_coe_heq hI f A tower g σ i j k hij hik hjk)
    ((FormalScheme.isSeparatedOverSpf_iff hI _ _ _ _ (Iso.refl _) (Category.id_comp _)).mp hsep)
  exact FormalScheme.isSeparatedOverSpf_of_isSeparated _ _ _ _ _ key

/-- **The formal scheme does not move; only its structural morphism does.**
`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData_xGlued_eq_awayBase'` is an **equality**
of formal schemes, so the conclusion of
`AlgebraicGeometry.AffineChartedFibreDatumX.isSeparatedOverSpf_awayBase` is a statement about the
glued object the caller already had. The `CategoryTheory.eqToHom` below is the transport along
that equality and carries no content: the structural morphism it precomposes is the away-base one,
landing in `Spf R{1/f}` rather than in `Spf R`.

**This is the statement the §10.15 refinement direction asks for**, specialised to a basic open of
the base and to a presentation in the smart-constructor vocabulary — see this file's
*What is not proved here* for what separates the two, and
`AlgebraicGeometry.FormalScheme.isSeparatedOverSpf_awayBase_of_factorsThrough` for the form that
asks its caller for no presentation at all. -/
theorem isSeparatedOverSpf_awayBase_xGlued
    (hsep : FormalScheme.IsSeparatedOverSpf hI
      (ofAlgebraData (B := B) hI A g τ τ_symm σ hστ hσc).xGlued
      (ofAlgebraData (B := B) hI A g τ τ_symm σ hστ hσc).xStructMap) :
    letI : ∀ i, IsAdicRing ((I.map (algebraMap R (awayCompletion I f))).map
        (algebraMap (awayCompletion I f) (A i))) :=
      isAdicRing_awayBaseChartIdeal f A hf halg
    haveI : IsAdicRing (I.map (algebraMap R (awayCompletion I f))) :=
      map_awayCompletionHom I f ▸ isAdicRing_awayCompletionIdeal I f hI
    FormalScheme.IsSeparatedOverSpf (hI.map (algebraMap R (awayCompletion I f)))
      (ofAlgebraData (B := B) hI A g τ τ_symm σ hστ hσc).xGlued
      (eqToHom (congrArg FormalScheme.toLocallyRingedSpace
          (ofAlgebraData_xGlued_eq_awayBase' (B := B) (B' := B') hI f A hf g halg
            τ τ_symm σ hστ hσc)).symm ≫
        (ofAlgebraData (B := B') (hI.map (algebraMap R (awayCompletion I f))) A g
          (awayBaseTransition hI f A
            (isScalarTower_of_algebraMap_eq_awayCompletionLift f A hf halg) g τ)
          (awayBaseTransition_symm hI f A
            (isScalarTower_of_algebraMap_eq_awayCompletionLift f A hf halg) g τ τ_symm)
          (awayBaseOverlap hI f A
            (isScalarTower_of_algebraMap_eq_awayCompletionLift f A hf halg) g σ)
          (awayBaseOverlap_transition hI f A
            (isScalarTower_of_algebraMap_eq_awayCompletionLift f A hf halg) g τ σ hστ)
          (awayBaseOverlap_cocycle hI f A
            (isScalarTower_of_algebraMap_eq_awayCompletionLift f A hf halg) g
            σ hσc)).xStructMap) := by
  letI := isScalarTower_of_algebraMap_eq_awayCompletionLift f A hf halg
  letI : ∀ i, IsAdicRing ((I.map (algebraMap R (awayCompletion I f))).map
      (algebraMap (awayCompletion I f) (A i))) :=
    isAdicRing_awayBaseChartIdeal f A hf halg
  haveI : IsAdicRing (I.map (algebraMap R (awayCompletion I f))) :=
    map_awayCompletionHom I f ▸ isAdicRing_awayCompletionIdeal I f hI
  refine FormalScheme.isSeparatedOverSpf_of_iso _
    (eqToIso (congrArg FormalScheme.toLocallyRingedSpace
      (ofAlgebraData_xGlued_eq_awayBase' (B := B) (B' := B') hI f A hf g halg
        τ τ_symm σ hστ hσc))) ?_
    (isSeparatedOverSpf_awayBase hI f A hf g halg τ τ_symm σ hστ hσc hsep)
  simp

/-- **The same statement about an arbitrary formal scheme presented by the datum, on both sides.**
A caller holding a formal scheme `X`, a structural morphism `sX` to `Spf R` and a presentation of
the first by the second gets separatedness of *that* `X` over `Spf R{1/f}`, for the structural
morphism the presentation transports.

This is the form the three open §10.15 directions consume:
`AlgebraicGeometry.FormalScheme.IsSeparatedOverSpf` is presentation-free on both sides of the
implication, and the datum appears only in the hypothesis that `X` is presented by it. The proof
is `AlgebraicGeometry.AffineChartedFibreDatumX.isSeparatedOverSpf_awayBase_xGlued` between two
applications of `AlgebraicGeometry.FormalScheme.isSeparatedOverSpf_iff_of_iso`, one on each
base. -/
theorem isSeparatedOverSpf_awayBase_of_presentation {X : FormalScheme.{u}}
    {sX : X.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I}
    (e : (ofAlgebraData (B := B) hI A g τ τ_symm σ hστ hσc).xGlued.toLocallyRingedSpace ≅
      X.toLocallyRingedSpace)
    (he : e.hom ≫ sX = (ofAlgebraData (B := B) hI A g τ τ_symm σ hστ hσc).xStructMap)
    (hsep : FormalScheme.IsSeparatedOverSpf hI X sX) :
    letI : ∀ i, IsAdicRing ((I.map (algebraMap R (awayCompletion I f))).map
        (algebraMap (awayCompletion I f) (A i))) :=
      isAdicRing_awayBaseChartIdeal f A hf halg
    haveI : IsAdicRing (I.map (algebraMap R (awayCompletion I f))) :=
      map_awayCompletionHom I f ▸ isAdicRing_awayCompletionIdeal I f hI
    FormalScheme.IsSeparatedOverSpf (hI.map (algebraMap R (awayCompletion I f))) X
      (e.inv ≫ eqToHom (congrArg FormalScheme.toLocallyRingedSpace
          (ofAlgebraData_xGlued_eq_awayBase' (B := B) (B' := B') hI f A hf g halg
            τ τ_symm σ hστ hσc)).symm ≫
        (ofAlgebraData (B := B') (hI.map (algebraMap R (awayCompletion I f))) A g
          (awayBaseTransition hI f A
            (isScalarTower_of_algebraMap_eq_awayCompletionLift f A hf halg) g τ)
          (awayBaseTransition_symm hI f A
            (isScalarTower_of_algebraMap_eq_awayCompletionLift f A hf halg) g τ τ_symm)
          (awayBaseOverlap hI f A
            (isScalarTower_of_algebraMap_eq_awayCompletionLift f A hf halg) g σ)
          (awayBaseOverlap_transition hI f A
            (isScalarTower_of_algebraMap_eq_awayCompletionLift f A hf halg) g τ σ hστ)
          (awayBaseOverlap_cocycle hI f A
            (isScalarTower_of_algebraMap_eq_awayCompletionLift f A hf halg) g
            σ hσc)).xStructMap) := by
  letI := isScalarTower_of_algebraMap_eq_awayCompletionLift f A hf halg
  letI : ∀ i, IsAdicRing ((I.map (algebraMap R (awayCompletion I f))).map
      (algebraMap (awayCompletion I f) (A i))) :=
    isAdicRing_awayBaseChartIdeal f A hf halg
  haveI : IsAdicRing (I.map (algebraMap R (awayCompletion I f))) :=
    map_awayCompletionHom I f ▸ isAdicRing_awayCompletionIdeal I f hI
  refine FormalScheme.isSeparatedOverSpf_of_iso _ e ?_
    (isSeparatedOverSpf_awayBase_xGlued (B := B) (B' := B') hI f A hf g halg τ τ_symm σ hστ hσc
      ((FormalScheme.isSeparatedOverSpf_iff_of_iso hI e he).mpr hsep))
  exact e.hom_inv_id_assoc _

end AffineChartedFibreDatumX

/-!
### Steps 1 and 2 at a presentation, and the basic-open statement they free

The two declarations of this section that carry no `f` are the consumer-shaped form of
`AlgebraicGeometry.AffineChartedFibreDatumX.eq_ofAlgebraData`: an arbitrary presentation of a
formal scheme is a smart-constructor presentation, because
`AlgebraicGeometry.FormalScheme.IsSeparatedOverSpf` hands its caller the double-overlap data along
with the datum. The rest turn a factorisation of the structural morphism through the basic open of
the base into the two hypotheses that
`AlgebraicGeometry.AffineChartedFibreDatumX.isSeparatedOverSpf_awayBase` asks for, chart by
chart.
-/

section AwayBaseFactorisation

variable {R : Type u} [CommRing R] {I : Ideal R} (hI : I.FG) (f : R)
variable [TopologicalSpace R] [IsAdicRing I]
variable {B : Type u} [CommRing B] [Algebra R B]
variable [IsAdicRing (I.map (algebraMap R (awayCompletion I f)))]

namespace AffineChartedFibreDatumX

omit [TopologicalSpace R] [IsAdicRing I]
  [IsAdicRing (I.map (algebraMap R (awayCompletion I f)))] in
/-- **A presentation transports along an equality of data.** Trivial, and stated because the
equality it consumes is the conclusion of
`AlgebraicGeometry.AffineChartedFibreDatumX.eq_ofAlgebraData` and the existential it produces is
the shape `AlgebraicGeometry.FormalScheme.IsSeparatedOverSpf` unpacks to. -/
theorem exists_presentation_of_eq {D D' : AffineChartedFibreDatumX R I hI B} (h : D = D')
    {X : FormalScheme.{u}} {s : X.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I}
    (e : D.xGlued.toLocallyRingedSpace ≅ X.toLocallyRingedSpace)
    (he : e.hom ≫ s = D.xStructMap) :
    ∃ e' : D'.xGlued.toLocallyRingedSpace ≅ X.toLocallyRingedSpace,
      e'.hom ≫ s = D'.xStructMap := by
  subst h
  exact ⟨e, he⟩

variable (D : AffineChartedFibreDatumX R I hI B)

/-- **The localising element is inverted on every chart of a presentation whose structural morphism
factors through the basic open.** `FormalSpectrum.isUnit_algebraMap_of_factorsThrough` at the
restriction of the factorisation to chart `i`, whose composite with the basic open is
`AlgebraicGeometry.AffineChartedFibreDatumX.xStructMapChart` by
`AlgebraicGeometry.AffineChartedFibreDatumX.ι_xStructMap`. -/
theorem isUnit_algebraMap_of_xStructMap_factorsThrough
    (t : D.xGlued.toLocallyRingedSpace ⟶
      locallyRingedSpaceObj (I.map (algebraMap R (awayCompletion I f))))
    (ht : t ≫ awayBaseChart I f = D.xStructMap) (i : D.J) :
    letI := D.commRing
    letI := D.algebra
    IsUnit (algebraMap R (D.A i) f) := by
  letI := D.commRing
  letI := D.algebra
  letI := D.topology
  letI := D.isAdic
  let u : locallyRingedSpaceObj (I.map (algebraMap R (D.A i))) ⟶
      locallyRingedSpaceObj (I.map (algebraMap R (awayCompletion I f))) :=
    D.xFormalGlueData.ι i ≫ t
  refine isUnit_algebraMap_of_factorsThrough I f hI u ?_
  change (D.xFormalGlueData.ι i ≫ t) ≫ _ = _
  rw [Category.assoc]
  exact (congrArg (fun m => D.xFormalGlueData.ι i ≫ m) ht).trans (D.ι_xStructMap i)

/-- **The factorisation restricted to a chart is `Spf` of the lift.**
`FormalSpectrum.eq_locallyRingedSpaceMap_awayCompletionLift` at the restriction of the
factorisation to chart `i`.

This is the per-chart half of identifying the structural morphism of the away-base presentation
with the factorisation itself; see this file's *What is not proved here* for the half that is
missing. -/
theorem ι_comp_eq_of_factorsThrough
    (t : D.xGlued.toLocallyRingedSpace ⟶
      locallyRingedSpaceObj (I.map (algebraMap R (awayCompletion I f))))
    (ht : t ≫ awayBaseChart I f = D.xStructMap) (i : D.J)
    (hfu : letI := D.commRing; letI := D.algebra; IsUnit (algebraMap R (D.A i) f)) :
    letI := D.commRing
    letI := D.algebra
    letI := D.topology
    letI := D.isAdic
    letI := (D.isAdic i).toIsAdicComplete
    D.xFormalGlueData.ι i ≫ t =
      locallyRingedSpaceMap (I.map (algebraMap R (awayCompletion I f)))
        (I.map (algebraMap R (D.A i))) (awayCompletionLift I f hfu)
        (le_comap_awayCompletionLift I f hfu) := by
  letI := D.commRing
  letI := D.algebra
  letI := D.topology
  letI := D.isAdic
  letI := (D.isAdic i).toIsAdicComplete
  refine eq_locallyRingedSpaceMap_awayCompletionLift I f hI
    (D.xFormalGlueData.ι i ≫ t) ?_ hfu
  change (D.xFormalGlueData.ι i ≫ t) ≫ _ = _
  rw [Category.assoc]
  exact (congrArg (fun m => D.xFormalGlueData.ι i ≫ m) ht).trans (D.ι_xStructMap i)

/-- **A structural morphism factors through the basic open of its base in at most one way.** The
two factorisations agree on every chart by
`AlgebraicGeometry.AffineChartedFibreDatumX.ι_comp_eq_of_factorsThrough`, whose right-hand side
depends on the factorisation only through a proof of a proposition, and the glue inclusions are
jointly epimorphic (`AlgebraicGeometry.FormalScheme.GlueData.hom_ext`). -/
theorem factorsThrough_awayBase_unique
    (t t' : D.xGlued.toLocallyRingedSpace ⟶
      locallyRingedSpaceObj (I.map (algebraMap R (awayCompletion I f))))
    (ht : t ≫ awayBaseChart I f = D.xStructMap)
    (ht' : t' ≫ awayBaseChart I f = D.xStructMap) :
    t = t' := by
  refine D.xFormalGlueData.hom_ext fun i => ?_
  letI := D.commRing
  letI := D.algebra
  letI := D.topology
  letI := D.isAdic
  have hfu : IsUnit (algebraMap R (D.A i) f) :=
    D.isUnit_algebraMap_of_xStructMap_factorsThrough hI f t ht i
  rw [D.ι_comp_eq_of_factorsThrough hI f t ht i hfu,
    D.ι_comp_eq_of_factorsThrough hI f t' ht' i hfu]

end AffineChartedFibreDatumX

open AffineChartedFibreDatumX in
/-- **Every presentation is a smart-constructor presentation, for the caller who holds one.**
`AlgebraicGeometry.FormalScheme.IsSeparatedOverSpf` is existential over a datum *together with* its
double-overlap data and the two laws, which is exactly what
`AlgebraicGeometry.AffineChartedFibreDatumX.eq_ofAlgebraData` asks for; so unpacking the predicate
and transporting the presentation along that equality re-presents the same formal scheme in the
`AlgebraicGeometry.AffineChartedFibreDatumX.ofAlgebraData` vocabulary.

The instance arguments of the final term are supplied by name rather than by `inferInstance`:
elaborating them by unification costs more than the default budget allows. -/
theorem FormalScheme.isSeparatedOverSpf_exists_ofAlgebraData {X : FormalScheme.{u}}
    {s : X.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I}
    (hsep : FormalScheme.IsSeparatedOverSpf hI X s) :
    ∃ (BX : Type u) (_ : CommRing BX) (_ : Algebra R BX) (J : Type u) (A : J → Type u)
      (_ : ∀ i, CommRing (A i)) (_ : ∀ i, Algebra R (A i)) (_ : ∀ i, TopologicalSpace (A i))
      (_ : ∀ i, IsAdicRing (I.map (algebraMap R (A i)))) (g : ∀ i : J, J → A i)
      (τ : ∀ (i j : J), i ≠ j →
        (awayCompletion (I.map (algebraMap R (A i))) (g i j) ≃ₐ[R]
          awayCompletion (I.map (algebraMap R (A j))) (g j i)))
      (τ_symm : ∀ (i j : J) (h : i ≠ j), τ j i h.symm = (τ i j h).symm)
      (σ : ∀ (i j k : J), i ≠ j → i ≠ k → j ≠ k →
        (awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k) ≃ₐ[R]
          awayCompletion (I.map (algebraMap R (A j))) (g j k * g j i)))
      (hστ : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
        (σ i j k hij hik hjk).symm.toAlgHom.comp (furtherLocSnd I (g j k) (g j i) hI) =
          (furtherLocFst I (g i j) (g i k) hI).comp (τ i j hij).symm.toAlgHom)
      (hσc : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
        (σ i j k hij hik hjk).trans ((σ j k i hjk hij.symm hik.symm).trans
          (σ k i j hik.symm hjk.symm hij)) =
          AlgEquiv.refl (R := R)
            (A₁ := awayCompletion (I.map (algebraMap R (A i))) (g i j * g i k)))
      (e : (ofAlgebraData (B := BX) hI A g τ τ_symm σ hστ
          hσc).xGlued.toLocallyRingedSpace ≅ X.toLocallyRingedSpace),
      e.hom ≫ s = (ofAlgebraData (B := BX) hI A g τ τ_symm σ hστ hσc).xStructMap := by
  obtain ⟨BX, _, _, DX, σX, hστX, hσcX, e, he, _⟩ := hsep
  letI := DX.commRing
  letI := DX.algebra
  letI := DX.topology
  letI := DX.isAdic
  obtain ⟨e', he'⟩ := AffineChartedFibreDatumX.exists_presentation_of_eq hI
    (AffineChartedFibreDatumX.eq_ofAlgebraData hI DX σX hστX hσcX) e he
  exact ⟨BX, inferInstance, inferInstance, DX.J, DX.A, DX.commRing, DX.algebra, DX.topology,
    DX.isAdic, DX.g, DX.τ, DX.τ_symm, σX, hστX, hσcX, e', he'⟩

open AffineChartedFibreDatumX in
/-- **Separatedness over `Spf R` descends to a basic open of the base that the structural morphism
factors through, with no presentation in the statement at all.**

This is row 1987's statement (B) at a basic open of the base: the source is an arbitrary formal
scheme, the hypothesis is separatedness over `Spf R` together with a factorisation of the
structural morphism through `Spf R{1/f}`, and **nothing about a presentation appears on either
side**. Both hypotheses of
`AlgebraicGeometry.AffineChartedFibreDatumX.isSeparatedOverSpf_awayBase_of_presentation` are
discharged here:
`AlgebraicGeometry.AffineChartedFibreDatumX.isUnit_algebraMap_of_xStructMap_factorsThrough`
supplies the unit, and at the `RingHom.toAlgebra` structure of
`FormalSpectrum.awayCompletionLift` the identification of the algebra structure with the lift is
`rfl`.

**The structural morphism of the conclusion is existentially quantified, and that is the one thing
this statement does not settle.** It is the one the away-base presentation carries, and identifying
it with the factorisation is the residue recorded in this file's *What is not proved here*. -/
theorem FormalScheme.isSeparatedOverSpf_awayBase_of_factorsThrough {X : FormalScheme.{u}}
    {sX : X.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I}
    (t : X.toLocallyRingedSpace ⟶
      locallyRingedSpaceObj (I.map (algebraMap R (awayCompletion I f))))
    (ht : t ≫ awayBaseChart I f = sX)
    (hsep : FormalScheme.IsSeparatedOverSpf hI X sX) :
    ∃ s' : X.toLocallyRingedSpace ⟶
        locallyRingedSpaceObj (I.map (algebraMap R (awayCompletion I f))),
      FormalScheme.IsSeparatedOverSpf (hI.map (algebraMap R (awayCompletion I f))) X s' := by
  obtain ⟨BX, _, _, J, A, cA, aA, tA, adA, g, τ, τ_symm, σ, hστ, hσc, e, he⟩ :=
    FormalScheme.isSeparatedOverSpf_exists_ofAlgebraData hI hsep
  letI := cA
  letI := aA
  letI := tA
  letI := adA
  have hf : ∀ i, IsUnit (algebraMap R (A i) f) := fun i =>
    (ofAlgebraData (B := BX) hI A g τ τ_symm σ hστ
      hσc).isUnit_algebraMap_of_xStructMap_factorsThrough hI f (e.hom ≫ t)
      (by rw [Category.assoc, ht, he]) i
  letI : ∀ i, Algebra (awayCompletion I f) (A i) := fun i =>
    letI := (adA i).toIsAdicComplete
    (awayCompletionLift I f (hf i)).toAlgebra
  have halg : ∀ i, letI := (adA i).toIsAdicComplete
      algebraMap (awayCompletion I f) (A i) = awayCompletionLift I f (hf i) := fun _ => rfl
  exact ⟨_, isSeparatedOverSpf_awayBase_of_presentation (B := BX) (B' := awayCompletion I f)
    hI f A hf g halg τ τ_symm σ hστ hσc e he hsep⟩

end AwayBaseFactorisation

end AlgebraicGeometry

end
