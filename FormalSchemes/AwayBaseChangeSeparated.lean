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
open of the base is a **basic** open and the presentation of the source is given in the
smart-constructor vocabulary with `f` inverted on every chart. Getting from an arbitrary open
subscheme of an arbitrary formal scheme to that shape is the residue, and it is not done here.

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
`FormalSchemes.GeneralSeparatedScheme`'s reverse closure is **13**, and none of those modules is
about a change of base.

A leaf leaves all three subjects alone and moves no forward closure anywhere, at the price of the
reverse closure of every module it imports moving by one.

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

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.12, §10.15.
* [The Stacks Project, Tag 01KJ](https://stacks.math.columbia.edu/tag/01KJ).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum Topology
open CompletedTensorAwayInterchange CompletedTensorProduct

universe u

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
*What is not proved here* for what separates the two. -/
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

end AlgebraicGeometry

end
