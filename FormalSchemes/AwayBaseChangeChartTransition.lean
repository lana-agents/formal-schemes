import FormalSchemes.GeneralFibreProductBaseChange
import FormalSchemes.AwayBaseChangeGluedX

set_option linter.style.header false

/-!
# The chart-transition hypothesis of the fibre-product base change, at an away base

`FormalSchemes.GeneralFibreProductBaseChange` assembles the comparison
`X ×_{Spf I'} Y ⟶ X ×_{Spf I} Y` out of its charts and proves the two facts a consumer wants — the
overlap square `AlgebraicGeometry.DoubleChartGlue.isBaseChangeOverlapCompatible_of_bothAlgData` and
injectivity of the glued comparison
`AlgebraicGeometry.DoubleChartGlue.injective_baseChange_base_of_bothAlgData` — over **one** input
that file does not produce and says so: `AlgebraicGeometry.IsChartTransitionBaseChange`, the
statement that the primed chart transitions are the unprimed ones read over `R'`.

That input is a *condition on how the primed datum is chosen*, and over a general tower `R → R'`
it has to stay one: an `R`-algebra equivalence of chart rings is not an `R'`-algebra equivalence,
and nothing enlarges its scalars. **This file discharges it at `R' = R{1/f}`**, which is the case
the refinement of a formal-scheme presentation actually needs, since shrinking the affine base
`Spf R` to a basic open replaces it by the completed localization.

## Why the away base is different, and it is not a matter of degree

The scalars are enlarged by `FormalSpectrum.awayCompletionChartAlgEquivBase`
(`FormalSchemes.AwayCompletionUniversal`), which reads an `R`-algebra equivalence of two away
completions of `(R, I)`-algebras as an `R{1/f}`-algebra equivalence *without changing its
underlying function*. Its proof is `FormalSpectrum.awayCompletion_hom_ext'` — **rigidity of the
away completion as a source**: two continuous maps out of `R{1/f}^` agreeing on `R` agree. That is
a statement about `R{1/f}` and about no other `R'`, so nothing here generalises to a tower, and
`FormalSchemes.GeneralFibreProductBaseChange`'s *Reducing the square* says the same thing from the
other side.

## The `Y` side is the `X`-side construction, re-instantiated

`AlgebraicGeometry.AffineChartedFibreDatumX.awayBaseTransition`
(`FormalSchemes.AwayBaseChangeGluedX`) already builds the primed transitions: enlarge the scalars
as above, then move the carriers from `I·A i` to `(I·R{1/f})·A i` along
`AlgebraicGeometry.AffineChartedFibreDatumX.awayBaseChartIdeal` with
`FormalSpectrum.awayTransport`. **Nothing two-sided had to be constructed here**, because that
definition is stated over an arbitrary index type and an arbitrary chart family: the `X` in its
namespace records where it was proved and not what it is about, so instantiating it at the second
factor's `(JY, B, gY)` gives the `Y`-side family verbatim. The same is true of its
`AlgebraicGeometry.AffineChartedFibreDatumX.awayBaseTransition_coe_heq`, which is exactly the
`HEq`-of-coercions that each of the two fields of
`AlgebraicGeometry.IsChartTransitionBaseChange` asks for.

So the content of this file is the *edge*: neither of its two parents names the other, one states
the hypothesis and the other builds the thing that meets it, and the term below is the pair of
coercion equalities handed to the structure's anonymous constructor.

## Main results

* `AlgebraicGeometry.isChartTransitionBaseChange_awayBase`: **the hypothesis, discharged** at
  `R' = R{1/f}` and `I' = I·R{1/f}`, for the primed transitions
  `AlgebraicGeometry.AffineChartedFibreDatumX.awayBaseTransition` produces on each side.
* `AlgebraicGeometry.DoubleChartGlue.isBaseChangeOverlapCompatible_of_bothAlgData_awayBase`: **the
  overlap square at that base**, so a caller who has shrunk `Spf R` to a basic open supplies the
  six identifications of the two glues and no transition hypothesis at all.

Both are stated at `I' = I.map (algebraMap R (FormalSpectrum.awayCompletion I f))` *by
definition* rather than over an equation, so the base-equation argument of everything they consume
is `rfl` and no transport along it appears anywhere below.

## What is not proved here

* **The primed glue is still not constructed.** The corollary takes a
  `AlgebraicGeometry.DoubleChartGlue` over `(R{1/f}, I·R{1/f})` as an argument together with the
  six identifications of its fields, exactly as its general-tower original does. Assembling one —
  the transitions **and** the double-overlap data over the primed base, as a
  `AlgebraicGeometry.BothChartedFibreDatum` — is the obligation
  `FormalSchemes.GeneralFibreProductBaseChange` records under *What is not proved here* and it is
  untouched by this file. What this file removes from that obligation is its transition half:
  `AlgebraicGeometry.AffineChartedFibreDatumX.awayBaseTransition` is the family such a constructor
  should carry, and the theorem below is the proof that carrying it costs the assembler nothing.
* **No injectivity corollary.**
  `AlgebraicGeometry.DoubleChartGlue.injective_baseChange_base_of_bothAlgData` specialises the same
  way and over the same term, but it carries the adic-ring and topology instances of the fibre
  product besides, and no consumer on this tree asks for it yet.
* **Nothing about a general tower**, and nothing restated from either parent. The general-tower
  statements are where they were; this file adds no hypothesis to them and weakens none.
* **No separation statement.** Nothing here mentions
  `AlgebraicGeometry.BothChartedFibreDatumXY.IsSeparated` or
  `AlgebraicGeometry.FormalScheme.IsSeparatedOverSpf`.

## Placement

A leaf over `FormalSchemes.GeneralFibreProductBaseChange` and
`FormalSchemes.AwayBaseChangeGluedX`: this file's forward closure is **116** project modules
besides itself (117 counted with itself), and this file's reverse closure is **0**.

The two parents are **import-incomparable**, and that is what makes this a leaf rather than a
declaration in one of them. They share **72** modules; `FormalSchemes.GeneralFibreProductBaseChange`
contributes **22** that the other does not reach and
`FormalSchemes.AwayBaseChangeGluedX` contributes **22** that the first does not, so either edge
costs twenty-two modules and neither is cheaper than the other. What decides it is what the edge
would carry:

* adding the statement to `FormalSchemes.GeneralFibreProductBaseChange` puts the one-sided
  away-base gluing theory inside the closure of the file whose own *What is not proved here* says,
  correctly, that nothing in it produces this hypothesis — a sentence the import would falsify
  while the file's subject stayed the general tower;
* adding it to `FormalSchemes.AwayBaseChangeGluedX` puts the whole completed-tensor base change of
  a *fibre product* inside the closure of a file about gluing a single factor, and everything that
  file ever acquires as a consumer would carry it. `FormalSchemes.AwayBaseChangeGluedX`'s reverse
  closure is **1** — this file, and this file only — which is an argument for not making the
  one-sided theory expensive while it is still cheap.

A leaf leaves both subjects alone and both forward closures unmoved, at the price of the reverse
closure of every module it imports moving by one — the trade
`FormalSchemes.GeneralFibreProductBaseChange`'s own *Placement* section made when it rejected an
edge in both directions for the same reason.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.14.
-/

noncomputable section

open CategoryTheory FormalSpectrum

universe u

namespace AlgebraicGeometry

variable {R : Type u} [CommRing R] {I : Ideal R} (hI : I.FG) (f : R)
variable {JX JY : Type u} {A : JX → Type u} {B : JY → Type u}
variable [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
variable [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
variable [∀ i, Algebra (awayCompletion I f) (A i)]
variable [∀ j, Algebra (awayCompletion I f) (B j)]
variable [towerA : ∀ i, IsScalarTower R (awayCompletion I f) (A i)]
variable [towerB : ∀ j, IsScalarTower R (awayCompletion I f) (B j)]
variable {gX : ∀ i _ : JX, A i} {gY : ∀ j _ : JY, B j}

/-- **The transition hypothesis of the fibre-product base change is a theorem at an away base.**
*Reach for this one*: it is the single input
`AlgebraicGeometry.DoubleChartGlue.isBaseChangeOverlapCompatible_of_bothAlgData` asks for and
cannot produce, and over `R' = R{1/f}` with `I' = I·R{1/f}` it is produced rather than assumed.

The primed transitions are not new data. On each side they are
`AlgebraicGeometry.AffineChartedFibreDatumX.awayBaseTransition` of the unprimed ones — the scalars
enlarged by `FormalSpectrum.awayCompletionChartAlgEquivBase` and the carriers moved by
`FormalSpectrum.awayTransport` — and both fields are then that definition's own
`AlgebraicGeometry.AffineChartedFibreDatumX.awayBaseTransition_coe_heq`, which says the transport
leaves the underlying function alone.

The `Y` side is the same lemma at the second factor's index type: the construction is stated over
an arbitrary chart family, so no `Y`-side analogue exists or is needed. -/
theorem isChartTransitionBaseChange_awayBase
    (τX : ∀ (i i' : JX), i ≠ i' →
      (awayCompletion (I.map (algebraMap R (A i))) (gX i i') ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A i'))) (gX i' i)))
    (τY : ∀ (j j' : JY), j ≠ j' →
      (awayCompletion (I.map (algebraMap R (B j))) (gY j j') ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (B j'))) (gY j' j))) :
    IsChartTransitionBaseChange (R' := awayCompletion I f)
      (I' := I.map (algebraMap R (awayCompletion I f))) τX τY
      (AffineChartedFibreDatumX.awayBaseTransition hI f A towerA gX τX)
      (AffineChartedFibreDatumX.awayBaseTransition hI f B towerB gY τY) :=
  ⟨AffineChartedFibreDatumX.awayBaseTransition_coe_heq hI f A towerA gX τX,
    AffineChartedFibreDatumX.awayBaseTransition_coe_heq hI f B towerB gY τY⟩

/-- **The overlap square of the glued base change, at an away base.** *Reach for this one*: it is
`AlgebraicGeometry.DoubleChartGlue.isBaseChangeOverlapCompatible_of_bothAlgData` with its
transition hypothesis discharged and its primed transitions filled in, so a caller who has replaced
`Spf R` by the basic open `D(f)` supplies only the six identifications saying that the two glues
carry the dispatched overlap data.

The base equation `I.map (algebraMap R R') = I'` is `rfl` here, because the primed ideal is that
extension by definition; that is why no transport along it appears in the statement and why the
finite-generation argument of each dispatched field at the primed base is spelled
`CompletedTensorProduct.fg_of_map_eq hI rfl`. -/
theorem DoubleChartGlue.isBaseChangeOverlapCompatible_of_bothAlgData_awayBase
    (G' : DoubleChartGlue (awayCompletion I f)
      (I.map (algebraMap R (awayCompletion I f))) A B)
    (G : DoubleChartGlue R I A B)
    (τX : ∀ (i i' : JX), i ≠ i' →
      (awayCompletion (I.map (algebraMap R (A i))) (gX i i') ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (A i'))) (gX i' i)))
    (τY : ∀ (j j' : JY), j ≠ j' →
      (awayCompletion (I.map (algebraMap R (B j))) (gY j j') ≃ₐ[R]
        awayCompletion (I.map (algebraMap R (B j'))) (gY j' j)))
    (hGV : ∀ (p p' : JX × JY) (hne : p ≠ p'),
      G.V p p' hne = bothAlgDataV hI gX gY p p' hne)
    (hGf : ∀ (p p' : JX × JY) (hne : p ≠ p'),
      G.f p p' hne = eqToHom (hGV p p' hne) ≫ bothAlgDataF hI gX gY p p' hne)
    (hGt : ∀ (p p' : JX × JY) (hne : p ≠ p'),
      G.t p p' hne = eqToHom (hGV p p' hne) ≫ bothAlgDataT hI gX gY τX τY p p' hne ≫
        eqToHom (hGV p' p hne.symm).symm)
    (hG'V : ∀ (p p' : JX × JY) (hne : p ≠ p'),
      G'.V p p' hne =
        bothAlgDataV (CompletedTensorProduct.fg_of_map_eq hI rfl) gX gY p p' hne)
    (hG'f : ∀ (p p' : JX × JY) (hne : p ≠ p'),
      G'.f p p' hne = eqToHom (hG'V p p' hne) ≫
        bothAlgDataF (CompletedTensorProduct.fg_of_map_eq hI rfl) gX gY p p' hne)
    (hG't : ∀ (p p' : JX × JY) (hne : p ≠ p'),
      G'.t p p' hne = eqToHom (hG'V p p' hne) ≫
        bothAlgDataT (CompletedTensorProduct.fg_of_map_eq hI rfl) gX gY
          (AffineChartedFibreDatumX.awayBaseTransition hI f A towerA gX τX)
          (AffineChartedFibreDatumX.awayBaseTransition hI f B towerB gY τY) p p' hne ≫
        eqToHom (hG'V p' p hne.symm).symm) :
    G'.IsBaseChangeOverlapCompatible G hI rfl :=
  isBaseChangeOverlapCompatible_of_bothAlgData G' G hI rfl τX τY _ _
    (isChartTransitionBaseChange_awayBase hI f τX τY) hGV hGf hGt hG'V hG'f hG't

end AlgebraicGeometry

end
