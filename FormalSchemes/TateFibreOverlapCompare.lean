import FormalSchemes.TateSelfProductGlueDatum
import FormalSchemes.TateTensorOverlapChartIsoBoth
import FormalSchemes.GeneralFibreProductBothAlgebraDataObject

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000

/-!
# Comparing the two presentations of the Tate self-fibre-product overlaps

Brick 4 of issue 601 has to identify the hand-built four-chart self fibre product
`tateSelfProductInv` with the `generalFibreProduct` of the diagonal datum of
`tateCurveExposeXDatum`. The `Φ` direction of that comparison (`TateFibreProductHom.lean`) needs no
glue-datum work; the `Ψ` direction does, and this file supplies its **object and chart layer**: the
two presentations have isomorphic overlap objects, compatibly with their overlap charts.

## The two presentations

The generic side is the `bothAlgData…` family: `bothAlgDataV` dispatches on the *difference type* of
a pair of product indices `p p' : ULift Bool × ULift Bool` — second coordinate differs, first
coordinate differs, both differ — and produces the **merged** chart
`Spf(A ⊗̂_R A{1/(x+y)}^)`, `Spf(A{1/(x+y)}^ ⊗̂_R A)`, `Spf(A{1/(x+y)}^ ⊗̂_R A{1/(x+y)}^)`, with
`bothAlgDataF` the corresponding `…InterchangeOpenImmersion`.

The Tate side is `tateSelfProductGlueV` / `…GlueF`: an explicit sixteen-way match on
`Bool × Bool` producing the **coproduct** objects `Spf(A ⊗̂ A{1/x}) ⨿ Spf(A ⊗̂ A{1/y})` and their
siblings, with the `…FactorOverlapChart`s.

Merged versus coproduct is exactly what 738/739 identified
(`tensorOverlapChartIso{First,Second,Both}`), and those isomorphisms come with the factorisations
`…_hom_fac` saying that they commute with the two chart presentations. So the comparison is
mechanical once the sixteen-way match is reduced by difference type, which is what the
`tateSelfProductGlueV_…` / `…GlueF_…` lemmas below do.

## What is here, and what is not

`tateOverlapCompareIso` and `tateOverlapCompareIso_hom_fac` are the **`V` and `f` layers** of the
`Ψ` comparison. The **`t` layer** — matching `bothAlgDataT` (which is `Spf` of `id ⊗̂ τ` for
`τ = annulusFibreOverlapTransitionAlg`) against `tateSelfProductGlueTInv` — is *not* here. That is
the content of the remaining half of 705c and is where 751/761's eight `tensorOverlapSummand…`
identifications get consumed; the `Ψ` morphism cannot be built without it.

Both layers are stated against the raw algebra data (`A` constant, `g = x + y` constant, both read
off `tateCurveExposeXDatum`) rather than against the datum, so that they do not depend on the
`ofFactors`/`diagonalDatum` packaging: `ofFactors_hV` and `tateCurveExposeXDatum_g` bridge to them
by `rfl`.

## Main definitions and results

* `AlgebraicGeometry.tateFibreIdx`: the free index conversion
  `ULift Bool × ULift Bool → Bool × Bool`.
* `AlgebraicGeometry.tateSelfProductGlueV_snd` / `_fst` / `_both`,
  `tateSelfProductGlueF_snd` / `_fst` / `_both`: reduction of the sixteen-way match by difference
  type.
* `AlgebraicGeometry.tateOverlapCompareIso`: the overlap comparison isomorphism.
* `AlgebraicGeometry.tateOverlapCompareIso_hom_fac`: it is a morphism over the common chart.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
  CompletedTensorProduct CompletedTensorAwayInterchange

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-! ### The index conversion -/

/-- **The chart family of the Tate `X`-expose datum**: the constant family `A i = A`. Read off
`tateCurveExposeXDatum`, where it is the `A` argument of `ofAlgebraData`. -/
abbrev tateFibreA : ULift.{u} Bool → Type u := fun _ => annulusAlgebra R I q

/-- **The away element of the Tate `X`-expose datum**: the constant family `g i j = x + y`. This is
601a's content — the two-chart overlap is the single basic open `D(x + y)` — and it is what
`tateCurveExposeXDatum_g` records. -/
abbrev tateFibreG : ∀ _ _ : ULift.{u} Bool, annulusAlgebra R I q :=
  fun _ _ => overlapX R I q + overlapY R I q

/-- **The index conversion** `ULift Bool × ULift Bool → Bool × Bool` between the generic datum's
product index and the Tate glue datum's. Its inverse `⟨p.1, p.2⟩ ↦ (⟨p.1⟩, ⟨p.2⟩)` composes with it
to the identity definitionally, by structure eta, so no transport is ever needed. -/
abbrev tateFibreIdx (p : ULift.{u} Bool × ULift.{u} Bool) : Bool × Bool := (p.1.down, p.2.down)

/-- The index conversion is injective, in the form the sixteen-way match consumes. -/
theorem tateFibreIdx_ne {p p' : ULift.{u} Bool × ULift.{u} Bool} (h : p ≠ p') :
    tateFibreIdx p ≠ tateFibreIdx p' := fun e =>
  h (Prod.ext (ULift.ext _ _ (congrArg Prod.fst e)) (ULift.ext _ _ (congrArg Prod.snd e)))

/-! ### Reducing the sixteen-way match by difference type

`tateSelfProductGlueV` and `tateSelfProductGlueF` are defined by an explicit sixteen-way match so
that `V i j` and `V j i` are the *same* object definitionally. That is the right definition for the
glue datum, but it means nothing reduces under a hypothesis of the form `i.1 = j.1`. The six lemmas
below do the reduction once, by `rcases` on both indices; every branch is `rfl` or a contradiction,
so they are cheap despite the sixteen cases. -/

variable {R I q}

/-- **The `V` datum in the second-coordinate-differs shape.** -/
theorem tateSelfProductGlueV_snd (hI : I.FG) (i j : Bool × Bool) (h : i ≠ j) (h1 : i.1 = j.1) :
    tateSelfProductGlueV R I q hI i j h =
      (locallyRingedSpaceObj (idealOfDefinition R I (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) ⨿
        locallyRingedSpaceObj (idealOfDefinition R I (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))) := by
  rcases i with ⟨_ | _, _ | _⟩ <;> rcases j with ⟨_ | _, _ | _⟩ <;>
    first
      | exact (h rfl).elim
      | exact absurd h1 (by decide)
      | rfl

/-- **The `V` datum in the first-coordinate-differs shape.** -/
theorem tateSelfProductGlueV_fst (hI : I.FG) (i j : Bool × Bool) (h : i ≠ j) (h1 : i.1 ≠ j.1)
    (h2 : i.2 = j.2) :
    tateSelfProductGlueV R I q hI i j h =
      (locallyRingedSpaceObj (idealOfDefinition R I
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
          (annulusAlgebra R I q)) ⨿
        locallyRingedSpaceObj (idealOfDefinition R I
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
          (annulusAlgebra R I q))) := by
  rcases i with ⟨_ | _, _ | _⟩ <;> rcases j with ⟨_ | _, _ | _⟩ <;>
    first
      | exact (h rfl).elim
      | exact absurd h2 (by decide)
      | exact absurd rfl h1
      | rfl

/-- **The `V` datum in the both-coordinates-differ shape.** -/
theorem tateSelfProductGlueV_both (hI : I.FG) (i j : Bool × Bool) (h : i ≠ j) (h1 : i.1 ≠ j.1)
    (h2 : i.2 ≠ j.2) :
    tateSelfProductGlueV R I q hI i j h =
      ((locallyRingedSpaceObj (idealOfDefinition R I
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) ⨿
          locallyRingedSpaceObj (idealOfDefinition R I
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))) ⨿
        (locallyRingedSpaceObj (idealOfDefinition R I
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) ⨿
          locallyRingedSpaceObj (idealOfDefinition R I
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))))) := by
  rcases i with ⟨_ | _, _ | _⟩ <;> rcases j with ⟨_ | _, _ | _⟩ <;>
    first
      | exact (h rfl).elim
      | exact absurd rfl h1
      | exact absurd rfl h2
      | rfl

/-- **The `f` datum in the second-coordinate-differs shape.** -/
theorem tateSelfProductGlueF_snd (hI : I.FG) (i j : Bool × Bool) (h : i ≠ j) (h1 : i.1 = j.1) :
    tateSelfProductGlueF R I q hI i j h =
      eqToHom (tateSelfProductGlueV_snd hI i j h h1) ≫ secondFactorOverlapChart R I q hI := by
  rcases i with ⟨_ | _, _ | _⟩ <;> rcases j with ⟨_ | _, _ | _⟩ <;>
    first
      | exact (h rfl).elim
      | exact absurd h1 (by decide)
      | exact (Category.id_comp _).symm

/-- **The `f` datum in the first-coordinate-differs shape.** -/
theorem tateSelfProductGlueF_fst (hI : I.FG) (i j : Bool × Bool) (h : i ≠ j) (h1 : i.1 ≠ j.1)
    (h2 : i.2 = j.2) :
    tateSelfProductGlueF R I q hI i j h =
      eqToHom (tateSelfProductGlueV_fst hI i j h h1 h2) ≫ firstFactorOverlapChart R I q hI := by
  rcases i with ⟨_ | _, _ | _⟩ <;> rcases j with ⟨_ | _, _ | _⟩ <;>
    first
      | exact (h rfl).elim
      | exact absurd h2 (by decide)
      | exact absurd rfl h1
      | exact (Category.id_comp _).symm

/-- **The `f` datum in the both-coordinates-differ shape.** -/
theorem tateSelfProductGlueF_both (hI : I.FG) (i j : Bool × Bool) (h : i ≠ j) (h1 : i.1 ≠ j.1)
    (h2 : i.2 ≠ j.2) :
    tateSelfProductGlueF R I q hI i j h =
      eqToHom (tateSelfProductGlueV_both hI i j h h1 h2) ≫ bothFactorOverlapChart R I q hI := by
  rcases i with ⟨_ | _, _ | _⟩ <;> rcases j with ⟨_ | _, _ | _⟩ <;>
    first
      | exact (h rfl).elim
      | exact absurd rfl h1
      | exact absurd rfl h2
      | exact (Category.id_comp _).symm

/-! ### The generic constant-datum reductions

`bothAlgDataV` and `bothAlgDataF` dispatch through `A p.1` / `gX p.1 p'.1`, and the Tate datum's
`A` and `g` are *constant* families. Reducing those redexes at the point of use is what one would
expect to do, and it does not work: see the build-cost note below. Everything is therefore reduced
here, with the constant kept as a **variable** `C` and `g`, so that the only conversion involved is
beta on a variable. Instantiating at `C := A`, `g := x + y` afterwards is substitution, not
conversion, and costs nothing.

## Build cost, measured

Instantiating `bothAlgDataV_both` at the Tate data *first* and converting the result to the annulus
spelling afterwards **does not elaborate**. Measured on a quiet box, `maxHeartbeats 200000`
(≈ 13 s) unless stated:

| conversion required of `idealOfDefinition R I X Y` | result |
| --- | --- |
| `X` only, `A p.1 ↝ A` and `g p.1 p'.1 ↝ x + y` | green |
| `Y` only | green |
| the *types* `CompletedTensorProduct R I X Y`, **both** arguments | green |
| the *ideal* `idealOfDefinition R I X Y`, **both** arguments | **timeout at `whnf`**, |
| | also at 3200000 |
| the same, factored as `(rfl : L = M).trans (rfl : M = N)` | **timeout** — `Eq.trans` needs |
| | `L`, `M`, `N` at one type, which is the same conversion again |

So it is not that the conversion is slow: converting either argument alone is cheap and converting
the underlying *type* is cheap, but converting both arguments of the *ideal* diverges. The
single-`awayCompletion` shapes (`snd`, `fst`) are unaffected, which is why only the both-factor
shape needs this treatment — but all three are done the same way here, because the uniform
statement is what the `Ψ` assembly consumes.

The rule this instance of the wall gives, worth carrying: **when a lemma is stated over a family and
the family is constant, generalise the constant to a variable before the equation, never after.**
-/

section Const

variable (R : Type u) [CommRing R] (I : Ideal R) {C : Type u} [CommRing C] [Algebra R C]

/-- `bothAlgDataV` for a constant chart family, second-coordinate-differs shape. -/
theorem bothAlgDataV_snd_const (hI : I.FG) (g : C)
    (p p' : ULift.{u} Bool × ULift.{u} Bool) (h : p ≠ p') (h1 : p.1 = p'.1) :
    bothAlgDataV (A := fun _ : ULift.{u} Bool => C) (B := fun _ : ULift.{u} Bool => C) hI
        (fun _ _ => g) (fun _ _ => g) p p' h =
      locallyRingedSpaceObj (idealOfDefinition R I C (awayCompletion (I.map (algebraMap R C)) g)) :=
  bothAlgDataV_snd hI _ _ p p' h h1

/-- `bothAlgDataV` for a constant chart family, first-coordinate-differs shape. -/
theorem bothAlgDataV_fst_const (hI : I.FG) (g : C)
    (p p' : ULift.{u} Bool × ULift.{u} Bool) (h : p ≠ p') (h1 : p.1 ≠ p'.1) (h2 : p.2 = p'.2) :
    bothAlgDataV (A := fun _ : ULift.{u} Bool => C) (B := fun _ : ULift.{u} Bool => C) hI
        (fun _ _ => g) (fun _ _ => g) p p' h =
      locallyRingedSpaceObj (idealOfDefinition R I (awayCompletion (I.map (algebraMap R C)) g) C) :=
  bothAlgDataV_fst hI _ _ p p' h h1 h2

/-- `bothAlgDataV` for a constant chart family, both-coordinates-differ shape. This is the one that
the wall above makes impossible to obtain by instantiating first. -/
theorem bothAlgDataV_both_const (hI : I.FG) (g : C)
    (p p' : ULift.{u} Bool × ULift.{u} Bool) (h : p ≠ p') (h1 : p.1 ≠ p'.1) (h2 : p.2 ≠ p'.2) :
    bothAlgDataV (A := fun _ : ULift.{u} Bool => C) (B := fun _ : ULift.{u} Bool => C) hI
        (fun _ _ => g) (fun _ _ => g) p p' h =
      locallyRingedSpaceObj (idealOfDefinition R I (awayCompletion (I.map (algebraMap R C)) g)
        (awayCompletion (I.map (algebraMap R C)) g)) :=
  bothAlgDataV_both hI _ _ p p' h h1 h2

/-- `bothAlgDataF` for a constant chart family, second-coordinate-differs shape. -/
theorem bothAlgDataF_snd_const (hI : I.FG) (g : C)
    (p p' : ULift.{u} Bool × ULift.{u} Bool) (h : p ≠ p') (h1 : p.1 = p'.1) :
    bothAlgDataF (A := fun _ : ULift.{u} Bool => C) (B := fun _ : ULift.{u} Bool => C) hI
        (fun _ _ => g) (fun _ _ => g) p p' h =
      eqToHom (bothAlgDataV_snd_const R I hI g p p' h h1) ≫
        rightInterchangeOpenImmersion (A := C) I g hI := by
  unfold bothAlgDataF
  rw [dif_pos h1]

/-- `bothAlgDataF` for a constant chart family, first-coordinate-differs shape. -/
theorem bothAlgDataF_fst_const (hI : I.FG) (g : C)
    (p p' : ULift.{u} Bool × ULift.{u} Bool) (h : p ≠ p') (h1 : p.1 ≠ p'.1) (h2 : p.2 = p'.2) :
    bothAlgDataF (A := fun _ : ULift.{u} Bool => C) (B := fun _ : ULift.{u} Bool => C) hI
        (fun _ _ => g) (fun _ _ => g) p p' h =
      eqToHom (bothAlgDataV_fst_const R I hI g p p' h h1 h2) ≫
        interchangeOpenImmersion (B := C) I g hI := by
  unfold bothAlgDataF
  rw [dif_neg h1, dif_pos h2]

/-- `bothAlgDataF` for a constant chart family, both-coordinates-differ shape. -/
theorem bothAlgDataF_both_const (hI : I.FG) (g : C)
    (p p' : ULift.{u} Bool × ULift.{u} Bool) (h : p ≠ p') (h1 : p.1 ≠ p'.1) (h2 : p.2 ≠ p'.2) :
    bothAlgDataF (A := fun _ : ULift.{u} Bool => C) (B := fun _ : ULift.{u} Bool => C) hI
        (fun _ _ => g) (fun _ _ => g) p p' h =
      eqToHom (bothAlgDataV_both_const R I hI g p p' h h1 h2) ≫
        bothInterchangeOpenImmersion (A := C) (B := C) I g g hI := by
  unfold bothAlgDataF
  rw [dif_neg h1, dif_neg h2]

end Const

variable (R I q)

/-! ### The overlap comparison isomorphism -/

/-- **The overlap comparison isomorphism.** For each pair of distinct product-index charts, the
generic (merged) overlap object `bothAlgDataV` and the Tate glue datum's (coproduct) overlap object
`tateSelfProductGlueV` are isomorphic, by 738/739's `tensorOverlapChartIso{Second,First,Both}`
according to the difference type of the pair. The two `eqToIso`s are the difference-type reductions
of the two dispatches; neither moves any ring. -/
def tateOverlapCompareIso (hq : q ∈ I) (hI : I.FG) (p p' : ULift.{u} Bool × ULift.{u} Bool)
    (h : p ≠ p') :
    bothAlgDataV (A := tateFibreA R I q) (B := tateFibreA R I q) hI
        (tateFibreG R I q) (tateFibreG R I q) p p' h ≅
      tateSelfProductGlueV R I q hI (tateFibreIdx p) (tateFibreIdx p') (tateFibreIdx_ne h) :=
  if h1 : p.1 = p'.1 then
    eqToIso (bothAlgDataV_snd_const R I hI (overlapX R I q + overlapY R I q) p p' h h1) ≪≫
      tensorOverlapChartIsoSecond R I q hq hI ≪≫
      eqToIso (tateSelfProductGlueV_snd hI _ _ (tateFibreIdx_ne h) (congrArg ULift.down h1)).symm
  else if h2 : p.2 = p'.2 then
    eqToIso (bothAlgDataV_fst_const R I hI (overlapX R I q + overlapY R I q) p p' h h1 h2) ≪≫
      tensorOverlapChartIsoFirst R I q hq hI ≪≫
      eqToIso (tateSelfProductGlueV_fst hI _ _ (tateFibreIdx_ne h)
        (fun e => h1 (ULift.ext _ _ e)) (congrArg ULift.down h2)).symm
  else
    eqToIso (bothAlgDataV_both_const R I hI (overlapX R I q + overlapY R I q) p p' h h1 h2) ≪≫
      tensorOverlapChartIsoBoth R I q hq hI ≪≫
      eqToIso (tateSelfProductGlueV_both hI _ _ (tateFibreIdx_ne h)
        (fun e => h1 (ULift.ext _ _ e)) (fun e => h2 (ULift.ext _ _ e))).symm

/-- **The overlap comparison is a morphism over the common chart** `Spf(A ⊗̂_R A)`: it carries the
Tate glue datum's overlap chart to the generic datum's overlap immersion. This is the `f` law of the
`Ψ` comparison, and it is 738/739's `…_hom_fac` in each of the three shapes — the merged chart on
the generic side *is* the `…InterchangeOpenImmersion` those lemmas produce. -/
theorem tateOverlapCompareIso_hom_fac (hq : q ∈ I) (hI : I.FG)
    (p p' : ULift.{u} Bool × ULift.{u} Bool) (h : p ≠ p') :
    (tateOverlapCompareIso R I q hq hI p p' h).hom ≫
        tateSelfProductGlueF R I q hI (tateFibreIdx p) (tateFibreIdx p') (tateFibreIdx_ne h) =
      bothAlgDataF (A := tateFibreA R I q) (B := tateFibreA R I q) hI
        (tateFibreG R I q) (tateFibreG R I q) p p' h := by
  rw [tateOverlapCompareIso]
  split_ifs with h1 h2
  · rw [tateSelfProductGlueF_snd hI _ _ (tateFibreIdx_ne h) (congrArg ULift.down h1),
      bothAlgDataF_snd_const R I hI (overlapX R I q + overlapY R I q) p p' h h1]
    simp only [Iso.trans_hom, eqToIso.hom, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
    rw [tensorOverlapChartIsoSecond_hom_fac]
  · rw [tateSelfProductGlueF_fst hI _ _ (tateFibreIdx_ne h) (fun e => h1 (ULift.ext _ _ e))
      (congrArg ULift.down h2),
      bothAlgDataF_fst_const R I hI (overlapX R I q + overlapY R I q) p p' h h1 h2]
    simp only [Iso.trans_hom, eqToIso.hom, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
    rw [tensorOverlapChartIsoFirst_hom_fac]
  · rw [tateSelfProductGlueF_both hI _ _ (tateFibreIdx_ne h) (fun e => h1 (ULift.ext _ _ e))
      (fun e => h2 (ULift.ext _ _ e)),
      bothAlgDataF_both_const R I hI (overlapX R I q + overlapY R I q) p p' h h1 h2]
    simp only [Iso.trans_hom, eqToIso.hom, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
      Category.id_comp]
    rw [tensorOverlapChartIsoBoth_hom_fac]

end AlgebraicGeometry

end
