import FormalSchemes.ChartedCompletionToScheme
import FormalSchemes.SpecThreeChartCover

set_option linter.style.header false

/-!
# The three-chart completion and its morphism to the three-chart scheme (EGA I, 10.8)

`FormalSchemes/SpecThreeChartCover.lean` presents `Spec A` by three basic opens `D(f_i)` as an
`AlgebraicGeometry.ChartedSchemeDatum` whose triple-overlap fields are derived from `tauAlg` and
`sigmaAlg` and are genuinely evaluated at the triple `0, 1, 2`. This file runs the completion side
of `FormalSchemes.ChartedCompletionDatum` at exactly that data: the glued completion of `Spec A`
along `V (I)` presented by three charts, and the canonical morphism `X_{/Y} ⟶ X` between them.

**No new algebra is needed.** The completion datum's fields are the same `tauAlg` / `sigmaAlg`
families the `Spec` side already uses, plus `hI.map _` for the finite generation of each chart
ideal — which is what `ChartedCompletionDatum` was shaped to make true, and
`completionDatum_toChartedSchemeDatum` says so on the nose.

## Why a three-chart instance and not a two-chart one

On a two-element index type no triple of indices is pairwise distinct, so `t'`, `t_fac` and
`cocycle` are `False.elim` and a construction that consumes them is never exercised. That defect
has been shipped twice on this umbrella (issue 1132 at `ULift Unit`, redone at `ULift (Fin 3)` by
1139) and the `Spec` side removed it in #462. `completionDatum_t'_zero_one_two` removes it on the
completion side.

## Main definitions and results

* `AlgebraicGeometry.SpecThreeChartCover.completionDatum`: the three-chart completion datum, with
  `..completionDatum_toChartedSchemeDatum` identifying its ambient scheme with
  `SpecThreeChartCover.datum`.
* `AlgebraicGeometry.SpecThreeChartCover.completionGlued`, `..toScheme`,
  `..completionι_comp_toScheme`: the glued completion, the canonical morphism and its computation
  rule.
* `AlgebraicGeometry.SpecThreeChartCover.completionDatum_t'_eq` and
  `..completionDatum_t'_zero_one_two`: the triple-overlap field is the derived transition, at an
  inhabited pairwise distinct triple.

## What is *not* proved

* **The completion-side triple overlap is not shown non-empty.**
  `SpecThreeChartCover.intCover_overlap_nonempty` does that for the `Spec` side at `ℤ` with
  `D(2)`, `D(3)`, `D(5)`; the corresponding statement for `Spf` of the completed triple-overlap
  ring is a separate computation and is not made here. The concrete example below is at
  `I = (7)`, chosen so that `7` stays a non-unit in every chart and every overlap of that cover,
  which is the arithmetic precondition such a statement would need; it is not itself that
  statement.
* Nothing here says the three charts *cover* `Spec A` — that needs `Ideal.span {f₀, f₁, f₂} = ⊤`
  and is issue 60s's business, not this file's.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

namespace SpecThreeChartCover

variable {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG) (f : ULift.{u} (Fin 3) → A)

/-- **The three-chart datum, with its ideals' finite generation.** The charts are the three basic
opens `D(f_i)` of `Spec A`, the ideals are `I·A_{f_i}`, and the two transition families are
`SpecThreeChartCover.tauAlg` and `SpecThreeChartCover.sigmaAlg` — the very data
`AlgebraicGeometry.ChartedSchemeDatum.ofAlgebraData` consumes, which is why the completion side
needs no new input. -/
def completionDatum : ChartedCompletionDatum.{u} where
  J := ULift.{u} (Fin 3)
  C := chartRing f
  K := fun i => I.map (algebraMap A (chartRing f i))
  hK := fun _ => hI.map _
  g := overlapElt f
  θ := fun i j _ => (tauAlg f i j).toRingEquiv
  θ_symm := fun i j _ => tauAlg_symm f i j
  hθ := fun i j _ => tauAlg_map_ideal I f i j
  σ := fun i j k _ _ _ => (sigmaAlg f i j k).toRingEquiv
  hσθ := fun i j k _ _ _ => sigmaAlg_tauAlg f i j k
  hσc := fun i j k _ _ _ => sigmaAlg_cocycle f i j k

/-- **The ambient scheme of the completion datum is the three-chart scheme**, on the nose: the
completion datum's `toChartedSchemeDatum` is `SpecThreeChartCover.datum`, because both are
`ofAlgebraData` at the same arguments. -/
theorem completionDatum_toChartedSchemeDatum :
    (completionDatum I hI f).toChartedSchemeDatum = datum I f :=
  rfl

/-- **The glued completion of `Spec A` along `V (I)`, presented by three charts.** -/
def completionGlued : FormalScheme.{u} := (completionDatum I hI f).completionGlued

/-- **The canonical morphism `X_{/Y} ⟶ X` for the three-chart presentation.** -/
def toScheme : (completionGlued I hI f).toLocallyRingedSpace ⟶ glued I f :=
  (completionDatum I hI f).toScheme

/-- **The computation rule for the three-chart morphism**: on the `i`-th chart it is the affine
`formalCompletion.toSpec` followed by the `i`-th chart of the glued scheme. -/
theorem completionι_comp_toScheme (i : ULift.{u} (Fin 3)) :
    (completionDatum I hI f).completionι i ≫ toScheme I hI f =
      formalCompletion.toSpec (chartRing f i) (I.map (algebraMap A (chartRing f i))) (hI.map _) ≫
        (completionDatum I hI f).specι i :=
  (completionDatum I hI f).completionι_comp_toScheme i

/-! ### Non-vacuity -/

/-- Distinct elements of `Fin 3` stay distinct after `ULift.up`. Restated here rather than imported:
`FormalSchemes/SpecThreeChartCover.lean`'s copy is `private`, and its docstring records that the
tree
has eleven copies of this shape, one per file that needs it. -/
private theorem up_ne_up_of_ne {a b : Fin 3} (h : a ≠ b) : (⟨a⟩ : ULift.{u} (Fin 3)) ≠ ⟨b⟩ :=
  fun hh => h (congrArg ULift.down hh)

/-- **Non-vacuity of the completion side's triple-overlap field, in general.** At a pairwise
distinct triple the glue datum's `t'` is the derived transition of
`ChartedCompletionDatum.tripleTransition`, not `False.elim`. -/
theorem completionDatum_t'_eq (i j k : ULift.{u} (Fin 3)) (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) :
    (completionDatum I hI f).completionGlueData'.t' i j k hij hik hjk =
      (completionDatum I hI f).tripleTransition i j k hij hik hjk :=
  rfl

/-- **Non-vacuity, at the inhabited triple `0, 1, 2`.** This is the statement the two-patch
completion cannot make: the triple exists, so the field is genuinely evaluated. -/
theorem completionDatum_t'_zero_one_two :
    (completionDatum I hI f).completionGlueData'.t' ⟨0⟩ ⟨1⟩ ⟨2⟩ (up_ne_up_of_ne (by decide))
        (up_ne_up_of_ne (by decide)) (up_ne_up_of_ne (by decide)) =
      (completionDatum I hI f).tripleTransition ⟨0⟩ ⟨1⟩ ⟨2⟩ (up_ne_up_of_ne (by decide))
        (up_ne_up_of_ne (by decide)) (up_ne_up_of_ne (by decide)) :=
  rfl

/-- `(7 : ℤ)` generates a finitely generated ideal, by exhibiting the generating finset. -/
private theorem fg_span_seven : (Ideal.span {(7 : ℤ)}).FG := ⟨{7}, by simp⟩

/-- **The whole construction at a concrete base**: `Spec ℤ` covered by `D(2)`, `D(3)`, `D(5)`,
completed along `V (7)`. The ideal is finitely generated, the index type has a pairwise distinct
triple, and `SpecThreeChartCover.intCover_overlap_nonempty` shows the `Spec`-side double overlap
that `t'` transports is not empty. -/
example : (completionGlued (Ideal.span {(7 : ℤ)}) (fg_span_seven)
    intCover).toLocallyRingedSpace ⟶
      glued (Ideal.span {(7 : ℤ)}) intCover :=
  toScheme (Ideal.span {(7 : ℤ)}) (fg_span_seven) intCover

end SpecThreeChartCover

end AlgebraicGeometry

end
