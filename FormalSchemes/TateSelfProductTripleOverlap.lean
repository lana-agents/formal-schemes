import FormalSchemes.TateSelfProductBothOverlap
import FormalSchemes.PullbackRangeLRS

set_option linter.style.header false
-- The completed-tensor interchange morphisms range over the nested localization/completion
-- towers of the completed tensor product, which are slow for the elaborator and the kernel;
-- raise the budgets (matching `TateSelfProductBothOverlap.lean`).
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Triple overlaps of the four-chart Tate self-fibre-product glue

Fix an adic base `(R, I)` with `q ∈ I` finitely generated, `A = annulusAlgebra R I q`, and
`C = A ⊗̂_R A`. The self fibre-product `𝔈_q ×_{Spf R} 𝔈_q` is a **four-chart** glue whose charts are
four copies of `Spf C` indexed by `Bool × Bool`. Fixing one source chart, the three overlap charts
`f i j : V i j ⟶ U i` toward the three other charts are exactly the coproduct overlap charts merged
in `TateSelfProduct{,Right,Both}Overlap`:

* `firstFactorOverlapChart` — first factor differs: `Spf(A{1/x}⊗̂A) ⨿ Spf(A{1/y}⊗̂A) ⟶ Spf C`,
  range `D(x⊗1) ∪ D(y⊗1)`;
* `secondFactorOverlapChart` — second factor differs: `Spf(A⊗̂A{1/x}) ⨿ Spf(A⊗̂A{1/y}) ⟶ Spf C`,
  range `D(1⊗x) ∪ D(1⊗y)`;
* `bothFactorOverlapChart` — both factors differ: the nested 4-fold coproduct, range
  `⋃_{a,b∈{x,y}} (D(a⊗1) ⊓ D(1⊗b))`.

The genuine `Bool × Bool` cocycle of the glue is built from the triple-overlap pullbacks
`pullback (f i j) (f i k)` for pairwise distinct charts. Because the `f i j` are open immersions,
each such pullback is computed **by range** (`PullbackRangeLRS`): its range is
`range (f i j) ∩ range (f i k)`, and the concrete both-overlap object realises exactly that
intersection, so the two are canonically isomorphic. This file records those three identifications —
the geometric input the cocycle construction consumes, reducing it to summand tracking through the
`coprod.desc` isos rather than an explicit completed-tensor associativity computation.

## Main results

* `range_firstFactorOverlapChart`, `range_secondFactorOverlapChart`, `range_bothFactorOverlapChart`:
  the underlying-space ranges of the three overlap charts, as unions of basic opens.
* `range_bothFactorOverlapChart_eq_inter_first_second`: the both-overlap range is the intersection
  of the first- and second-factor overlap ranges (pure distributivity of `∪`/`∩`).
* `firstSecondTripleOverlapIso`, `firstBothTripleOverlapIso`, `secondBothTripleOverlapIso`: each
  triple-overlap pullback of two of the three charts is canonically isomorphic to the both-overlap
  object, via `pullbackIsoOfRangeEq`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* Mathlib `AlgebraicGeometry.Scheme.Pullback` (the scheme-level analogue of the glue cocycle).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
  CompletedTensorAwayInterchange

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-! ### The three overlap charts, named -/

/-- **First-factor overlap chart** `Spf(A{1/x}⊗̂A) ⨿ Spf(A{1/y}⊗̂A) ⟶ Spf C`: the combined chart of
the one-factor-differing overlap shape, whose open-immersion property is
`isOpenImmersion_tateSelfProductOverlapChart`. -/
def firstFactorOverlapChart (hI : I.FG) :=
  coprod.desc
    (interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapX R I q) hI)
    (interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapY R I q) hI)

/-- **Second-factor overlap chart** `Spf(A⊗̂A{1/x}) ⨿ Spf(A⊗̂A{1/y}) ⟶ Spf C`: the combined chart of
the second-factor-differing overlap shape, whose open-immersion property is
`isOpenImmersion_tateSelfProductRightOverlapChart`. -/
def secondFactorOverlapChart (hI : I.FG) :=
  coprod.desc
    (rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapX R I q) hI)
    (rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapY R I q) hI)

/-- **Both-factor overlap chart**: the nested 4-fold coproduct
`coprod.desc (coprod.desc f_xx f_xy) (coprod.desc f_yx f_yy) ⟶ Spf C` of the both-localized charts,
whose open-immersion property is `isOpenImmersion_tateSelfProductBothOverlapChart`. -/
def bothFactorOverlapChart (hI : I.FG) :=
  coprod.desc
    (coprod.desc
      (bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I
        (overlapX R I q) (overlapX R I q) hI)
      (bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I
        (overlapX R I q) (overlapY R I q) hI))
    (coprod.desc
      (bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I
        (overlapY R I q) (overlapX R I q) hI)
      (bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I
        (overlapY R I q) (overlapY R I q) hI))

theorem isOpenImmersion_firstFactorOverlapChart (hq : q ∈ I) (hI : I.FG) :
    LocallyRingedSpace.IsOpenImmersion (firstFactorOverlapChart R I q hI) :=
  isOpenImmersion_tateSelfProductOverlapChart R I q hq hI

theorem isOpenImmersion_secondFactorOverlapChart (hq : q ∈ I) (hI : I.FG) :
    LocallyRingedSpace.IsOpenImmersion (secondFactorOverlapChart R I q hI) :=
  isOpenImmersion_tateSelfProductRightOverlapChart R I q hq hI

theorem isOpenImmersion_bothFactorOverlapChart (hq : q ∈ I) (hI : I.FG) :
    LocallyRingedSpace.IsOpenImmersion (bothFactorOverlapChart R I q hI) :=
  isOpenImmersion_tateSelfProductBothOverlapChart R I q hq hI

/-! ### The ranges of the three overlap charts -/

/-- The range of the first-factor overlap chart is `D(x⊗1) ∪ D(y⊗1)`. -/
theorem range_firstFactorOverlapChart (hI : I.FG) :
    Set.range (firstFactorOverlapChart R I q hI).base =
      (↑(FormalSpectrum.basicOpen
          (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
            (annulusAlgebra R I q))
          (CompletedTensorProduct.inl R I (annulusAlgebra R I q) (annulusAlgebra R I q)
            (overlapX R I q))) ∪
        ↑(FormalSpectrum.basicOpen
          (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
            (annulusAlgebra R I q))
          (CompletedTensorProduct.inl R I (annulusAlgebra R I q) (annulusAlgebra R I q)
            (overlapY R I q))) :
        Set (FormalSpectrum (CompletedTensorProduct.idealOfDefinition R I
          (annulusAlgebra R I q) (annulusAlgebra R I q)))) := by
  rw [firstFactorOverlapChart, range_coprodDesc_base]
  refine congrArg₂ (· ∪ ·) ?_ ?_
  · exact range_interchangeOpenImmersion_base (B := annulusAlgebra R I q) I (overlapX R I q) hI
  · exact range_interchangeOpenImmersion_base (B := annulusAlgebra R I q) I (overlapY R I q) hI

/-- The range of the second-factor overlap chart is `D(1⊗x) ∪ D(1⊗y)`. -/
theorem range_secondFactorOverlapChart (hI : I.FG) :
    Set.range (secondFactorOverlapChart R I q hI).base =
      (↑(FormalSpectrum.basicOpen
          (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
            (annulusAlgebra R I q))
          (CompletedTensorProduct.inr R I (annulusAlgebra R I q) (annulusAlgebra R I q)
            (overlapX R I q))) ∪
        ↑(FormalSpectrum.basicOpen
          (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
            (annulusAlgebra R I q))
          (CompletedTensorProduct.inr R I (annulusAlgebra R I q) (annulusAlgebra R I q)
            (overlapY R I q))) :
        Set (FormalSpectrum (CompletedTensorProduct.idealOfDefinition R I
          (annulusAlgebra R I q) (annulusAlgebra R I q)))) := by
  rw [secondFactorOverlapChart, range_coprodDesc_base]
  refine congrArg₂ (· ∪ ·) ?_ ?_
  · exact range_rightInterchangeOpenImmersion_base (A := annulusAlgebra R I q) I (overlapX R I q) hI
  · exact range_rightInterchangeOpenImmersion_base (A := annulusAlgebra R I q) I (overlapY R I q) hI

/-- The range of the both-factor overlap chart is `⋃_{a,b∈{x,y}} (D(a⊗1) ⊓ D(1⊗b))`, the nested
union of the four intersections `D(inl a) ⊓ D(inr b)`. -/
theorem range_bothFactorOverlapChart (hI : I.FG) :
    Set.range (bothFactorOverlapChart R I q hI).base =
      ((↑(FormalSpectrum.basicOpen
              (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
                (annulusAlgebra R I q))
              (CompletedTensorProduct.inl R I (annulusAlgebra R I q) (annulusAlgebra R I q)
                (overlapX R I q)) ⊓
            FormalSpectrum.basicOpen
              (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
                (annulusAlgebra R I q))
              (CompletedTensorProduct.inr R I (annulusAlgebra R I q) (annulusAlgebra R I q)
                (overlapX R I q))) ∪
          ↑(FormalSpectrum.basicOpen
              (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
                (annulusAlgebra R I q))
              (CompletedTensorProduct.inl R I (annulusAlgebra R I q) (annulusAlgebra R I q)
                (overlapX R I q)) ⊓
            FormalSpectrum.basicOpen
              (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
                (annulusAlgebra R I q))
              (CompletedTensorProduct.inr R I (annulusAlgebra R I q) (annulusAlgebra R I q)
                (overlapY R I q)))) ∪
        (↑(FormalSpectrum.basicOpen
              (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
                (annulusAlgebra R I q))
              (CompletedTensorProduct.inl R I (annulusAlgebra R I q) (annulusAlgebra R I q)
                (overlapY R I q)) ⊓
            FormalSpectrum.basicOpen
              (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
                (annulusAlgebra R I q))
              (CompletedTensorProduct.inr R I (annulusAlgebra R I q) (annulusAlgebra R I q)
                (overlapX R I q))) ∪
          ↑(FormalSpectrum.basicOpen
              (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
                (annulusAlgebra R I q))
              (CompletedTensorProduct.inl R I (annulusAlgebra R I q) (annulusAlgebra R I q)
                (overlapY R I q)) ⊓
            FormalSpectrum.basicOpen
              (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q)
                (annulusAlgebra R I q))
              (CompletedTensorProduct.inr R I (annulusAlgebra R I q) (annulusAlgebra R I q)
                (overlapY R I q)))) :
        Set (FormalSpectrum (CompletedTensorProduct.idealOfDefinition R I
          (annulusAlgebra R I q) (annulusAlgebra R I q)))) := by
  rw [bothFactorOverlapChart, range_coprodDesc_base, range_coprodDesc_base, range_coprodDesc_base]
  refine congrArg₂ (· ∪ ·) (congrArg₂ (· ∪ ·) ?_ ?_) (congrArg₂ (· ∪ ·) ?_ ?_)
  · exact range_bothInterchangeOpenImmersion_base (A := annulusAlgebra R I q)
      (B := annulusAlgebra R I q) I (overlapX R I q) (overlapX R I q) hI
  · exact range_bothInterchangeOpenImmersion_base (A := annulusAlgebra R I q)
      (B := annulusAlgebra R I q) I (overlapX R I q) (overlapY R I q) hI
  · exact range_bothInterchangeOpenImmersion_base (A := annulusAlgebra R I q)
      (B := annulusAlgebra R I q) I (overlapY R I q) (overlapX R I q) hI
  · exact range_bothInterchangeOpenImmersion_base (A := annulusAlgebra R I q)
      (B := annulusAlgebra R I q) I (overlapY R I q) (overlapY R I q) hI

/-! ### The triple-overlap range identity and the pullback identifications -/

/-- The both-overlap range is contained in the first-factor overlap range: every summand
`D(inl a) ⊓ D(inr b)` sits inside `D(inl a) ⊆ D(inl x) ∪ D(inl y)`. Proved by destructuring the
four-fold union membership (definitional), avoiding the `FormalSpectrum`/carrier friction that
`simp` and `rw` stumble on here. -/
theorem range_bothFactorOverlapChart_subset_first (hI : I.FG) :
    Set.range (bothFactorOverlapChart R I q hI).base ⊆
      Set.range (firstFactorOverlapChart R I q hI).base := by
  rw [range_bothFactorOverlapChart, range_firstFactorOverlapChart]
  rintro x (((h | h) | h | h))
  · exact Or.inl h.1
  · exact Or.inl h.1
  · exact Or.inr h.1
  · exact Or.inr h.1

/-- The both-overlap range is contained in the second-factor overlap range: every summand
`D(inl a) ⊓ D(inr b)` sits inside `D(inr b) ⊆ D(inr x) ∪ D(inr y)`. -/
theorem range_bothFactorOverlapChart_subset_second (hI : I.FG) :
    Set.range (bothFactorOverlapChart R I q hI).base ⊆
      Set.range (secondFactorOverlapChart R I q hI).base := by
  rw [range_bothFactorOverlapChart, range_secondFactorOverlapChart]
  rintro x (((h | h) | h | h))
  · exact Or.inl h.2
  · exact Or.inr h.2
  · exact Or.inl h.2
  · exact Or.inr h.2

/-- **The key distributivity:** the both-overlap range equals the intersection of the first- and
second-factor overlap ranges: `(D(x⊗1)∪D(y⊗1)) ∩ (D(1⊗x)∪D(1⊗y)) = ⋃_{a,b}(D(a⊗1)⊓D(1⊗b))`. The
`⊆` direction is the two containments above; the `⊇` direction distributes the intersection of the
two two-fold unions over the four summands, by destructuring the membership (definitional). -/
theorem range_bothFactorOverlapChart_eq_inter_first_second (hI : I.FG) :
    Set.range (bothFactorOverlapChart R I q hI).base =
      Set.range (firstFactorOverlapChart R I q hI).base ∩
        Set.range (secondFactorOverlapChart R I q hI).base := by
  apply Set.Subset.antisymm
  · exact Set.subset_inter (range_bothFactorOverlapChart_subset_first R I q hI)
      (range_bothFactorOverlapChart_subset_second R I q hI)
  · rw [range_bothFactorOverlapChart, range_firstFactorOverlapChart,
      range_secondFactorOverlapChart]
    rintro x ⟨h1, h2⟩
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact Or.inl (Or.inl ⟨h1, h2⟩)
    · exact Or.inl (Or.inr ⟨h1, h2⟩)
    · exact Or.inr (Or.inl ⟨h1, h2⟩)
    · exact Or.inr (Or.inr ⟨h1, h2⟩)

/-- **First–second triple overlap.** The pullback of the first- and second-factor overlap charts is
canonically isomorphic to the both-overlap object, since its range is exactly their intersection. -/
def firstSecondTripleOverlapIso (hq : q ∈ I) (hI : I.FG) :=
  letI := isOpenImmersion_firstFactorOverlapChart R I q hq hI
  letI := isOpenImmersion_secondFactorOverlapChart R I q hq hI
  letI := isOpenImmersion_bothFactorOverlapChart R I q hq hI
  LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq
    (firstFactorOverlapChart R I q hI) (secondFactorOverlapChart R I q hI)
    (bothFactorOverlapChart R I q hI)
    (range_bothFactorOverlapChart_eq_inter_first_second R I q hI)

/-- **First–both triple overlap.** The pullback of the first-factor and both-factor overlap charts
is canonically isomorphic to the both-overlap object, since the both-overlap range is contained in
the first-factor range. -/
def firstBothTripleOverlapIso (hq : q ∈ I) (hI : I.FG) :=
  letI := isOpenImmersion_firstFactorOverlapChart R I q hq hI
  letI := isOpenImmersion_bothFactorOverlapChart R I q hq hI
  LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq
    (firstFactorOverlapChart R I q hI) (bothFactorOverlapChart R I q hI)
    (bothFactorOverlapChart R I q hI)
    (Set.inter_eq_right.mpr (range_bothFactorOverlapChart_subset_first R I q hI)).symm

/-- **Second–both triple overlap.** The pullback of the second-factor and both-factor overlap charts
is canonically isomorphic to the both-overlap object, since the both-overlap range is contained in
the second-factor range. -/
def secondBothTripleOverlapIso (hq : q ∈ I) (hI : I.FG) :=
  letI := isOpenImmersion_secondFactorOverlapChart R I q hq hI
  letI := isOpenImmersion_bothFactorOverlapChart R I q hq hI
  LocallyRingedSpace.IsOpenImmersion.pullbackIsoOfRangeEq
    (secondFactorOverlapChart R I q hI) (bothFactorOverlapChart R I q hI)
    (bothFactorOverlapChart R I q hI)
    (Set.inter_eq_right.mpr (range_bothFactorOverlapChart_subset_second R I q hI)).symm

end AlgebraicGeometry
