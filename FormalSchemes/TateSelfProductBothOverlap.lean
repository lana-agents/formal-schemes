import FormalSchemes.OpenImmersionIsoOfRangeEq
import FormalSchemes.TateSelfProductRightOverlap
import FormalSchemes.CompletedTensorAwayInterchangeBoth

set_option linter.style.header false
-- The completed-tensor interchange morphisms range over the nested localization/completion
-- towers of the completed tensor product, which are slow for the elaborator and the kernel;
-- raise the budgets (matching `TateSelfProductOverlap.lean`).
set_option linter.style.setOption false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The both-factors-differing overlap chart of the Tate self-fibre-product

Fix an adic base `(R, I)` with `q ∈ I` (the Tate parameter is topologically nilpotent) and finitely
generated `I`, and let `A = annulusAlgebra R I q = R{x, y}/(x·y − q)` be the coordinate ring of the
formal Tate annulus. This file assembles the **both-factors-differing overlap chart** of the self
fibre-product `𝔈_q ×_{Spf R} 𝔈_q`, completing the trio of overlap objects begun in
`FormalSchemes.TateSelfProductOverlap` (first factor differs) and
`FormalSchemes.TateSelfProductRightOverlap` (second factor differs).

The two-chart Tate curve model `𝔈_q = tateCurveModel` is glued from `Spf A` on the index
`ULift Bool`, its two charts overlapping on the `𝔾̂m`-locus `Spf A{1/x} ⊔ Spf A{1/y}` (coordinates
`x` vs `y`). In the self fibre-product, the overlap between two charts whose *both* factors differ
is the product of the two `𝔾̂m`-overlaps; distributing the fibre product over the coproduct
decomposes it into **four** pieces `Spf((A{1/a}) ⊗̂_R (A{1/b}))`, `a, b ∈ {x, y}`, glued into
`Spf(A ⊗̂_R A)`
via the both-localized interchange open immersions (`CompletedTensorAwayInterchangeBoth`), whose
images are the intersections `D(inl a) ⊓ D(inr b)`.

Because `x · y = q` with `q ∈ I` topologically nilpotent forces `D(inl x) ⊓ D(inl y) = ⊥` (first
factor) and `D(inr x) ⊓ D(inr y) = ⊥` (second factor), the four ranges `D(inl a) ⊓ D(inr b)` are
pairwise disjoint: two distinct index pairs `(a, b) ≠ (a', b')` differ in the first coordinate
(disjoint via `inl`) or the second (disjoint via `inr`). Hence the nested coproduct

`coprod.desc (coprod.desc f_xx f_xy) (coprod.desc f_yx f_yy) : (… ⨿ …) ⨿ (… ⨿ …) ⟶ Spf(A ⊗̂_R A)`

of the four charts is an open immersion. This is the `V`/`f` overlap datum (for the
both-factors-differing chart shape) that the eventual four-chart glue of `𝔈_q ×_{Spf R} 𝔈_q`
consumes, alongside the first-factor datum of `TateSelfProductOverlap` and the second-factor datum
of `TateSelfProductRightOverlap`.

## Main results

* `AlgebraicGeometry.isOpenImmersion_tateSelfProductBothOverlapChart`: the nested four-chart
  coproduct chart into `Spf(A ⊗̂_R A)` is an open immersion.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7, §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7, §10.13.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
  CompletedTensorAwayInterchange

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- The coordinate ring of the formal Tate annulus, base for the self fibre-product. -/
private abbrev A : Type u := annulusAlgebra R I q

/-- **Two both-localized charts sharing their first coordinate have disjoint ranges.** For a fixed
`a ∈ A`, the two charts `bothInterchangeOpenImmersion I a x` (range `D(inl a) ⊓ D(inr x)`) and
`bothInterchangeOpenImmersion I a y` (range `D(inl a) ⊓ D(inr y)`) into `Spf(A ⊗̂_R A)` have
disjoint underlying-space ranges when `q ∈ I`, because the second-coordinate loci `D(inr x)` and
`D(inr y)`
are disjoint (`selfProductRightOverlap_basicOpen_disjoint`). -/
private theorem bothChart_range_disjoint_inr (a : A R I q) (hq : q ∈ I) (hI : I.FG) :
    Disjoint
      (Set.range (bothInterchangeOpenImmersion
        (A := A R I q) (B := A R I q) I a (overlapX R I q) hI).base)
      (Set.range (bothInterchangeOpenImmersion
        (A := A R I q) (B := A R I q) I a (overlapY R I q) hI).base) := by
  rw [range_bothInterchangeOpenImmersion_base, range_bothInterchangeOpenImmersion_base]
  have hdisj : Disjoint
      ((FormalSpectrum.basicOpen (CompletedTensorProduct.idealOfDefinition R I (A R I q) (A R I q))
          (CompletedTensorProduct.inr R I (A R I q) (A R I q) (overlapX R I q)) :
            Set (FormalSpectrum (CompletedTensorProduct.idealOfDefinition R I
              (A R I q) (A R I q)))))
      (FormalSpectrum.basicOpen (CompletedTensorProduct.idealOfDefinition R I (A R I q) (A R I q))
          (CompletedTensorProduct.inr R I (A R I q) (A R I q) (overlapY R I q))) := by
    rw [Set.disjoint_iff_inter_eq_empty, ← TopologicalSpace.Opens.coe_inf,
      selfProductRightOverlap_basicOpen_disjoint R I q hq, TopologicalSpace.Opens.coe_bot]
  refine Set.disjoint_of_subset ?_ ?_ hdisj
  · rw [TopologicalSpace.Opens.coe_inf]; exact Set.inter_subset_right
  · rw [TopologicalSpace.Opens.coe_inf]; exact Set.inter_subset_right

/-- **The `a = x` and `a = y` inner overlap charts have disjoint ranges.** The two inner coproduct
charts `coprod.desc f_xx f_xy` (range contained in the first-coordinate locus `D(inl x)`) and
`coprod.desc f_yx f_yy` (range contained in `D(inl y)`) into `Spf(A ⊗̂_R A)` have disjoint
underlying-space ranges when `q ∈ I`, because `D(inl x)` and `D(inl y)` are disjoint
(`selfProductOverlap_basicOpen_disjoint`). This is the disjointness feeding the *outer*
`coprod.desc` of the four-chart overlap object. -/
private theorem innerChart_range_disjoint (hq : q ∈ I) (hI : I.FG) :
    Disjoint
      (Set.range (coprod.desc
        (bothInterchangeOpenImmersion (A := A R I q) (B := A R I q) I
          (overlapX R I q) (overlapX R I q) hI)
        (bothInterchangeOpenImmersion (A := A R I q) (B := A R I q) I
          (overlapX R I q) (overlapY R I q) hI)).base)
      (Set.range (coprod.desc
        (bothInterchangeOpenImmersion (A := A R I q) (B := A R I q) I
          (overlapY R I q) (overlapX R I q) hI)
        (bothInterchangeOpenImmersion (A := A R I q) (B := A R I q) I
          (overlapY R I q) (overlapY R I q) hI)).base) := by
  have hsub_x : Set.range (coprod.desc
        (bothInterchangeOpenImmersion (A := A R I q) (B := A R I q) I
          (overlapX R I q) (overlapX R I q) hI)
        (bothInterchangeOpenImmersion (A := A R I q) (B := A R I q) I
          (overlapX R I q) (overlapY R I q) hI)).base ⊆
      (FormalSpectrum.basicOpen (CompletedTensorProduct.idealOfDefinition R I (A R I q) (A R I q))
          (CompletedTensorProduct.inl R I (A R I q) (A R I q) (overlapX R I q)) :
            Set (FormalSpectrum (CompletedTensorProduct.idealOfDefinition R I
              (A R I q) (A R I q)))) := by
    rw [LocallyRingedSpace.range_coprodDesc_base]
    refine Set.union_subset ?_ ?_ <;>
      · rw [range_bothInterchangeOpenImmersion_base, TopologicalSpace.Opens.coe_inf]
        exact Set.inter_subset_left
  have hsub_y : Set.range (coprod.desc
        (bothInterchangeOpenImmersion (A := A R I q) (B := A R I q) I
          (overlapY R I q) (overlapX R I q) hI)
        (bothInterchangeOpenImmersion (A := A R I q) (B := A R I q) I
          (overlapY R I q) (overlapY R I q) hI)).base ⊆
      (FormalSpectrum.basicOpen (CompletedTensorProduct.idealOfDefinition R I (A R I q) (A R I q))
          (CompletedTensorProduct.inl R I (A R I q) (A R I q) (overlapY R I q)) :
            Set (FormalSpectrum (CompletedTensorProduct.idealOfDefinition R I
              (A R I q) (A R I q)))) := by
    rw [LocallyRingedSpace.range_coprodDesc_base]
    refine Set.union_subset ?_ ?_ <;>
      · rw [range_bothInterchangeOpenImmersion_base, TopologicalSpace.Opens.coe_inf]
        exact Set.inter_subset_left
  have hdisj : Disjoint
      ((FormalSpectrum.basicOpen (CompletedTensorProduct.idealOfDefinition R I (A R I q) (A R I q))
          (CompletedTensorProduct.inl R I (A R I q) (A R I q) (overlapX R I q)) :
            Set (FormalSpectrum (CompletedTensorProduct.idealOfDefinition R I
              (A R I q) (A R I q)))))
      (FormalSpectrum.basicOpen (CompletedTensorProduct.idealOfDefinition R I (A R I q) (A R I q))
          (CompletedTensorProduct.inl R I (A R I q) (A R I q) (overlapY R I q))) := by
    rw [Set.disjoint_iff_inter_eq_empty, ← TopologicalSpace.Opens.coe_inf,
      selfProductOverlap_basicOpen_disjoint R I q hq, TopologicalSpace.Opens.coe_bot]
  exact Set.disjoint_of_subset hsub_x hsub_y hdisj

/-- **The four-chart both-factors-differing overlap chart is an open immersion.** The nested
coproduct `coprod.desc (coprod.desc f_xx f_xy) (coprod.desc f_yx f_yy)` of the four both-localized
interchange charts `f_ab = bothInterchangeOpenImmersion I a b`, `a, b ∈ {x, y}` (each with range
`D(inl a) ⊓ D(inr b) ⊆ Spf(A ⊗̂_R A)`), is an open immersion of locally ringed spaces, because the
four ranges are pairwise disjoint: the two inner coproducts pair up the charts that share a first
coordinate (disjoint via the second coordinate `inr`), and the outer coproduct separates the two
first coordinates (disjoint via `inl`). This is the `V`/`f` overlap datum (for the
both-factors-differing chart shape) feeding the eventual four-chart glue of the self fibre-product
`𝔈_q ×_{Spf R} 𝔈_q`. -/
theorem isOpenImmersion_tateSelfProductBothOverlapChart (hq : q ∈ I) (hI : I.FG) :
    LocallyRingedSpace.IsOpenImmersion
      (coprod.desc
        (coprod.desc
          (bothInterchangeOpenImmersion (A := A R I q) (B := A R I q) I
            (overlapX R I q) (overlapX R I q) hI)
          (bothInterchangeOpenImmersion (A := A R I q) (B := A R I q) I
            (overlapX R I q) (overlapY R I q) hI))
        (coprod.desc
          (bothInterchangeOpenImmersion (A := A R I q) (B := A R I q) I
            (overlapY R I q) (overlapX R I q) hI)
          (bothInterchangeOpenImmersion (A := A R I q) (B := A R I q) I
            (overlapY R I q) (overlapY R I q) hI))) := by
  haveI := isOpenImmersion_bothInterchangeOpenImmersion (A := A R I q) (B := A R I q) I
    (overlapX R I q) (overlapX R I q) hI
  haveI := isOpenImmersion_bothInterchangeOpenImmersion (A := A R I q) (B := A R I q) I
    (overlapX R I q) (overlapY R I q) hI
  haveI := isOpenImmersion_bothInterchangeOpenImmersion (A := A R I q) (B := A R I q) I
    (overlapY R I q) (overlapX R I q) hI
  haveI := isOpenImmersion_bothInterchangeOpenImmersion (A := A R I q) (B := A R I q) I
    (overlapY R I q) (overlapY R I q) hI
  haveI : LocallyRingedSpace.IsOpenImmersion
      (coprod.desc
        (bothInterchangeOpenImmersion (A := A R I q) (B := A R I q) I
          (overlapX R I q) (overlapX R I q) hI)
        (bothInterchangeOpenImmersion (A := A R I q) (B := A R I q) I
          (overlapX R I q) (overlapY R I q) hI)) :=
    LocallyRingedSpace.IsOpenImmersion.coprodDesc _ _
      (bothChart_range_disjoint_inr R I q (overlapX R I q) hq hI)
  haveI : LocallyRingedSpace.IsOpenImmersion
      (coprod.desc
        (bothInterchangeOpenImmersion (A := A R I q) (B := A R I q) I
          (overlapY R I q) (overlapX R I q) hI)
        (bothInterchangeOpenImmersion (A := A R I q) (B := A R I q) I
          (overlapY R I q) (overlapY R I q) hI)) :=
    LocallyRingedSpace.IsOpenImmersion.coprodDesc _ _
      (bothChart_range_disjoint_inr R I q (overlapY R I q) hq hI)
  exact LocallyRingedSpace.IsOpenImmersion.coprodDesc _ _
    (innerChart_range_disjoint R I q hq hI)

end AlgebraicGeometry
