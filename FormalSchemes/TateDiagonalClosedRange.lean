import FormalSchemes.TateDiagonalPreimageBounds
import FormalSchemes.TateMixedChartDescent

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000
set_option maxRecDepth 8000

/-!
# Global closedness of the range of the Tate self-product diagonal

Fix an adic base `(R, I)` with `I` finitely generated and a Tate parameter `q ∈ I`. Over the
*corrected* (𝔾m-inversion, Néron 2-gon) model of the Tate curve `𝔈_q`, the glued diagonal

```
Δ : 𝔈_q ⟶ 𝔈_q ×_{Spf R} 𝔈_q
```

has **closed range**, so (being a topological embedding as a section of `pr₁`) it is a **closed
topological embedding**. This is the global (route b) form of the separatedness input of EGA I
§10.15: it collapses the per-chart bricks 424/425 into a single global fact, from which the
per-chart `restrictPreimage` closed-embedding statements follow immediately by
`Set.restrictPreimage_isClosedEmbedding`.

## Strategy

Closedness of `range Δ.base` is checked local-at-target along the four-chart open cover
`tateSelfProductChartCover` (`IsOpenCover.isClosed_iff_coe_preimage`):

* on the two **diagonal** charts `(b, b)` the coe-preimage of `range Δ.base` is closed because
  `restrictPreimage_diagonal_diagChart` already exhibits the chart restriction of `Δ.base` as a
  closed embedding, whose range is exactly that coe-preimage;
* on the two **mixed** charts `(b, ¬b)` the coe-preimage is the union of the two graph pieces
  `Q_x ∪ Q_y` — the graphs of the 𝔾m-inversion transition on the two annulus overlaps — each of
  which is the range of `Spf` of a surjective graph codiagonal (`graphCodiag{X,Y}`), hence closed.

The mixed-chart set equality is the content of `preimage_range_diagonal_ft` / `_tf`. Its `⊇` half
is on master (`range_spfGraphCodiag*_subset`). Its `⊆` half runs, for each of the two diagonal
charts `(c, c)` the mixed chart meets and each of the two summands of the corresponding overlap
object:

1. descend the point into the overlap summand (`mixedChartSplit_*`);
2. bound the preimage of the affine diagonal locus under that summand's transition composite by the
   range of the summand's graph lift (`spfPreimage_range_diagChart_subset_*`);
3. rewrite through the summand's **(A)** identity (`spfGraphCodiag*_eq*`) to land in `Q_x` or `Q_y`.

That is eight branches, tabulated in `mem_range_of_branch`'s uses below.

## Main results

* `AlgebraicGeometry.preimage_range_diagonal_ft`, `AlgebraicGeometry.preimage_range_diagonal_tf`:
  the mixed-chart preimage of `range Δ.base` is `Q_x ∪ Q_y`.
* `AlgebraicGeometry.isClosed_coe_preimage_range_diagonal_offChart`: it is closed (issue 424-ii).
* `AlgebraicGeometry.isClosed_range_tateSelfProductDiagonal_base`: `range Δ.base` is closed.
* `AlgebraicGeometry.isClosedEmbedding_tateSelfProductDiagonal_base`: `Δ.base` is a closed
  embedding.
* `AlgebraicGeometry.restrictPreimage_diagonal_offDiag`: the mixed-chart restriction of `Δ.base`
  is a closed embedding (issue 424).

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
open AlgebraicGeometry FormalSpectrum CompletedTensorProduct CompletedTensorAwayInterchange

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R) [IsNoetherianRing R]
variable [TopologicalSpace R] [IsAdicRing I]

/-! ### The range decomposition of the glued diagonal -/

/-- **Range decomposition of the glued diagonal.** The range of `Δ.base` is the union, over the two
curve charts `b : ULift Bool`, of the ranges of the diagonal-chart composites
`diagChart ≫ ι (b, b)`. This follows from the joint surjectivity of the two curve-chart
inclusions together with the factorisation `ι b ≫ Δ = diagChart ≫ ι (b, b)`
(`curve_ι_comp_selfProductDiagonal`). -/
theorem range_tateSelfProductDiagonal_base_eq_union (hq : q ∈ I) (hI : I.FG) :
    Set.range (tateSelfProductDiagonal R I q hq hI).base =
      Set.range ((diagChart R I q hI ≫
          (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(false, false)⟩).base) ∪
        Set.range ((diagChart R I q hI ≫
          (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(true, true)⟩).base) := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, rfl⟩
    obtain ⟨b, x', rfl⟩ := (tateCurveFormalGlueData R I q hq hI).ι_jointly_surjective x
    have hpt : (tateSelfProductDiagonal R I q hq hI).base
        (((tateCurveFormalGlueData R I q hq hI).ι b).base x') =
        (diagChart R I q hI ≫
          (tateSelfProductFormalGlueDataInv R I q hq hI).ι ⟨(b.down, b.down)⟩).base x' :=
      congrArg (fun m => m.base x')
        (curve_ι_comp_selfProductDiagonal R I q hq hI b.down)
    rw [hpt]
    obtain ⟨_ | _⟩ := b
    · exact Or.inl ⟨x', rfl⟩
    · exact Or.inr ⟨x', rfl⟩
  · rintro y (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · exact ⟨((tateCurveFormalGlueData R I q hq hI).ι ⟨false⟩).base x,
        congrArg (fun m => m.base x) (curve_ι_comp_selfProductDiagonal R I q hq hI false)⟩
    · exact ⟨((tateCurveFormalGlueData R I q hq hI).ι ⟨true⟩).base x,
        congrArg (fun m => m.base x) (curve_ι_comp_selfProductDiagonal R I q hq hI true)⟩

/-! ### The summand legs of the two overlap charts and of the two transitions -/

section Legs

variable (hI : I.FG)

/-- The `dAX` leg of the second-factor overlap chart. -/
theorem inl_comp_secondFactorOverlapChart :
    (coprod.inl : dAX R I q ⟶ dAX R I q ⨿ dAY R I q) ≫ secondFactorOverlapChart R I q hI =
      rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapX R I q) hI :=
  coprod.inl_desc _ _

/-- The `dAY` leg of the second-factor overlap chart. -/
theorem inr_comp_secondFactorOverlapChart :
    (coprod.inr : dAY R I q ⟶ dAX R I q ⨿ dAY R I q) ≫ secondFactorOverlapChart R I q hI =
      rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapY R I q) hI :=
  coprod.inr_desc _ _

/-- The `dXA` leg of the first-factor overlap chart. -/
theorem inl_comp_firstFactorOverlapChart :
    (coprod.inl : dXA R I q ⟶ dXA R I q ⨿ dYA R I q) ≫ firstFactorOverlapChart R I q hI =
      interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapX R I q) hI :=
  coprod.inl_desc _ _

/-- The `dYA` leg of the first-factor overlap chart. -/
theorem inr_comp_firstFactorOverlapChart :
    (coprod.inr : dYA R I q ⟶ dXA R I q ⨿ dYA R I q) ≫ firstFactorOverlapChart R I q hI =
      interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapY R I q) hI :=
  coprod.inr_desc _ _

/-- **The `dAX`-summand transition composite** of the second-factor overlap: the shape bounded by
`spfPreimage_range_diagChart_subset_second_dAX_*`. -/
theorem inl_comp_secondTransition_comp_chart :
    (coprod.inl : dAX R I q ⟶ dAX R I q ⨿ dAY R I q) ≫
        (tateSelfProductRightTransitionInv R I q hI).hom ≫ secondFactorOverlapChart R I q hI =
      (rightSummandInv R I q hI).hom ≫
        rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapY R I q) hI := by
  have htr : (coprod.inl : dAX R I q ⟶ dAX R I q ⨿ dAY R I q) ≫
      (tateSelfProductRightTransitionInv R I q hI).hom =
      (rightSummandInv R I q hI).hom ≫ coprod.inr := coprod.inl_desc _ _
  rw [← Category.assoc, htr, Category.assoc, inr_comp_secondFactorOverlapChart]

/-- **The `dAY`-summand transition composite** of the second-factor overlap. -/
theorem inr_comp_secondTransition_comp_chart :
    (coprod.inr : dAY R I q ⟶ dAX R I q ⨿ dAY R I q) ≫
        (tateSelfProductRightTransitionInv R I q hI).hom ≫ secondFactorOverlapChart R I q hI =
      (rightSummandInv R I q hI).inv ≫
        rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapX R I q) hI := by
  have htr : (coprod.inr : dAY R I q ⟶ dAX R I q ⨿ dAY R I q) ≫
      (tateSelfProductRightTransitionInv R I q hI).hom =
      (rightSummandInv R I q hI).inv ≫ coprod.inl := coprod.inr_desc _ _
  rw [← Category.assoc, htr, Category.assoc, inl_comp_secondFactorOverlapChart]

/-- **The `dXA`-summand transition composite** of the first-factor overlap. -/
theorem inl_comp_firstTransition_comp_chart :
    (coprod.inl : dXA R I q ⟶ dXA R I q ⨿ dYA R I q) ≫
        (tateSelfProductFirstTransitionInv R I q hI).hom ≫ firstFactorOverlapChart R I q hI =
      (firstSummandInv R I q hI).hom ≫
        interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapY R I q) hI := by
  have htr : (coprod.inl : dXA R I q ⟶ dXA R I q ⨿ dYA R I q) ≫
      (tateSelfProductFirstTransitionInv R I q hI).hom =
      (firstSummandInv R I q hI).hom ≫ coprod.inr := coprod.inl_desc _ _
  rw [← Category.assoc, htr, Category.assoc, inr_comp_firstFactorOverlapChart]

/-- **The `dYA`-summand transition composite** of the first-factor overlap. -/
theorem inr_comp_firstTransition_comp_chart :
    (coprod.inr : dYA R I q ⟶ dXA R I q ⨿ dYA R I q) ≫
        (tateSelfProductFirstTransitionInv R I q hI).hom ≫ firstFactorOverlapChart R I q hI =
      (firstSummandInv R I q hI).inv ≫
        interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapX R I q) hI := by
  have htr : (coprod.inr : dYA R I q ⟶ dXA R I q ⨿ dYA R I q) ≫
      (tateSelfProductFirstTransitionInv R I q hI).hom =
      (firstSummandInv R I q hI).inv ≫ coprod.inl := coprod.inr_desc _ _
  rw [← Category.assoc, htr, Category.assoc, inl_comp_firstFactorOverlapChart]

end Legs

/-! ### The generic branch step -/

/-- **One branch of the mixed-chart `⊆` argument.** A point `z` presented as `cRaw.base u` whose
transported point `σRaw.base u` lies in the affine diagonal locus `D` lies in the range of the
graph codiagonal `codiag`, provided

* `cRaw`/`σRaw` are the raw (coproduct-inclusion) forms of the summand chart `c` and the summand
  transition composite `σ` (`hc`, `hσ`);
* the preimage of `D` under `σ` is bounded by the range of the summand's graph lift `g`
  (`hbound`, i.e. issue 557c);
* `codiag` factors as `g ≫ c` (`hA`, the summand's **(A)** identity). -/
theorem mem_range_of_branch {W X Y Z : LocallyRingedSpace.{u}}
    {cRaw c : X ⟶ Z} {σRaw σ : X ⟶ Y} {D : Set Y} {g : W ⟶ X} {codiag : W ⟶ Z}
    (hc : cRaw = c) (hσ : σRaw = σ)
    (hbound : ⇑σ.base ⁻¹' D ⊆ Set.range ⇑g.base) (hA : codiag = g ≫ c)
    {z : Z} (h : ∃ u : X, z = cRaw.base u ∧ σRaw.base u ∈ D) :
    z ∈ Set.range ⇑codiag.base := by
  obtain ⟨u, hzu, hu⟩ := h
  rw [hc] at hzu
  rw [hσ] at hu
  obtain ⟨w, hw⟩ := hbound hu
  refine ⟨w, ?_⟩
  rw [hA]
  exact (congrArg (⇑c.base) hw).trans hzu.symm

/-! ### The mixed-chart preimage is the union of the two graph pieces -/

section MixedCharts

/-- **The mixed chart `(false, true)`.** The preimage of `range Δ.base` under the chart inclusion
is exactly the union of the two graph pieces `Q_x ∪ Q_y`. -/
theorem preimage_range_diagonal_ft (hq : q ∈ I) (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
    haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    ⇑((tateSelfProductFormalGlueDataInv R I q hq hI).ι
          (⟨(false, true)⟩ : ULift.{u} (Bool × Bool))).base ⁻¹'
        Set.range (tateSelfProductDiagonal R I q hq hI).base =
      Set.range ⇑(spfGraphCodiagX R I q hI).base ∪
        Set.range ⇑(spfGraphCodiagY R I q hI).base := by
  haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
  haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  apply Set.Subset.antisymm
  · intro z hz
    have hz₀ : ((tateSelfProductFormalGlueDataInv R I q hq hI).ι
        (⟨(false, true)⟩ : ULift.{u} (Bool × Bool))).base z ∈
        Set.range (tateSelfProductDiagonal R I q hq hI).base := hz
    rcases (Set.ext_iff.mp
      (range_tateSelfProductDiagonal_base_eq_union R I q hq hI) _).mp hz₀ with h | h
    · rcases mixedChartSplit_second_ft R I q hq hI z h with hb | hb
      · exact Or.inr (mem_range_of_branch
          (inl_comp_secondFactorOverlapChart R I q hI)
          (inl_comp_secondTransition_comp_chart R I q hI)
          (spfPreimage_range_diagChart_subset_second_dAX_y R I q hI)
          (spfGraphCodiagY_eq_ft_dAX R I q hI) hb)
      · exact Or.inl (mem_range_of_branch
          (inr_comp_secondFactorOverlapChart R I q hI)
          (inr_comp_secondTransition_comp_chart R I q hI)
          (spfPreimage_range_diagChart_subset_second_dAY_x R I q hI)
          (spfGraphCodiagX_eq R I q hI) hb)
    · rcases mixedChartSplit_first_ft R I q hq hI z h with hb | hb
      · exact Or.inl (mem_range_of_branch
          (inl_comp_firstFactorOverlapChart R I q hI)
          (inl_comp_firstTransition_comp_chart R I q hI)
          (spfPreimage_range_diagChart_subset_first_dXA_x R I q hI)
          (spfGraphCodiagX_eq_ft_dXA R I q hI) hb)
      · exact Or.inr (mem_range_of_branch
          (inr_comp_firstFactorOverlapChart R I q hI)
          (inr_comp_firstTransition_comp_chart R I q hI)
          (spfPreimage_range_diagChart_subset_first_dYA_y R I q hI)
          (spfGraphCodiagY_eq R I q hI) hb)
  · rintro z (⟨w, rfl⟩ | ⟨w, rfl⟩)
    · exact range_spfGraphCodiagX_ft_subset R I q hq hI ⟨w, rfl⟩
    · exact range_spfGraphCodiagY_ft_subset R I q hq hI ⟨w, rfl⟩

/-- **The mixed chart `(true, false)`.** The mirror of `preimage_range_diagonal_ft`, with the two
factor-swapped graph pieces. -/
theorem preimage_range_diagonal_tf (hq : q ∈ I) (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
    haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    ⇑((tateSelfProductFormalGlueDataInv R I q hq hI).ι
          (⟨(true, false)⟩ : ULift.{u} (Bool × Bool))).base ⁻¹'
        Set.range (tateSelfProductDiagonal R I q hq hI).base =
      Set.range ⇑(spfGraphCodiagXComm R I q hI).base ∪
        Set.range ⇑(spfGraphCodiagYComm R I q hI).base := by
  haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
  haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  apply Set.Subset.antisymm
  · intro z hz
    have hz₀ : ((tateSelfProductFormalGlueDataInv R I q hq hI).ι
        (⟨(true, false)⟩ : ULift.{u} (Bool × Bool))).base z ∈
        Set.range (tateSelfProductDiagonal R I q hq hI).base := hz
    rcases (Set.ext_iff.mp
      (range_tateSelfProductDiagonal_base_eq_union R I q hq hI) _).mp hz₀ with h | h
    · rcases mixedChartSplit_first_tf R I q hq hI z h with hb | hb
      · exact Or.inr (mem_range_of_branch
          (inl_comp_firstFactorOverlapChart R I q hI)
          (inl_comp_firstTransition_comp_chart R I q hI)
          (spfPreimage_range_diagChart_subset_first_dXA_y R I q hI)
          (spfGraphCodiagYComm_eq_tf_dXA R I q hI) hb)
      · exact Or.inl (mem_range_of_branch
          (inr_comp_firstFactorOverlapChart R I q hI)
          (inr_comp_firstTransition_comp_chart R I q hI)
          (spfPreimage_range_diagChart_subset_first_dYA_x R I q hI)
          (spfGraphCodiagXComm_eq R I q hI) hb)
    · rcases mixedChartSplit_second_tf R I q hq hI z h with hb | hb
      · exact Or.inl (mem_range_of_branch
          (inl_comp_secondFactorOverlapChart R I q hI)
          (inl_comp_secondTransition_comp_chart R I q hI)
          (spfPreimage_range_diagChart_subset_second_dAX_x R I q hI)
          (spfGraphCodiagXComm_eq_tf_dAX R I q hI) hb)
      · exact Or.inr (mem_range_of_branch
          (inr_comp_secondFactorOverlapChart R I q hI)
          (inr_comp_secondTransition_comp_chart R I q hI)
          (spfPreimage_range_diagChart_subset_second_dAY_y R I q hI)
          (spfGraphCodiagYComm_eq R I q hI) hb)
  · rintro z (⟨w, rfl⟩ | ⟨w, rfl⟩)
    · exact range_spfGraphCodiagXComm_tf_subset R I q hq hI ⟨w, rfl⟩
    · exact range_spfGraphCodiagYComm_tf_subset R I q hq hI ⟨w, rfl⟩

/-! ### The mixed-chart coe-preimage is closed -/

/-- **The coe-preimage of `range Δ.base` over a mixed chart `(b, ¬b)` is closed** (issue 424-ii).
This is the genuine new content over the corrected inversion model: the diagonal-over-overlap locus
in the mixed chart is the union of the two graphs of the 𝔾m-inversion transition, each realised as
the range of `Spf` of a surjective graph codiagonal, hence closed. -/
theorem isClosed_coe_preimage_range_diagonal_offChart (hq : q ∈ I) (hI : I.FG) (b : ULift Bool) :
    IsClosed (Subtype.val ⁻¹' Set.range (tateSelfProductDiagonal R I q hq hI).base :
      Set (tateSelfProductChartCover R I q hq hI ⟨(b.down, !b.down)⟩)) := by
  haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
  haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  refine isClosed_coe_preimage_chartCover_of_isClosed_preimage R I q hq hI _ _ ?_
  obtain ⟨_ | _⟩ := b
  · have h := (isClosed_range_spfGraphCodiagX R I q hI).union
      (isClosed_range_spfGraphCodiagY R I q hI)
    rw [← preimage_range_diagonal_ft R I q hq hI] at h
    exact h
  · have h := (isClosed_range_spfGraphCodiagXComm R I q hI).union
      (isClosed_range_spfGraphCodiagYComm R I q hI)
    rw [← preimage_range_diagonal_tf R I q hq hI] at h
    exact h

/-! ### Global closedness and the closed embedding -/

/-- **The range of the glued Tate self-product diagonal is closed.** Checked local-at-target along
the four-chart open cover: on the diagonal charts by `restrictPreimage_diagonal_diagChart`, on the
mixed charts by `isClosed_coe_preimage_range_diagonal_offChart`. -/
theorem isClosed_range_tateSelfProductDiagonal_base (hq : q ∈ I) (hI : I.FG) :
    IsClosed (Set.range (tateSelfProductDiagonal R I q hq hI).base) := by
  apply (tateSelfProductChartCover_isOpenCover R I q hq hI).isClosed_iff_coe_preimage.mpr
  rintro ⟨⟨c₁, c₂⟩⟩
  match c₁, c₂ with
  | false, false =>
    have h := (restrictPreimage_diagonal_diagChart R I q hq hI
      (⟨false⟩ : ULift.{u} Bool)).isClosed_range
    rwa [Set.range_restrictPreimage] at h
  | true, true =>
    have h := (restrictPreimage_diagonal_diagChart R I q hq hI
      (⟨true⟩ : ULift.{u} Bool)).isClosed_range
    rwa [Set.range_restrictPreimage] at h
  | false, true =>
    exact isClosed_coe_preimage_range_diagonal_offChart R I q hq hI (⟨false⟩ : ULift.{u} Bool)
  | true, false =>
    exact isClosed_coe_preimage_range_diagonal_offChart R I q hq hI (⟨true⟩ : ULift.{u} Bool)

/-- **The base map of the glued Tate self-product diagonal is a topological embedding.** It is a
section of the first projection `pr₁` (`tateSelfProductDiagonal_comp_pr₁`), hence a
left-invertible continuous map. -/
theorem isEmbedding_tateSelfProductDiagonal_base (hq : q ∈ I) (hI : I.FG) :
    IsEmbedding ⇑(tateSelfProductDiagonal R I q hq hI).base := by
  have hsecpt : ∀ c, (tateSelfProductPr₁ R I q hq hI).base
      ((tateSelfProductDiagonal R I q hq hI).base c) = c := fun c =>
    congrArg (fun m => m.base c) (tateSelfProductDiagonal_comp_pr₁ R I q hq hI)
  exact Topology.IsEmbedding.of_leftInverse hsecpt
    (tateSelfProductPr₁ R I q hq hI).base.hom.continuous
    (tateSelfProductDiagonal R I q hq hI).base.hom.continuous

/-- **The base map of the glued Tate self-product diagonal is a closed topological embedding**
(EGA I §10.15, route b): it is a topological embedding with closed range. -/
theorem isClosedEmbedding_tateSelfProductDiagonal_base (hq : q ∈ I) (hI : I.FG) :
    IsClosedEmbedding ⇑(tateSelfProductDiagonal R I q hq hI).base :=
  ⟨isEmbedding_tateSelfProductDiagonal_base R I q hq hI,
    isClosed_range_tateSelfProductDiagonal_base R I q hq hI⟩

/-- **The mixed-chart restriction of the diagonal is a closed embedding** (issue 424). On the mixed
chart `(b, ¬b)` the restriction of `Δ.base` to the preimage of the chart is a closed topological
embedding, immediately from the global closed embedding via
`Set.restrictPreimage_isClosedEmbedding`. -/
theorem restrictPreimage_diagonal_offDiag (hq : q ∈ I) (hI : I.FG) (b : ULift Bool) :
    IsClosedEmbedding
      ((tateSelfProductChartCover R I q hq hI ⟨(b.down, !b.down)⟩ :
        Set ((tateSelfProductInv R I q hq hI).toLocallyRingedSpace)).restrictPreimage
        (tateSelfProductDiagonal R I q hq hI).base) :=
  Set.restrictPreimage_isClosedEmbedding _
    (isClosedEmbedding_tateSelfProductDiagonal_base R I q hq hI)

end MixedCharts

end AlgebraicGeometry
