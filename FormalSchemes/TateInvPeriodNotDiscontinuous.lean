import FormalSchemes.ActionSpecialization
import FormalSchemes.TateActionInv

set_option linter.style.header false

/-!
# The period-`q` shift of the Tate chain, and what it would take to be properly discontinuous

Fix an adic base `(R, I)` with `I` finitely generated and Noetherian `R`, and a Tate parameter
`q ∈ I`. `FormalSchemes.TateActionInv` builds the `q^ℤ`-action `tateInvPeriodAction` of the shift
`σ` on the inversion-glued chain `T_inv`, and `FormalSchemes.ActionDiscontinuous` proves the
*square* action `σ^{2ℤ}` is free and properly discontinuous
(`tateInvPeriodSq_isFreeProperlyDiscontinuous`), which is what makes `𝔈_q = T_inv/⟨σ²⟩` — the Tate
curve of period `q²` — a formal scheme.

The period-`q` curve `T_inv/⟨σ⟩` is a different matter, and by
`AlgebraicGeometry.LocallyRingedSpace.freeActionQuotientFormalScheme` the *whole* of it reduces to
one hypothesis: `IsFreeProperlyDiscontinuous (tateInvPeriodAction R I q hq hI)`. Every other input
of that theorem is already available for `σ` — `tateChainInv_locallyFG` supplies `LocallyFG`,
`isActionQuotient_actionQuotientπ` the quotient, and `Multiplicative ℤ` is `Small`.

The `σ²` proof cannot be reused: it takes the separating neighbourhood of a point to be the whole
patch `U_n` containing it, which works because `tateInvShift_properlyDiscontinuous` covers every
translation amount `k` with `|k| ≥ 2`, and every exponent of the square action is even. For `σ` the
amounts that arise are exactly the excluded `k = ±1`, and `U_n` does meet `U_{n±1}`.

## What this file proves

The single-patch **reduction**. `not_isFreeProperlyDiscontinuous_tateInvPeriodAction_of_specializes`
says: if one point `v` of the `x`-overlap `Spf A{1/x}` has the property that its image under the
`x`-chart *and* its image under the transition followed by the `y`-chart both specialize to one
point `N` of the patch `Spf A`, then the `σ`-action is **not** free and properly discontinuous, so
`T_inv/⟨σ⟩` is not reachable by `freeActionQuotientFormalScheme`.

Geometrically `N` is a node of the special fibre `Spec (A ⧸ I·A)` — two affine lines meeting at a
point — and `v` is the generic point of the `𝔾m` between two consecutive patches: its `x`-chart
image is the generic point of one branch through `N`, and its transported `y`-chart image is the
generic point of the other. The hypothesis is therefore a statement about a *single affine patch*,
with the whole chain, the gluing and the shift already discharged here. Such a `v` and `N` are
produced in `FormalSchemes.TateInvPeriodNodePoint`, where they settle the question: the answer is
that `σ` is **not** free and properly discontinuous whenever `I ≠ ⊤`.

The chain-level ingredients are `annulusOverlapChart_comp_ι` (the glue condition read as an identity
between the two charts and the two inclusions) and the cover-shift law `ι_tateInvShiftAut_zpow`; the
topological ingredient is `LocallyRingedSpace.not_isFreeProperlyDiscontinuous_of_specializes`
(`FormalSchemes.ActionSpecialization`).

## Main results

* `AlgebraicGeometry.annulusOverlapChart_comp_ι`
* `AlgebraicGeometry.not_isFreeProperlyDiscontinuous_tateInvPeriodAction_of_specializes`

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9 — where `E_q` is formed on the
  *rigid* side, not the formal one.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum Topology

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)

set_option maxHeartbeats 1600000 in
-- The four-case unfolding of `CategoryTheory.GlueData.ofGlueData'` gives a large term; raise the
-- budget, exactly as `tateChainInv_glueMorphisms_compat` does.
omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The glue condition of the inversion-glued chain, read on the two charts.** For consecutive
indices `j = i + 1`, the `x`-chart of the patch `U_i` and the `y`-chart of the patch `U_j` have the
same composite into the glued chain, once the second is preceded by the `𝔾m`-inversion transition:
```
Spf A{1/x} ⟶ U_i ⟶ T_inv   =   Spf A{1/x} ≅ Spf A{1/y} ⟶ U_j ⟶ T_inv.
```
This is `CategoryTheory.GlueData.glue_condition` with the `f` and `t` fields of
`tateChainInvGlueData'` unfolded on the adjacent pair; the unfolding is the forward half of the
four-case split performed by `tateChainInv_glueMorphisms_compat`. -/
theorem annulusOverlapChart_comp_ι {i j : ULift.{u} ℤ} (h : j.down - i.down = 1) :
    annulusOverlapChart R I q ≫ (tateChainInvFormalGlueData R I q hq hI).ι i =
      (annulusChartTransitionInvSpf R I q hI).hom ≫ annulusOverlapChartY R I q ≫
        (tateChainInvFormalGlueData R I q hq hI).ι j := by
  have hij : ¬ @Eq (ULift.{u} ℤ) i j := fun e => by rw [e] at h; omega
  have hji : ¬ @Eq (ULift.{u} ℤ) j i := fun e => hij e.symm
  have key := (tateChainInvFormalGlueData R I q hq
    hI).toLocallyRingedSpaceGlueData.toGlueData.glue_condition i j
  simp only [tateChainInvFormalGlueData, tateChainInvLRSGlueData, tateChainInvGlueData',
    CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f', dif_neg hij,
    dif_neg hji, Category.assoc] at key
  rw [tateF_forward R I q h, tateTInv, dif_pos h,
    tateF_backward R I q (show i.down - j.down = -1 by omega)] at key
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] at key
  exact (cancel_epi _).mp key.symm

/-- **The single-patch reduction of the period-`q` question.** Suppose some point `v` of the
`x`-overlap `Spf A{1/x}` has both of its images in the patch `Spf A` — the `x`-chart image, and the
`y`-chart image of its transition — specializing to one and the same point `N`. Then the `q^ℤ`-shift
`σ` on the inversion-glued chain is **not** free and properly discontinuous, and therefore
`T_inv/⟨σ⟩` (the period-`q` Tate curve, as opposed to the period-`q²` object `𝔈_q =
T_inv/⟨σ²⟩` that the tree builds) is not obtainable from
`LocallyRingedSpace.freeActionQuotientFormalScheme`.

The proof puts both images into the patch `U₀`: the glue condition
(`annulusOverlapChart_comp_ι`) identifies the `x`-chart image seen in `U₀` with the transported
`y`-chart image seen in `U₁`, and the cover-shift law `ι_tateInvShiftAut_zpow` says `σ` carries
`U₀` onto `U₁`. So the two points of `U₀` are exchanged by `σ` inside the chain, and both
specialize to the image of `N`, which is `not_isFreeProperlyDiscontinuous_of_specializes`. -/
theorem not_isFreeProperlyDiscontinuous_tateInvPeriodAction_of_specializes
    (v : locallyRingedSpaceObj
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q)))
    (N : locallyRingedSpaceObj (annulusIdealOfDefinition R I q))
    (hx : ((annulusOverlapChart R I q).base v : locallyRingedSpaceObj _) ⤳ N)
    (hy : ((annulusOverlapChartY R I q).base
      ((annulusChartTransitionInvSpf R I q hI).hom.base v) :
        locallyRingedSpaceObj _) ⤳ N) :
    ¬ LocallyRingedSpace.IsFreeProperlyDiscontinuous (tateInvPeriodAction R I q hq hI) := by
  have hglue : ((tateChainInvFormalGlueData R I q hq hI).ι ⟨(0 : ℤ)⟩).base
        ((annulusOverlapChart R I q).base v) =
      ((tateChainInvFormalGlueData R I q hq hI).ι ⟨(1 : ℤ)⟩).base
        ((annulusOverlapChartY R I q).base
          ((annulusChartTransitionInvSpf R I q hI).hom.base v)) := by
    have h1 := annulusOverlapChart_comp_ι R I q hq hI
      (i := ⟨(0 : ℤ)⟩) (j := ⟨(1 : ℤ)⟩) (by norm_num)
    have h2 : (annulusOverlapChart R I q ≫
          (tateChainInvFormalGlueData R I q hq hI).ι ⟨(0 : ℤ)⟩).base v =
        ((annulusChartTransitionInvSpf R I q hI).hom ≫ annulusOverlapChartY R I q ≫
          (tateChainInvFormalGlueData R I q hq hI).ι ⟨(1 : ℤ)⟩).base v := by rw [h1]
    simp only [LocallyRingedSpace.comp_toHom, PresheafedSpace.comp_base, TopCat.hom_comp,
      ContinuousMap.coe_comp, Function.comp_apply] at h2
    exact h2
  have hshift : ∀ p : locallyRingedSpaceObj (annulusIdealOfDefinition R I q),
      (tateInvPeriodAction R I q hq hI (Multiplicative.ofAdd (1 : ℤ))).hom.base
        (((tateChainInvFormalGlueData R I q hq hI).ι ⟨(0 : ℤ)⟩).base p) =
      ((tateChainInvFormalGlueData R I q hq hI).ι ⟨(1 : ℤ)⟩).base p := by
    intro p
    rw [tateInvPeriodAction_apply]
    have hz : (tateChainInvFormalGlueData R I q hq hI).ι ⟨(0 : ℤ)⟩ ≫
        (tateInvShiftAut R I q hq hI ^ (1 : ℤ)).hom =
          (tateChainInvFormalGlueData R I q hq hI).ι ⟨(1 : ℤ)⟩ := by
      simpa using ι_tateInvShiftAut_zpow R I q hq hI 1 ⟨(0 : ℤ)⟩
    have h3 : ((tateChainInvFormalGlueData R I q hq hI).ι ⟨(0 : ℤ)⟩ ≫
          (tateInvShiftAut R I q hq hI ^ (1 : ℤ)).hom).base p =
        ((tateChainInvFormalGlueData R I q hq hI).ι ⟨(1 : ℤ)⟩).base p := by
      rw [hz]
      rfl
    simp only [LocallyRingedSpace.comp_toHom, PresheafedSpace.comp_base, TopCat.hom_comp,
      ContinuousMap.coe_comp, Function.comp_apply] at h3
    exact h3
  refine LocallyRingedSpace.not_isFreeProperlyDiscontinuous_of_specializes
    (x := ((tateChainInvFormalGlueData R I q hq hI).ι ⟨(0 : ℤ)⟩).base N)
    (w := ((tateChainInvFormalGlueData R I q hq hI).ι ⟨(0 : ℤ)⟩).base
      ((annulusOverlapChartY R I q).base
        ((annulusChartTransitionInvSpf R I q hI).hom.base v)))
    (g := Multiplicative.ofAdd (1 : ℤ)) (by simp) ?_ ?_
  · exact hy.map ((tateChainInvFormalGlueData R I q hq hI).ι ⟨(0 : ℤ)⟩).base.hom.continuous
  · rw [hshift, ← hglue]
    exact hx.map ((tateChainInvFormalGlueData R I q hq hI).ι ⟨(0 : ℤ)⟩).base.hom.continuous

end AlgebraicGeometry
