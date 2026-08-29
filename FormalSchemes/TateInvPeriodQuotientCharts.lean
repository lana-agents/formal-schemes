import FormalSchemes.ActionQuotientChartAt
import FormalSchemes.TateChainInvLocallyFG
import FormalSchemes.TateInvOverlapDiscontinuous
import FormalSchemes.TateInvPeriodNodePoint

set_option linter.style.header false

/-!
# Charts of `T_inv/⟨σ⟩`, and the single orbit that is left

`AlgebraicGeometry.not_isFreeProperlyDiscontinuous_tateInvPeriodAction`
(`FormalSchemes.TateInvPeriodNodePoint`) closes `LocallyRingedSpace.freeActionQuotientFormalScheme`
as a route to the period-`q` quotient `T_inv/⟨σ⟩`. Closing a *sufficient* criterion is not a
negative answer, and this file measures how much of the question survives it.

The answer is: one orbit. Combining

* `tateInvOverlap_isProperlyDiscontinuousOn` (`FormalSchemes.TateInvOverlapDiscontinuous`) — the
  overlap `W_i = U_i ∩ U_{i+1}` separates `σ`, and
* `LocallyRingedSpace.hasAffineChartAt_of_isProperlyDiscontinuousOn`
  (`FormalSchemes.ActionQuotientChartAt`) — a separating open around one point already produces the
  quotient's chart at the image of that point,

gives an affine formal chart of the quotient at the image of **every point of every overlap**. The
overlaps meeting a patch `U_i` are the `ι i`-images of the two chart loci `D(x)` and `D(y)` of the
annulus `Spf A` (`tateInvOverlap_eq_image_chartX`, `tateInvOverlap_eq_image_chartY`), and the
`ι i`-images cover the chain. So the only points of `T_inv/⟨σ⟩` still without a chart are the images
of the annulus's node locus `V(x, y) = Spf A ∖ (D(x) ∪ D(y))`, and — since `σ` translates the
patches — it is enough to produce a chart at the images of the node locus of the **single** patch
`U_0`.

That is `tateInvPeriodQuotientFormalSchemeOfNodeChart`: the whole of "is `T_inv/⟨σ⟩` a formal
scheme?" is now one hypothesis about one patch, in the same shape as the reduction
`FormalSchemes.TateInvPeriodNodePoint` made for the refutation.

## What is *not* proved here

Whether that hypothesis holds. The expected answer is yes — the special fibre of `T_inv/⟨σ⟩` is the
Néron 1-gon, `ℙ¹` with `0` and `∞` glued, which is a perfectly good scheme, and its node has an
affine neighbourhood — but the chart has to be *built*, and building it cannot go through any open
of the chain: `not_isFreeProperlyDiscontinuous_tateInvPeriodAction` says no open of `T_inv`
containing a node maps injectively to the quotient. Nothing here asserts an answer either way.

Nothing here weakens `LocallyRingedSpace.IsProperlyDiscontinuousOn`,
`LocallyRingedSpace.IsFreeProperlyDiscontinuous` or
`LocallyRingedSpace.freeActionQuotientFormalScheme`; the reduction is assembled from the pointwise
criterion, which is a *different* theorem with its own justification, not an edit to those.

## Main results

* `AlgebraicGeometry.hasAffineChartAt_of_mem_tateInvOverlap`: the quotient has an affine formal
  chart at the image of every overlap point.
* `AlgebraicGeometry.tateInvOverlap_nonempty`: the overlaps are nonempty when `I ≠ ⊤`, so the
  previous statement is not vacuous.
* `AlgebraicGeometry.base_ι_eq_of_isActionQuotient`: the projection does not see the patch index.
* `AlgebraicGeometry.tateInvPeriodQuotientFormalSchemeOfNodeChart`: **the reduction** — a chart at
  the image of each node of `U_0` makes `T_inv/⟨σ⟩` a formal scheme.
* `AlgebraicGeometry.exists_hasAffineChartAt_actionQuotient_tateInvPeriod`: the canonical quotient
  really does have a chart somewhere.

## References

* [Deligne–Rapoport, *Les schémas de modules de courbes elliptiques*], II.1 — the Néron `n`-gon.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)
variable {Q : LocallyRingedSpace.{u}} {π : (tateChainInv R I q hq hI).toLocallyRingedSpace ⟶ Q}

/-- **The quotient has an affine formal chart at the image of every overlap point.** The overlap
`W_i` separates `σ` (`tateInvOverlap_isProperlyDiscontinuousOn`), and that is all the pointwise
criterion needs; the chain is `LocallyFG` by `tateChainInv_locallyFG`. -/
theorem hasAffineChartAt_of_mem_tateInvOverlap
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) {i : ULift.{u} ℤ}
    {x : (tateChainInv R I q hq hI).toLocallyRingedSpace}
    (hx : x ∈ tateInvOverlap R I q hq hI i) :
    LocallyRingedSpace.HasAffineChartAt Q (π.base x) :=
  LocallyRingedSpace.hasAffineChartAt_of_isProperlyDiscontinuousOn
    (tateChainInv_locallyFG R I q hq hI) h
    (U := ⟨tateInvOverlap R I q hq hI i, isOpen_tateInvOverlap R I q hq hI i⟩)
    (tateInvOverlap_isProperlyDiscontinuousOn R I q hq hI i) hx

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The overlaps are nonempty** whenever `Spf R` is: the generic point of the `𝔾m`-overlap over a
maximal ideal `𝔪 ⊇ I`, built for the refutation in `FormalSchemes.TateInvPeriodNodePoint`, is a
point of `Spf A{1/x}`, and its image under `ι i ∘ annulusOverlapChart` lies in `W_i`.

Without this the chart theorem above would be vacuous. `I ≠ ⊤` is the same standing hypothesis the
refutation needs, and for the same reason. -/
theorem tateInvOverlap_nonempty (hItop : I ≠ ⊤) (i : ULift.{u} ℤ) :
    (tateInvOverlap R I q hq hI i).Nonempty := by
  obtain ⟨𝔪, h𝔪, h𝔪le⟩ := Ideal.exists_le_maximal I hItop
  haveI : 𝔪.IsPrime := h𝔪.isPrime
  exact ⟨_, Set.mem_image_of_mem _
    (Set.mem_range_self (annulusOverlapGenericPoint R I q hI 𝔪 h𝔪le))⟩

/-- **The projection does not see the patch index.** The cover-shift law moves `ι n` to `ι m`
through `σ^{n−m}`, and the projection of an action quotient is invariant under `σ`. So a chart at
the image of a point of one patch is a chart at the image of the corresponding point of any
other. -/
theorem base_ι_eq_of_isActionQuotient
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) {m n : ULift.{u} ℤ} (k : ℤ)
    (hk : n.down = m.down + k)
    (y : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.U m) :
    π.base (((tateChainInvFormalGlueData R I q hq hI).ι n).base y) =
      π.base (((tateChainInvFormalGlueData R I q hq hI).ι m).base y) := by
  obtain rfl : n = (⟨m.down + k⟩ : ULift.{u} ℤ) := ULift.down_injective hk
  have hinv : ((tateInvShiftAut R I q hq hI) ^ k).hom ≫ π = π :=
    h.isInvariant (Multiplicative.ofAdd k)
  have hmor : (tateChainInvFormalGlueData R I q hq hI).ι ⟨m.down + k⟩ ≫ π =
      (tateChainInvFormalGlueData R I q hq hI).ι m ≫ π := by
    conv_lhs => rw [← ι_tateInvShiftAut_zpow R I q hq hI k m]
    exact (Category.assoc _ _ _).trans (congrArg
      (fun φ : (tateChainInv R I q hq hI).toLocallyRingedSpace ⟶ Q =>
        (tateChainInvFormalGlueData R I q hq hI).ι m ≫ φ) hinv)
  exact congrFun (congrArg
    (fun φ : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.U m ⟶ Q =>
      ⇑φ.base) hmor) y

/-- **The reduction: `T_inv/⟨σ⟩` is a formal scheme as soon as its node images have charts.**

Every point of the quotient is `π (ι n y)` for some patch index `n` and some `y : Spf A`. If `y`
lies in the `x`-chart locus `D(x)` it is in the overlap `W_n`; if it lies in the `y`-chart locus
`D(y)` it is in the overlap `W_{n−1}`; either way
`hasAffineChartAt_of_mem_tateInvOverlap` produces the chart. Otherwise `y` is in the node locus
`V(x, y)`, and `base_ι_eq_of_isActionQuotient` moves the question from patch `n` to patch `0`, which
is the hypothesis.

So the hypothesis is *only* about the node locus of *one* patch — the whole residue of "is
`T_inv/⟨σ⟩` a formal scheme?" after `FormalSchemes.TateInvPeriodNodePoint`. -/
def tateInvPeriodQuotientFormalSchemeOfNodeChart
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π)
    (hnode : ∀ y : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.U ⟨0⟩,
      y ∉ Set.range (annulusOverlapChart R I q).base →
      y ∉ Set.range (annulusOverlapChartY R I q).base →
      LocallyRingedSpace.HasAffineChartAt Q
        (π.base (((tateChainInvFormalGlueData R I q hq hI).ι ⟨0⟩).base y))) :
    FormalScheme.{u} :=
  LocallyRingedSpace.formalSchemeOfHasAffineChartAt Q (by
    intro xbar
    obtain ⟨x, rfl⟩ := LocallyRingedSpace.base_surjective_of_isActionQuotient h xbar
    obtain ⟨n, y, rfl⟩ := (tateChainInvFormalGlueData R I q hq hI).ι_jointly_surjective x
    by_cases hx : y ∈ Set.range (annulusOverlapChart R I q).base
    · exact hasAffineChartAt_of_mem_tateInvOverlap R I q hq hI h (i := n)
        (Set.mem_image_of_mem _ hx)
    · by_cases hy : y ∈ Set.range (annulusOverlapChartY R I q).base
      · refine hasAffineChartAt_of_mem_tateInvOverlap R I q hq hI h (i := ⟨n.down - 1⟩) ?_
        rw [tateInvOverlap_eq_image_chartY R I q hq hI
          (i := (⟨n.down - 1⟩ : ULift.{u} ℤ)) (j := n) (by simp)]
        exact Set.mem_image_of_mem _ hy
      · rw [base_ι_eq_of_isActionQuotient R I q hq hI h (m := ⟨0⟩) (n := n) n.down (by simp) y]
        exact hnode y hx hy)

/-- The formal scheme the reduction produces is the quotient itself. -/
@[simp]
theorem tateInvPeriodQuotientFormalSchemeOfNodeChart_toLocallyRingedSpace
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π)
    (hnode : ∀ y : (tateChainInvFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.U ⟨0⟩,
      y ∉ Set.range (annulusOverlapChart R I q).base →
      y ∉ Set.range (annulusOverlapChartY R I q).base →
      LocallyRingedSpace.HasAffineChartAt Q
        (π.base (((tateChainInvFormalGlueData R I q hq hI).ι ⟨0⟩).base y))) :
    (tateInvPeriodQuotientFormalSchemeOfNodeChart R I q hq hI h hnode).toLocallyRingedSpace = Q :=
  rfl

/-- **A quotient of the chain always has a chart somewhere.** An application of both halves: the
overlaps are nonempty when `I ≠ ⊤`, so `hasAffineChartAt_of_mem_tateInvOverlap` fires at a genuine
point. `exists_hasAffineChartAt_actionQuotient_tateInvPeriod` instantiates this at the coequalizer
quotient, so the hypothesis is satisfiable. -/
theorem exists_hasAffineChartAt_of_isActionQuotient (hItop : I ≠ ⊤)
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) :
    ∃ z : Q, LocallyRingedSpace.HasAffineChartAt Q z := by
  obtain ⟨x, hx⟩ := tateInvOverlap_nonempty R I q hq hI hItop ⟨0⟩
  exact ⟨_, hasAffineChartAt_of_mem_tateInvOverlap R I q hq hI h hx⟩

/-- The same at the canonical coequalizer quotient `CategoryTheory.actionQuotient`, which exists
unconditionally (`FormalSchemes.ActionQuotientColimit`). This is the witness that the reduction is
about a real object. -/
theorem exists_hasAffineChartAt_actionQuotient_tateInvPeriod (hItop : I ≠ ⊤) :
    ∃ z : (CategoryTheory.actionQuotient (tateInvPeriodAction R I q hq hI) :
        LocallyRingedSpace.{u}),
      LocallyRingedSpace.HasAffineChartAt
        (CategoryTheory.actionQuotient (tateInvPeriodAction R I q hq hI)) z :=
  exists_hasAffineChartAt_of_isActionQuotient R I q hq hI hItop
    (CategoryTheory.isActionQuotient_actionQuotientπ (tateInvPeriodAction R I q hq hI))

end AlgebraicGeometry
