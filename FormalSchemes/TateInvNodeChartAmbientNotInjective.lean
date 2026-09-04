import FormalSchemes.TateInvNodeChartAmbient
import FormalSchemes.TateInvPeriodQuotientCharts

set_option linter.style.header false

/-!
# The node chart's ambient morphism is not injective, so it is not the chart

`FormalSchemes.TateInvNodeChartAmbient` builds `AlgebraicGeometry.tateInvNodeChartAmbientHom`,
the morphism `Spf A{1/(x + y − 1)} ⟶ T_inv/⟨σ⟩`, and computes its range: it is **exactly** the
candidate node-chart domain `π '' tateInvSaturate D(x + y − 1)`. That file's docstring says the
morphism is *expected* to fail injectivity, and asks for the failure to be landed as a theorem
rather than cited as a paragraph. This file lands it.

## What is here

* **`AlgebraicGeometry.annulusBranchXPoint`** / **`AlgebraicGeometry.annulusBranchYPoint`**: the
  generic points of the two branches of the special fibre over a prime `𝔭 ⊇ I`, as points of
  `Spf A`. They are the kernels of the two evaluations `annulusBranchX`, `annulusBranchY` of
  `FormalSchemes.TateInvPeriodNodePoint`, which that file built to prove the node has no
  separating neighbourhood.
* **`AlgebraicGeometry.annulusBranchXPoint_ne_annulusBranchYPoint`**: they are distinct — `x` lies
  in one kernel and not the other — and
  **`AlgebraicGeometry.annulusBranchXPoint_mem_tateInvNodeChartLocus`** with its `Y`-mirror: both
  lie in the chosen chart domain `D(x + y − 1)`, because both branches evaluate `x + y − 1` to
  `X − 1 ≠ 0`.
* **`AlgebraicGeometry.annulusOverlapChart_base_annulusOverlapGenericPoint`** and
  **`AlgebraicGeometry.annulusOverlapChartY_base_transition_annulusOverlapGenericPoint`**: the two
  branch points are the two images, in the model patch, of the *one* point
  `annulusOverlapGenericPoint` of the overlap `Spf A{1/x}` — the `x`-chart image and the
  transported `y`-chart image. This is where `FormalSchemes.TateInvPeriodNodePoint`'s two
  `annulusChartEvalLaurentFibre_comp_*` identities are spent, together with its
  `AlgebraicGeometry.annulusOverlapChartY_base_transition_eq_comap_annulusTransitionedChartY`; the
  specialization statements that file draws from the same identities are not used.
* **`AlgebraicGeometry.base_actionQuotientπ_ι_annulusBranchXPoint_eq`**: the two branch points have
  the **same** image in the quotient. `base_ι_eq_of_isActionQuotient` moves patch `1` back onto
  patch `0`; the shift is what identifies them, exactly as the Néron 1-gon glues `0` to `∞`.
* **`AlgebraicGeometry.not_injOn_base_tateInvSaturate_tateInvNodeChartLocus`**: therefore `π` is
  not injective on the saturated chart domain, and
  **`AlgebraicGeometry.not_injective_base_tateInvNodeChartAmbientHom`**,
  **`AlgebraicGeometry.not_isOpenImmersion_tateInvNodeChartAmbientHom`**: the ambient morphism is
  not injective on points, hence not an open immersion.
* Those three carry the prime `𝔭 ⊇ I` they are proved at.
  **`AlgebraicGeometry.not_isOpenImmersion_tateInvNodeChartAmbientHom_of_ne_top`** and
  **`AlgebraicGeometry.not_injOn_base_tateInvSaturate_tateInvNodeChartLocus_of_ne_top`** discharge
  it against `I ≠ ⊤` by the same maximal-ideal step as
  `not_isFreeProperlyDiscontinuous_tateInvPeriodAction`, so the standing hypotheses are exactly
  `[IsNoetherianRing R]`, `[IsAdicRing I]`, `hq : q ∈ I`, `hI : I.FG` and `I ≠ ⊤`. No principality
  of `I`, no left-regularity, and no finite generation of any chart ideal is used.
* **`AlgebraicGeometry.exists_ne_and_base_actionQuotientπ_ι_eq`**: the two points packaged as an
  existential, which is the non-vacuity this file offers.

## What this does and does not settle

It settles the *identity of the chart candidate*, not `hnode`.
`AlgebraicGeometry.exists_formalScheme_of_openImmersion_spf_quotientIdeal_of_isLeftRegular_base`
(`FormalSchemes.TateInvNodeChartQuotientSpf`) asks for **some** open immersion
`f : Spf S ⟶ T_inv/⟨σ⟩` whose range contains
`Set.range (tateInvNodeChartAmbientHom …).base`. The obvious candidate for `f` — the morphism
whose range is *equal* to that set, already on the tree — is refuted here, and the refutation is
not evidence against `hnode`: the expected chart has source `Spf` of the **invariant subring**
`AlgebraicGeometry.tateInvNodeChartAwaySubring`, and the two-to-one behaviour proved here is
precisely the node of the 1-gon, which is what an affine nodal curve looks like from its
normalization. So this closes a route and confirms the picture that goals 1 and 2 were built on.

Nothing here weakens `LocallyRingedSpace.IsProperlyDiscontinuousOn`,
`LocallyRingedSpace.IsFreeProperlyDiscontinuous` or
`LocallyRingedSpace.freeActionQuotientFormalScheme`.

## References

* [Deligne–Rapoport, *Les schémas de modules de courbes elliptiques*], II.1 — the Néron 1-gon.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
-/

noncomputable section

open CategoryTheory Ideal AlgebraicGeometry FormalSpectrum Topology
open Polynomial LaurentPolynomial

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

section Branch

variable (𝔭 : Ideal R) [𝔭.IsPrime] (h𝔭 : I ≤ 𝔭) (hq : q ∈ I)

include h𝔭 hq in
/-- **The generic point of the `x`-branch of the special fibre over `𝔭`**, as a point of `Spf A`:
the kernel of `annulusBranchX`, a prime because `D[X]` is a domain. It is the `x`-chart image of
`annulusOverlapGenericPoint` (`annulusOverlapChart_base_annulusOverlapGenericPoint`). -/
def annulusBranchXPoint : PrimeSpectrum (annulusFibre R I q) :=
  PrimeSpectrum.comap (annulusBranchX R I q 𝔭 h𝔭 hq) ⟨⊥, Ideal.isPrime_bot⟩

include h𝔭 hq in
/-- **The generic point of the `y`-branch**, the mirror of `annulusBranchXPoint`. -/
def annulusBranchYPoint : PrimeSpectrum (annulusFibre R I q) :=
  PrimeSpectrum.comap (annulusBranchY R I q 𝔭 h𝔭 hq) ⟨⊥, Ideal.isPrime_bot⟩

include h𝔭 hq in
/-- Membership in the `x`-branch generic point is vanishing under the `x`-branch evaluation: the
point is a `PrimeSpectrum.comap` of `⊥`, so its ideal is the kernel. Definitional. -/
theorem mem_annulusBranchXPoint_iff {a : annulusFibre R I q} :
    a ∈ (annulusBranchXPoint R I q 𝔭 h𝔭 hq).asIdeal ↔ annulusBranchX R I q 𝔭 h𝔭 hq a = 0 :=
  Iff.rfl

include h𝔭 hq in
/-- The mirror of `mem_annulusBranchXPoint_iff`. -/
theorem mem_annulusBranchYPoint_iff {a : annulusFibre R I q} :
    a ∈ (annulusBranchYPoint R I q 𝔭 h𝔭 hq).asIdeal ↔ annulusBranchY R I q 𝔭 h𝔭 hq a = 0 :=
  Iff.rfl

omit [𝔭.IsPrime] in
include h𝔭 hq in
/-- The `x`-branch sends the coordinate `x` to the generator `X`. -/
theorem annulusBranchX_fibreX :
    annulusBranchX R I q 𝔭 h𝔭 hq (fibreX R I q) = (Polynomial.X : Polynomial (R ⧸ 𝔭)) := by
  rw [annulusBranchX, annulusFibreEval_fibreX]
  simp

omit [𝔭.IsPrime] in
include h𝔭 hq in
/-- The `x`-branch kills the coordinate `y`: it is the line `y = 0`. -/
theorem annulusBranchX_fibreY :
    annulusBranchX R I q 𝔭 h𝔭 hq (fibreY R I q) = (0 : Polynomial (R ⧸ 𝔭)) := by
  rw [annulusBranchX, annulusFibreEval_fibreY]
  simp

omit [𝔭.IsPrime] in
include h𝔭 hq in
/-- The `y`-branch kills the coordinate `x`: it is the line `x = 0`. -/
theorem annulusBranchY_fibreX :
    annulusBranchY R I q 𝔭 h𝔭 hq (fibreX R I q) = (0 : Polynomial (R ⧸ 𝔭)) := by
  rw [annulusBranchY, annulusFibreEval_fibreX]
  simp

omit [𝔭.IsPrime] in
include h𝔭 hq in
/-- The `y`-branch sends the coordinate `y` to the generator `X`. -/
theorem annulusBranchY_fibreY :
    annulusBranchY R I q 𝔭 h𝔭 hq (fibreY R I q) = (Polynomial.X : Polynomial (R ⧸ 𝔭)) := by
  rw [annulusBranchY, annulusFibreEval_fibreY]
  simp

include h𝔭 hq in
/-- **The two branch points are distinct.** The coordinate `x` vanishes on the `y`-branch and is
the generator `X` on the `x`-branch, and `X ≠ 0` because `R ⧸ 𝔭` is a domain. -/
theorem annulusBranchXPoint_ne_annulusBranchYPoint :
    annulusBranchXPoint R I q 𝔭 h𝔭 hq ≠ annulusBranchYPoint R I q 𝔭 h𝔭 hq := by
  intro hcon
  have hmem : fibreX R I q ∈ (annulusBranchXPoint R I q 𝔭 h𝔭 hq).asIdeal := by
    rw [hcon, mem_annulusBranchYPoint_iff]
    exact annulusBranchY_fibreX R I q 𝔭 h𝔭 hq
  rw [mem_annulusBranchXPoint_iff, annulusBranchX_fibreX] at hmem
  exact Polynomial.X_ne_zero hmem

include h𝔭 hq in
/-- **The `x`-branch generic point lies in the chosen chart domain `D(x + y − 1)`**: the branch
evaluates `x + y − 1` to `X − 1`, which is nonzero. -/
theorem annulusBranchXPoint_mem_tateInvNodeChartLocus :
    (annulusBranchXPoint R I q 𝔭 h𝔭 hq : PrimeSpectrum (annulusFibre R I q)) ∈
      tateInvNodeChartLocus R I q := by
  refine mem_tateInvNodeChartLocus_iff.mpr ?_
  rw [mem_annulusBranchXPoint_iff]
  simp only [map_sub, map_add, map_one, annulusBranchX_fibreX, annulusBranchX_fibreY, add_zero]
  simpa using Polynomial.X_sub_C_ne_zero (1 : R ⧸ 𝔭)

include h𝔭 hq in
/-- **The `y`-branch generic point lies in the chosen chart domain too**, the mirror of
`annulusBranchXPoint_mem_tateInvNodeChartLocus`. -/
theorem annulusBranchYPoint_mem_tateInvNodeChartLocus :
    (annulusBranchYPoint R I q 𝔭 h𝔭 hq : PrimeSpectrum (annulusFibre R I q)) ∈
      tateInvNodeChartLocus R I q := by
  refine mem_tateInvNodeChartLocus_iff.mpr ?_
  rw [mem_annulusBranchYPoint_iff]
  simp only [map_sub, map_add, map_one, annulusBranchY_fibreX, annulusBranchY_fibreY, zero_add]
  simpa using Polynomial.X_sub_C_ne_zero (1 : R ⧸ 𝔭)

end Branch

section Chart

variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hI : I.FG)
variable (𝔭 : Ideal R) [𝔭.IsPrime] (h𝔭 : I ≤ 𝔭) (hq : q ∈ I)

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
include hI h𝔭 hq in
/-- **The `x`-chart image of the overlap generic point is the `x`-branch generic point.** This is
`annulusChartEvalLaurentFibre_comp_chartX` read on prime spectra: the kernel of
`toLaurent ∘ annulusBranchX` is the kernel of `annulusBranchX`, because `D[X] ↪ D[T, T⁻¹]` is
injective. The specialization statement `annulusOverlapChart_genericPoint_specializes` is drawn
from the same identity but keeps only a containment; here the point itself is named. -/
theorem annulusOverlapChart_base_annulusOverlapGenericPoint :
    (annulusOverlapChart R I q).base (annulusOverlapGenericPoint R I q hI 𝔭 h𝔭) =
      annulusBranchXPoint R I q 𝔭 h𝔭 hq := by
  change PrimeSpectrum.comap (Ideal.quotientMap
      (awayCompletionIdeal (annulusIdealOfDefinition R I q) (overlapX R I q))
      (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q))
      (le_comap_awayCompletionHom _ _)) (annulusOverlapGenericPoint R I q hI 𝔭 h𝔭) =
    annulusBranchXPoint R I q 𝔭 h𝔭 hq
  rw [annulusOverlapGenericPoint, ← PrimeSpectrum.comap_comp_apply,
    annulusChartEvalLaurentFibre_comp_chartX R I q hI 𝔭 h𝔭 hq, PrimeSpectrum.comap_comp_apply,
    annulusBranchXPoint]
  refine congrArg _ (PrimeSpectrum.ext ?_)
  change Ideal.comap (Polynomial.toLaurent (R := R ⧸ 𝔭)) ⊥ = ⊥
  rw [← RingHom.ker_eq_comap_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).mp Polynomial.toLaurent_injective

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
include hI h𝔭 hq in
/-- **The transported `y`-chart image of the *same* overlap generic point is the `y`-branch generic
point.** Mirror of `annulusOverlapChart_base_annulusOverlapGenericPoint`, over
`annulusChartEvalLaurentFibre_comp_transitionedChartY`; the extra injective factor is the inversion
`T ↦ T⁻¹`, which is where the gluing `x_n · y_{n+1} = 1` enters. -/
theorem annulusOverlapChartY_base_transition_annulusOverlapGenericPoint :
    (annulusOverlapChartY R I q).base
        ((annulusChartTransitionInvSpf R I q hI).hom.base
          (annulusOverlapGenericPoint R I q hI 𝔭 h𝔭)) =
      annulusBranchYPoint R I q 𝔭 h𝔭 hq := by
  rw [annulusOverlapChartY_base_transition_eq_comap_annulusTransitionedChartY R I q hI
      (annulusOverlapGenericPoint R I q hI 𝔭 h𝔭),
    annulusOverlapGenericPoint, ← PrimeSpectrum.comap_comp_apply,
    annulusChartEvalLaurentFibre_comp_transitionedChartY R I q hI 𝔭 h𝔭 hq,
    PrimeSpectrum.comap_comp_apply, annulusBranchYPoint]
  refine congrArg _ (PrimeSpectrum.ext ?_)
  change Ideal.comap ((LaurentPolynomial.invert (R := R ⧸ 𝔭)).toRingHom.comp
    Polynomial.toLaurent) ⊥ = ⊥
  rw [← RingHom.ker_eq_comap_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).mp
    (LaurentPolynomial.invert.injective.comp Polynomial.toLaurent_injective)

end Chart

section Quotient

variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)
variable {Q : LocallyRingedSpace.{u}} {π : (tateChainInv R I q hq hI).toLocallyRingedSpace ⟶ Q}
variable (𝔭 : Ideal R) [𝔭.IsPrime] (h𝔭 : I ≤ 𝔭)

include hq hI h𝔭 in
/-- **The two branch generic points have the same image in the quotient.** They are the two images
of one overlap point, in the patches `U_0` and `U_1` respectively
(`base_ι_annulusOverlapChart_eq`), and the projection of an action quotient does not see the patch
index (`base_ι_eq_of_isActionQuotient`). This is the Néron 1-gon gluing `0` to `∞`, at the level of
points. -/
theorem base_actionQuotientπ_ι_annulusBranchXPoint_eq
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) :
    π.base (((tateChainInvFormalGlueData R I q hq hI).ι ⟨(0 : ℤ)⟩).base
        (annulusBranchXPoint R I q 𝔭 h𝔭 hq)) =
      π.base (((tateChainInvFormalGlueData R I q hq hI).ι ⟨(0 : ℤ)⟩).base
        (annulusBranchYPoint R I q 𝔭 h𝔭 hq)) := by
  rw [← annulusOverlapChart_base_annulusOverlapGenericPoint R I q hI 𝔭 h𝔭 hq,
    ← annulusOverlapChartY_base_transition_annulusOverlapGenericPoint R I q hI 𝔭 h𝔭 hq,
    base_ι_annulusOverlapChart_eq R I q hq hI (annulusOverlapGenericPoint R I q hI 𝔭 h𝔭)]
  exact base_ι_eq_of_isActionQuotient R I q hq hI h 1 (by norm_num) _

include hq hI h𝔭 in
/-- **The projection is not injective on the saturated chart domain.** The two branch generic
points both lie in `D(x + y − 1)` and both sit in the saturation through the patch `U_0`, they are
distinct, and they have one image. So the candidate node chart is *not* obtained by restricting
`π` to an open on which it is injective — which is the expected shape of the Néron 1-gon's node
and the reason goals 1 and 2 of this row went through invariant sections. -/
theorem not_injOn_base_tateInvSaturate_tateInvNodeChartLocus
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) :
    ¬ Set.InjOn π.base (tateInvSaturate R I q hq hI (tateInvNodeChartLocus R I q)) := by
  intro hinj
  refine annulusBranchXPoint_ne_annulusBranchYPoint R I q 𝔭 h𝔭 hq ?_
  refine ((tateChainInvFormalGlueData R I q hq hI).ι_isOpenImmersion
    ⟨(0 : ℤ)⟩).base_open.injective (hinj ?_ ?_
      (base_actionQuotientπ_ι_annulusBranchXPoint_eq R I q hq hI 𝔭 h𝔭 h))
  · exact image_ι_subset_tateInvSaturate hq hI _ ⟨(0 : ℤ)⟩
      ⟨_, annulusBranchXPoint_mem_tateInvNodeChartLocus R I q 𝔭 h𝔭 hq, rfl⟩
  · exact image_ι_subset_tateInvSaturate hq hI _ ⟨(0 : ℤ)⟩
      ⟨_, annulusBranchYPoint_mem_tateInvNodeChartLocus R I q 𝔭 h𝔭 hq, rfl⟩

include hq hI h𝔭 in
/-- **The ambient morphism of the node chart is not injective on points.** Both branch generic
points lie in `D(x + y − 1)`, which is the range of the basic-open chart
(`FormalSpectrum.range_basicOpenChart_base`), so both are hit; their two preimages are distinct and
have one image. -/
theorem not_injective_base_tateInvNodeChartAmbientHom
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) :
    ¬ Function.Injective ⇑(tateInvNodeChartAmbientHom R I q hq hI (π := π)).base := by
  haveI _hann : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  intro hinj
  have hrange : Set.range (FormalSpectrum.basicOpenChart (annulusIdealOfDefinition R I q)
      (annulusNodeChartCoord R I q)).base = tateInvNodeChartLocus R I q :=
    range_basicOpenChart_base _ _ (annulusIdealOfDefinition_fg R I q hI)
  obtain ⟨a, ha⟩ : annulusBranchXPoint R I q 𝔭 h𝔭 hq ∈
      Set.range (FormalSpectrum.basicOpenChart (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q)).base := by
    rw [hrange]
    exact annulusBranchXPoint_mem_tateInvNodeChartLocus R I q 𝔭 h𝔭 hq
  obtain ⟨b, hb⟩ : annulusBranchYPoint R I q 𝔭 h𝔭 hq ∈
      Set.range (FormalSpectrum.basicOpenChart (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q)).base := by
    rw [hrange]
    exact annulusBranchYPoint_mem_tateInvNodeChartLocus R I q 𝔭 h𝔭 hq
  have hcomp : ∀ z, (tateInvNodeChartAmbientHom R I q hq hI (π := π)).base z =
      π.base (((tateChainInvFormalGlueData R I q hq hI).ι ⟨(0 : ℤ)⟩).base
        ((FormalSpectrum.basicOpenChart (annulusIdealOfDefinition R I q)
          (annulusNodeChartCoord R I q)).base z)) := fun _ => rfl
  have hab : (tateInvNodeChartAmbientHom R I q hq hI (π := π)).base a =
      (tateInvNodeChartAmbientHom R I q hq hI (π := π)).base b := by
    rw [hcomp, hcomp, ha, hb]
    exact base_actionQuotientπ_ι_annulusBranchXPoint_eq R I q hq hI 𝔭 h𝔭 h
  refine annulusBranchXPoint_ne_annulusBranchYPoint R I q 𝔭 h𝔭 hq ?_
  rw [← ha, ← hb, hinj hab]

include hq hI h𝔭 in
/-- **So the ambient morphism is not an open immersion**, and the candidate `f` of
`exists_formalScheme_of_openImmersion_spf_quotientIdeal_of_isLeftRegular_base` whose range is
*equal* to the required set is refuted. See this file's module docstring for what that does and does
not say about `hnode`. -/
theorem not_isOpenImmersion_tateInvNodeChartAmbientHom
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) :
    ¬ LocallyRingedSpace.IsOpenImmersion
      (tateInvNodeChartAmbientHom R I q hq hI (π := π)) := fun hopen =>
  not_injective_base_tateInvNodeChartAmbientHom R I q hq hI 𝔭 h𝔭 h hopen.base_open.injective

end Quotient

section Conclusion

variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)
variable {Q : LocallyRingedSpace.{u}} {π : (tateChainInv R I q hq hI).toLocallyRingedSpace ⟶ Q}

include hq hI in
/-- **The hypothesis-free form**: `I ≠ ⊤` — that is, `Spf R` nonempty — is all that is needed, by
the same maximal-ideal step as `not_isFreeProperlyDiscontinuous_tateInvPeriodAction`. -/
theorem not_isOpenImmersion_tateInvNodeChartAmbientHom_of_ne_top (hItop : I ≠ ⊤)
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) :
    ¬ LocallyRingedSpace.IsOpenImmersion
      (tateInvNodeChartAmbientHom R I q hq hI (π := π)) := by
  obtain ⟨𝔪, h𝔪, h𝔪le⟩ := Ideal.exists_le_maximal I hItop
  haveI : 𝔪.IsPrime := h𝔪.isPrime
  exact not_isOpenImmersion_tateInvNodeChartAmbientHom R I q hq hI 𝔪 h𝔪le h

include hq hI in
/-- **The same for the projection on the saturated chart domain**, and the form the row's status
section quotes: the node chart cannot be cut out of the chain by an open on which `π` is injective.
-/
theorem not_injOn_base_tateInvSaturate_tateInvNodeChartLocus_of_ne_top (hItop : I ≠ ⊤)
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) :
    ¬ Set.InjOn π.base (tateInvSaturate R I q hq hI (tateInvNodeChartLocus R I q)) := by
  obtain ⟨𝔪, h𝔪, h𝔪le⟩ := Ideal.exists_le_maximal I hItop
  haveI : 𝔪.IsPrime := h𝔪.isPrime
  exact not_injOn_base_tateInvSaturate_tateInvNodeChartLocus R I q hq hI 𝔪 h𝔪le h

include hq hI in
/-- **Non-vacuity, as an application rather than a restatement.** The two points are exhibited, not
merely denied to be equal: `D(x + y − 1)` carries two distinct points of the model patch with one
image in the quotient. This is strictly stronger than
`AlgebraicGeometry.nonempty_range_tateInvNodeChartAmbientHom`
(`FormalSchemes.TateInvNodeChartSpfNonempty`), which it implies, and it needs the same `I ≠ ⊤`.
-/
theorem exists_ne_and_base_actionQuotientπ_ι_eq (hItop : I ≠ ⊤)
    (h : IsActionQuotient (tateInvPeriodAction R I q hq hI) π) :
    ∃ a b : FormalSpectrum.locallyRingedSpaceObj (annulusIdealOfDefinition R I q),
      a ≠ b ∧ a ∈ tateInvNodeChartLocus R I q ∧ b ∈ tateInvNodeChartLocus R I q ∧
        π.base (((tateChainInvFormalGlueData R I q hq hI).ι ⟨(0 : ℤ)⟩).base a) =
          π.base (((tateChainInvFormalGlueData R I q hq hI).ι ⟨(0 : ℤ)⟩).base b) := by
  obtain ⟨𝔪, h𝔪, h𝔪le⟩ := Ideal.exists_le_maximal I hItop
  haveI : 𝔪.IsPrime := h𝔪.isPrime
  exact ⟨annulusBranchXPoint R I q 𝔪 h𝔪le hq, annulusBranchYPoint R I q 𝔪 h𝔪le hq,
    annulusBranchXPoint_ne_annulusBranchYPoint R I q 𝔪 h𝔪le hq,
    annulusBranchXPoint_mem_tateInvNodeChartLocus R I q 𝔪 h𝔪le hq,
    annulusBranchYPoint_mem_tateInvNodeChartLocus R I q 𝔪 h𝔪le hq,
    base_actionQuotientπ_ι_annulusBranchXPoint_eq R I q hq hI 𝔪 h𝔪le h⟩

end Conclusion

end AlgebraicGeometry
