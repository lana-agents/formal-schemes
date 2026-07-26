import FormalSchemes.TateAction
import FormalSchemes.AnnulusNontrivial

set_option linter.style.header false

/-!
# Freeness of the `q^ℤ`-period action on the formal Tate chain (large periods)

Fix an adic base `(R, I)` with `I` finitely generated, Noetherian `R`, and a topologically nilpotent
Tate parameter `q ∈ I`. The `q^ℤ`-period action `tatePeriodAction : ℤ → Aut T`
(`FormalSchemes.TateAction`) sends `n` to the `n`-fold shift `σⁿ` of the formal Tate chain `T`.

This file establishes the **large-period freeness** of that action: for `I ≠ ⊤` and any `n` with
`|n| ≥ 2` (i.e. `n ∉ {−1, 0, 1}`) the automorphism `σⁿ` is **not** the identity. The argument
combines two merged inputs:

* proper discontinuity (`tateShift_properlyDiscontinuous`): the patch `U₀` is disjoint from its
  translate `σⁿ(U₀) = U_n` for `n ∉ {−1, 0, 1}`;
* nonemptiness of the patch (`annulus_formalSpectrum_nonempty`): for `I ≠ ⊤` the underlying space of
  `Spf A` is nonempty.

If `σⁿ = 𝟙` then `U₀` and `σⁿ(U₀)` coincide, so a nonempty set would be disjoint from itself — a
contradiction. This rules out every nontrivial period of absolute value `≥ 2`, reducing full
freeness of the `q^ℤ`-action to the single remaining case `n = ±1` (which additionally needs the
`x`-chart `D(x)` to be a *proper* open of `U₀`, i.e. `D(x) ≠ ⊤` — the annulus coordinate `x` a
non-unit in the special fibre — plus an image-intersection lemma at the locally-ringed-space level;
see the module note at the end).

## Main results

* `tateChain_range_ι_base_nonempty`: for `I ≠ ⊤`, the image of each patch inclusion `ι i` in `T` is
  nonempty.
* `tateShiftAut_zpow_ne_one`: for `I ≠ ⊤` and `n ∉ {−1, 0, 1}`, `σⁿ ≠ 𝟙`.
* `tatePeriodAction_apply_ne_one`: the same, phrased for the period action `tatePeriodAction`.
* `tateShiftAut_zpow_eq_one_imp`: if `σⁿ = 𝟙` then `n ∈ {−1, 0, 1}` (large-period freeness in
  eliminated form).

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*], Ch. V (the Tate curve).
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The image of each patch inclusion is nonempty.** For `I ≠ ⊤` the underlying space of the
annulus patch `Spf A` is nonempty (`annulus_formalSpectrum_nonempty`), so the range of the inclusion
`ι i : U i ⟶ T` is a nonempty subset of `T`. -/
theorem tateChain_range_ι_base_nonempty (hItop : I ≠ ⊤) (i : ULift.{u} ℤ) :
    (Set.range ((tateChainFormalGlueData R I q hq hI).ι i).base).Nonempty := by
  obtain ⟨p⟩ := annulus_formalSpectrum_nonempty R I q hq hItop
  exact ⟨_, Set.mem_range_self p⟩

/-- **Large-period freeness of the `q^ℤ`-action.** For `I ≠ ⊤` and any period `n` with `|n| ≥ 2`
(that is `n ∉ {−1, 0, 1}`), the shift power `σⁿ` is not the identity automorphism of the formal Tate
chain `T`. Indeed if `σⁿ = 𝟙` then the inclusion of `U₀` and its translate `ι₀ ≫ σⁿ = ι_n` have the
same range, so proper discontinuity (`tateShift_properlyDiscontinuous`) would force that nonempty
range to be disjoint from itself. -/
theorem tateShiftAut_zpow_ne_one {n : ℤ} (hItop : I ≠ ⊤)
    (hn0 : n ≠ 0) (hn1 : n ≠ 1) (hnm1 : n ≠ -1) :
    (tateShiftAut R I q hq hI) ^ n ≠ 1 := by
  intro h
  have hpd := tateShift_properlyDiscontinuous R I q hq hI ⟨0⟩ n hn0 hn1 hnm1
  have hhom : ((tateShiftAut R I q hq hI) ^ n).hom = 𝟙 _ := by rw [h]; rfl
  have hBA : (tateChainFormalGlueData R I q hq hI).ι ⟨0⟩ ≫ ((tateShiftAut R I q hq hI) ^ n).hom =
      (tateChainFormalGlueData R I q hq hI).ι ⟨0⟩ := by rw [hhom]; exact Category.comp_id _
  obtain ⟨x, hx⟩ := tateChain_range_ι_base_nonempty R I q hq hI hItop ⟨0⟩
  have hxB : x ∈ Set.range ((tateChainFormalGlueData R I q hq hI).ι ⟨0⟩ ≫
      ((tateShiftAut R I q hq hI) ^ n).hom).base := by rw [hBA]; exact hx
  exact (Set.disjoint_left.mp hpd hx) hxB

/-- **Large-period freeness, in eliminated form.** If a shift power `σⁿ` is the identity (with
`I ≠ ⊤`) then the period `n` lies in `{−1, 0, 1}`: no period of absolute value `≥ 2` fixes `T`. Full
freeness (`σⁿ = 𝟙 ⇒ n = 0`) then reduces to excluding `n = ±1`. -/
theorem tateShiftAut_zpow_eq_one_imp {n : ℤ} (hItop : I ≠ ⊤)
    (h : (tateShiftAut R I q hq hI) ^ n = 1) : n = 0 ∨ n = 1 ∨ n = -1 := by
  by_contra hc
  rw [not_or, not_or] at hc
  exact tateShiftAut_zpow_ne_one R I q hq hI hItop hc.1 hc.2.1 hc.2.2 h

/-- **Large-period freeness for the period action** `tatePeriodAction : ℤ → Aut T`: for `I ≠ ⊤` and
`n ∉ {−1, 0, 1}` the action element `tatePeriodAction n` is nontrivial. -/
theorem tatePeriodAction_apply_ne_one {n : ℤ} (hItop : I ≠ ⊤)
    (hn0 : n ≠ 0) (hn1 : n ≠ 1) (hnm1 : n ≠ -1) :
    tatePeriodAction R I q hq hI (Multiplicative.ofAdd n) ≠ 1 := by
  rw [tatePeriodAction_apply]
  simpa using tateShiftAut_zpow_ne_one R I q hq hI hItop hn0 hn1 hnm1

end AlgebraicGeometry
