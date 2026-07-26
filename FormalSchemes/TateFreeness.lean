import FormalSchemes.TateAction
import FormalSchemes.AnnulusNontrivial

set_option linter.style.header false

/-!
# Freeness of the `q^ℤ`-period action on the formal Tate chain (non-adjacent case)

Fix an adic base `(R, I)` with `I` finitely generated, `R` Noetherian and `I ≠ ⊤`, and a
topologically nilpotent Tate parameter `q ∈ I`. The `q^ℤ`-period action
`tatePeriodAction : ℤ → Aut T` (`FormalSchemes.TateAction`) shifts the cover `{U_n}` of the formal
Tate chain `T` by `n ↦ σⁿ` (`ι i ≫ σⁿ = ι ⟨i + n⟩`, the cover-shift law `ι_tateShiftAut_zpow`).

This file proves the **non-adjacent case of freeness**: for any period `n` with `|n| ≥ 2` (i.e.
`n ∉ {−1, 0, 1}`), the power `σⁿ` is *not* the identity automorphism of `T`. Geometrically, if
`σⁿ = 𝟙` then `U_0` would coincide with its translate `U_n = σⁿ(U_0)`; but by proper discontinuity
(`tateShift_properlyDiscontinuous`) a patch is disjoint from its non-adjacent translates, so `U_0`
would be disjoint from itself, forcing its underlying space to be empty — contradicting
`annulus_formalSpectrum_nonempty` (the special fibre `A ⧸ (I·A)` is nontrivial when `I ≠ ⊤`,
`FormalSchemes.AnnulusNontrivial`).

This is the payoff of the merged proper-discontinuity work (`FormalSchemes.TateAction`, issue 135
goal 3) together with the nonemptiness input (`FormalSchemes.AnnulusNontrivial`): the two combine
into genuine freeness away from the neighbouring translates.

## Main results

* `tateShiftAut_zpow_ne_one`: for `n ∉ {−1, 0, 1}`, `σⁿ ≠ 1` in `Aut T`.
* `tatePeriodAction_apply_ne_one`: the same, phrased for the period action `tatePeriodAction`.

## The remaining adjacent case `n = ±1`

Full freeness (`σⁿ = 𝟙 ⟹ n = 0` for *all* `n`) additionally needs the case `n = ±1`, where
`U_0` and its neighbour `U_1` *do* overlap. Ruling this out requires that the overlap
`U_0 ∩ U_1 = D(x) ⊊ U_0` is a *proper* open subset — i.e. the annulus coordinate `x` is a non-unit
in the special fibre `A ⧸ (I·A)` (`D(x) ≠ ⊤`). That non-unit fact is now reachable from the same
augmentation `A → R ⧸ I` used in `AnnulusNontrivial` (it sends `x ↦ 0`, a non-unit of the nontrivial
ring `R ⧸ I`); what is still missing is a *locally-ringed-space image-intersection* lemma
`Set.range (ι i).base ∩ Set.range (ι j).base = (ι i).base '' Set.range (f i j).base` (the LRS
analogue of the topological `TopCat.GlueData.image_inter` used in
`FormalSchemes.GlueDataCarrier`), transporting the proper overlap through `isoCarrier` to
distinguish `Set.range (ι ⟨0⟩).base` from `Set.range (ι ⟨1⟩).base`. That is left as a follow-up.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*], Ch. V (the Tate curve).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)

/-- **Freeness of the `q^ℤ`-action away from the neighbouring translates.** For a period `n` whose
absolute value is at least `2` (`n ∉ {−1, 0, 1}`), the power `σⁿ` of the shift automorphism is not
the identity of `T`, provided `I ≠ ⊤` (so the patches are nonempty).

If `σⁿ = 𝟙` then `ι ⟨0⟩ ≫ σⁿ = ι ⟨0⟩`, so the image of the patch `U_0` equals the image of its
translate `σⁿ(U_0) = U_n`; but `tateShift_properlyDiscontinuous` makes these two images disjoint for
`n ∉ {−1, 0, 1}`, so `U_0` is disjoint from itself, forcing its underlying space to be empty — which
contradicts `annulus_formalSpectrum_nonempty`. -/
theorem tateShiftAut_zpow_ne_one {n : ℤ} (hIt : I ≠ ⊤)
    (hn0 : n ≠ 0) (hn1 : n ≠ 1) (hnm1 : n ≠ -1) :
    (tateShiftAut R I q hq hI) ^ n ≠ 1 := by
  intro hone
  -- Proper discontinuity of the patch `U_0` under the translation by `n`.
  have hpd := tateShift_properlyDiscontinuous R I q hq hI ⟨(0 : ℤ)⟩ n hn0 hn1 hnm1
  -- `σⁿ = 𝟙` collapses `ι ⟨0⟩ ≫ σⁿ` to `ι ⟨0⟩`, so the second range equals the first.
  have hcomp : (tateChainFormalGlueData R I q hq hI).ι ⟨(0 : ℤ)⟩ ≫
        ((tateShiftAut R I q hq hI) ^ n).hom
      = (tateChainFormalGlueData R I q hq hI).ι ⟨(0 : ℤ)⟩ := by
    rw [hone]; exact Category.comp_id _
  rw [hcomp] at hpd
  -- A set disjoint from itself is empty; but the range of `ι ⟨0⟩` is nonempty.
  have hempty := disjoint_self.mp hpd
  haveI : Nonempty
      ((tateChainFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.U ⟨(0 : ℤ)⟩).carrier :=
    annulus_formalSpectrum_nonempty R I q hq hIt
  have hne := Set.range_nonempty
    ⇑(ConcreteCategory.hom ((tateChainFormalGlueData R I q hq hI).ι ⟨(0 : ℤ)⟩).base)
  rw [hempty] at hne
  exact hne.ne_empty Set.bot_eq_empty

/-- **Freeness of the period action away from the neighbouring translates**, phrased for
`tatePeriodAction`. For `n ∉ {−1, 0, 1}` and `I ≠ ⊤`, the period `n` acts on `T` by a non-identity
automorphism. -/
theorem tatePeriodAction_apply_ne_one {n : ℤ} (hIt : I ≠ ⊤)
    (hn0 : n ≠ 0) (hn1 : n ≠ 1) (hnm1 : n ≠ -1) :
    tatePeriodAction R I q hq hI (Multiplicative.ofAdd n) ≠ 1 := by
  rw [tatePeriodAction_apply]
  exact tateShiftAut_zpow_ne_one R I q hq hI hIt hn0 hn1 hnm1

end AlgebraicGeometry
