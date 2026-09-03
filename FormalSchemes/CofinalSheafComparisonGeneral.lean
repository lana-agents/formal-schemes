import FormalSchemes.CofinalAdicRing
import FormalSchemes.CofinalSheafComparisonIso
import FormalSchemes.LargestIdealOfDefinition

set_option linter.style.header false

/-!
# Ideal-independence of `Spf`, the general (non-nested) case (EGA I, §10.3, goal 1)

`FormalSchemes/CofinalSheafComparisonIso.lean` (`FormalSpectrum.cofinalSpfIso`) produced the
isomorphism of locally ringed spaces `Spf_I R ≅ Spf_J R` for two ideals of definition `I ≤ J`
(the *nested* case). This file removes the nesting hypothesis: for **two arbitrary ideals of
definition** `I J : Ideal R` of the same adic ring, `Spf_I R` and `Spf_J R` are isomorphic. This
closes goal 1 of the structure-sheaf intertwining (EGA I §10.3) in full — `Spf R` depends only on
the topological ring `R`, not on the chosen ideal of definition.

## Route

Set `K := I * J`. Then `K ≤ I` and `K ≤ J` are both *nested* comparisons, so — once `K` is known to
be an ideal of definition — the two nested isomorphisms `cofinalSpfIso K I` and `cofinalSpfIso K J`
compose to `Spf_I R ≅ Spf_K R ≅ Spf_J R`.

The work is in exhibiting `K = I * J` as an ideal of definition (`IsAdicRing K`):

* `K` is finitely generated (`Ideal.FG.mul`) and cofinal with `I`: `K ≤ I` and, since some power
  `I ^ m ≤ J` (`IsAdic.exists_pow_le`), `I ^ (m+1) = I ^ m * I ≤ J * I = K`. Being squeezed
  `I ^ (m+1) ≤ K ≤ I` between cofinal powers of `I`, `K` carries the same adic topology
  (`IsAdic K`), via `is_ideal_adic_pow` + `IsAdic.of_le_of_pow_le`.
* `K`-adic completeness is transferred from `I`-adic completeness purely algebraically:
  `IsHausdorff` is antitone in the ideal (`IsHausdorff.of_le`, only `K ≤ I` needed) and
  `IsPrecomplete` transfers under cofinality — `IsPrecomplete.of_isCofinal`
  (`FormalSchemes.CofinalAdicRing`), applied to the cofinality that
  `Ideal.IsCofinal.of_le_of_pow_le` builds out of `K ≤ I` and `I ^ c ≤ K`. We cannot route through
  `IsAdic.isAdicComplete_iff` here, as that requires a `UniformSpace R` instance not present in
  the adic-ring setting.

## Main definitions and results

* `IsHausdorff.of_le`: the `IsHausdorff` half of the transfer, which needs only `K ≤ I` (a general
  commutative-algebra lemma; a candidate for Mathlib / an earlier file). The `IsPrecomplete` half
  is not restated here: it is `IsPrecomplete.of_isCofinal` (`FormalSchemes.CofinalAdicRing`) at a
  containment read as a cofinality.
* `FormalSpectrum.generalCofinalSpfIso`: the isomorphism `Spf_I R ≅ Spf_J R` for two arbitrary
  ideals of definition `I`, `J`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], §10.3.
* [The Stacks Project, Tag 0AHZ](https://stacks.math.columbia.edu/tag/0AHZ).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

section CompletenessTransfer

variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]

/-- **`IsHausdorff` is antitone in the ideal.** If `K ≤ I` and `M` is `I`-adically Hausdorff, then
`M` is `K`-adically Hausdorff: an element in every `K ^ n • ⊤` lies in every `I ^ n • ⊤`. -/
theorem IsHausdorff.of_le {K I : Ideal R} (hKI : K ≤ I) [h : IsHausdorff I M] :
    IsHausdorff K M where
  haus' x hx :=
    h.haus x fun n => (hx n).mono (Submodule.smul_mono_left (Ideal.pow_right_mono hKI n))

end CompletenessTransfer

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I J : Ideal R)
  [IsAdicRing I] [IsAdicRing J]

/-- **The formal spectra of two arbitrary ideals of definition are isomorphic** (EGA I, §10.3,
goal 1). For an adic ring `R` with two ideals of definition `I`, `J` (no nesting assumed), the
affine formal schemes `Spf_I R` and `Spf_J R` are isomorphic as locally ringed spaces: `Spf R`
depends only on the topological ring `R`, not on the chosen ideal of definition. The proof factors
through the product `K = I * J`, which is again an ideal of definition and is nested below both `I`
and `J`, so the merged nested isomorphism `cofinalSpfIso` applies twice. -/
def generalCofinalSpfIso (hI : I.FG) (hJ : J.FG) :
    locallyRingedSpaceObj I ≅ locallyRingedSpaceObj J := by
  have hIadic : IsAdic I := IsAdicRing.isAdic
  have hJadic : IsAdic J := IsAdicRing.isAdic
  haveI : IsTopologicalRing R := hIadic.isTopologicalRing
  -- `K := I * J` is nested below both, and cofinal with `I`.
  have hKI : (I * J : Ideal R) ≤ I := by rw [mul_comm]; exact Ideal.mul_le_left
  have hKJ : (I * J : Ideal R) ≤ J := Ideal.mul_le_left
  -- Some power `I ^ (c+1)` of `I` lies in `K = I * J`, so `K` is cofinal with `I`.
  have hIcK : ∃ c : ℕ, I ^ (c + 1) ≤ I * J := by
    obtain ⟨m, hm⟩ := IsAdic.exists_pow_le hJadic hIadic
    refine ⟨m, ?_⟩
    rw [pow_succ]
    calc I ^ m * I ≤ J * I := Ideal.mul_mono hm le_rfl
      _ = I * J := mul_comm J I
  -- `K` is an ideal of definition: same adic topology (squeezed between cofinal powers of `I`) …
  have hK_adic : IsAdic (I * J) := by
    obtain ⟨c, hc⟩ := hIcK
    exact IsAdic.of_le_of_pow_le (is_ideal_adic_pow hIadic (Nat.succ_pos c)) hc
      (Ideal.pow_right_mono hKI (c + 1))
  -- … and adically complete (Hausdorff antitone, precomplete by cofinality).
  haveI : IsAdicComplete (I * J) R := by
    obtain ⟨c, hc⟩ := hIcK
    exact { toIsHausdorff := IsHausdorff.of_le hKI
            toIsPrecomplete :=
              IsPrecomplete.of_isCofinal (Ideal.IsCofinal.of_le_of_pow_le hKI hc) }
  haveI : IsAdicRing (I * J) := { isAdic := hK_adic }
  have hK_fg : (I * J).FG := hI.mul hJ
  exact (cofinalSpfIso (I * J) I hKI hK_fg hI).symm ≪≫ cofinalSpfIso (I * J) J hKJ hK_fg hJ

/-- **Existence form** of the ideal-independence isomorphism: for any two ideals of definition of an
adic ring, the two formal spectra are isomorphic. -/
theorem nonempty_cofinalSpfIso (hI : I.FG) (hJ : J.FG) :
    Nonempty (locallyRingedSpaceObj I ≅ locallyRingedSpaceObj J) :=
  ⟨generalCofinalSpfIso I J hI hJ⟩

end FormalSpectrum

end
