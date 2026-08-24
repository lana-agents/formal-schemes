import FormalSchemes.ThickeningBasicOpenRefinement
import FormalSchemes.FormalLineWitness

set_option linter.style.header false

/-!
# A non-degenerate witness for the cover pullback and its basic-open refinement

`FormalSchemes/ThickeningCoverPullback.lean` pulls an open cover of a locally ringed space `X`
back to `|Spf R|` along the common base map of a compatible family, and
`FormalSchemes/ThickeningBasicOpenRefinement.lean` refines the result by basic opens `D(r)`.
Both modules carry a concrete witness, and in both the witness is **degenerate on the conclusion
side**: they are instantiated at the `2`-adic integers, where `FormalSpectrum I` is
`PrimeSpectrum (ℤ^ ⧸ 2ℤ^) = PrimeSpectrum 𝔽₂`, a one-point space. Every open of a one-point space
is `⊥` or `⊤`, so the pulled-back cover there always has a member equal to `⊤` and the refinement
is always a single basic open equal to `⊤`. The non-degeneracy those modules could exhibit was on
the *hypothesis* side only: a genuine two-piece cover `Spec ℤ = D(2) ∪ D(3)` of the **target**.

`FormalSchemes/FormalLineWitness.lean` removed the obstruction. For `ℤ⟦X⟧`, the `(X)`-adic
completion of `ℤ[X]`, the residue ring is `ℤ`, so `|Spf ℤ⟦X⟧| ≃ₜ Spec ℤ` is infinite and carries
the two-piece cover `twoChart` with neither member equal to `⊤`. This file instantiates the two
theorems there, where the **conclusion** is non-degenerate too.

## Main results

* `FormalSpectrum.pulled`: the cover of `|Spf ℤ⟦X⟧|` obtained by pulling `twoChart` back along the
  common base map of the tautological family, with `iSup_pulled` that it covers.
* `FormalSpectrum.pulled_ne_top`: **neither member is `⊤`.** This is the point of the file, and at
  the `2`-adic witness it is not merely hard but false.
* `FormalSpectrum.exists_refinement_ne_top`: the basic-open refinement of that cover has **no**
  member equal to `⊤` either, while still covering.
* `FormalSpectrum.exists_finite_refinement_two_le_card`: the finite subcover of the refinement
  needs **at least two** basic opens. This is the sharpest form of "genuinely multi-piece"
  available for an existential statement, and it is what the degenerate witnesses cannot say.

## Implementation notes

The family used is the tautological one, `thickeningMap I n : Spec (R ⧸ I ^ (n + 1)) ⟶ Spf R`,
compatible by `thickeningMap_comp`. Its common base map is the identity (`commonBase_taut`), which
is what makes the pulled-back cover *equal* to the cover one started from (`pulled_eq`) rather than
merely comparable to it — so the non-degeneracy of `twoChart` transfers verbatim.

`twoChart` has type `Bool → Opens (FormalSpectrum formalLineIdeal)`, while the `commonBase` API
produces opens of `TopCat.of (FormalSpectrum formalLineIdeal)`. These are definitionally equal at
**default** transparency — so `iSup_map_commonBase_obj_eq_top … twoChart iSup_twoChart` typechecks
with no bridging at all — but not at `instances` transparency, so `rw [commonBase_taut]` fails
against such a goal with an application type mismatch on `Quiver.Hom`. `simp only
[commonBase_taut]` fires where `rw` does not, because it elaborates the motive differently. Per the
standing diagnosis on this tree, two `rw` spellings failing and a third tactic succeeding means the
**tactic** was wrong, not the transparency; this file sets no option beyond the header linter.

Nothing here edits a landed module. In particular the `private` `Spec ℤ = D(2) ∪ D(3)` helpers
duplicated in `ThickeningCoverPullback.lean` and `ThickeningBasicOpenRefinement.lean` are left
alone: this file needs none of them, so it is not the third consumer whose arrival those modules
name as the trigger to extract them.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6 (10.6.10).
* [The Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Polynomial

namespace FormalSpectrum

/-- **A cover with no member equal to `⊤` needs at least two members.** Stated for an arbitrary
family of opens of a nonempty space; the empty `Finset` is ruled out by `⊥ ≠ ⊤` and a singleton by
the hypothesis itself. -/
private theorem two_le_card_of_iSup_eq_top {α : Type*} [TopologicalSpace α] [Nonempty α]
    {ι : Type*} {V : ι → Opens α} {s : Finset ι} (hs : (⨆ x ∈ s, V x) = ⊤)
    (hne : ∀ x, V x ≠ ⊤) : 2 ≤ s.card := by
  rcases Finset.eq_empty_or_nonempty s with rfl | ⟨y, hy⟩
  · simp only [Finset.notMem_empty, iSup_false, iSup_bot] at hs
    exact absurd hs bot_ne_top
  · haveI : Nonempty ι := ⟨y⟩
    by_contra hcard
    obtain ⟨x₀, hx₀⟩ := (Finset.card_le_one_iff_subset_singleton (s := s)).mp (by omega)
    refine hne x₀ (eq_top_iff.mpr ?_)
    rw [← hs]
    refine iSup_le fun x => iSup_le fun hx => ?_
    rw [Finset.mem_singleton.mp (hx₀ hx)]

attribute [local instance] isAdicRing_formalLineIdeal

/-- **The two-piece cover of `Spec ℤ = |Spf ℤ⟦X⟧|`, pulled back along the common base map** of the
tautological family out of the thickenings of `ℤ⟦X⟧`. -/
def pulled : Bool → Opens (TopCat.of (FormalSpectrum formalLineIdeal)) :=
  fun b => (Opens.map (commonBase formalLineIdeal (thickeningMap formalLineIdeal))).obj
    (twoChart b)

/-- **The pulled-back cover covers**, by `iSup_map_commonBase_obj_eq_top`. -/
theorem iSup_pulled : ⨆ b, pulled b = ⊤ :=
  iSup_map_commonBase_obj_eq_top formalLineIdeal (thickeningMap formalLineIdeal)
    twoChart iSup_twoChart

/-- **The tautological family has the identity as its common base map.** Read off at level `0`,
where `commonBase` is by definition `(thickeningTopIso I 0).hom ≫ (thickeningMap I 0).base` and the
second factor is `(thickeningTopIso I 0).inv`. -/
theorem commonBase_taut : commonBase formalLineIdeal (thickeningMap formalLineIdeal) =
    𝟙 (TopCat.of (FormalSpectrum formalLineIdeal)) :=
  (commonBase_eq formalLineIdeal (thickeningMap formalLineIdeal)
    (thickeningMap_comp formalLineIdeal) 0).trans (Iso.hom_inv_id _)

/-- Pulling back along the identity changes nothing, so the pulled-back cover **is** `twoChart`. -/
theorem pulled_eq (b : Bool) : pulled b = twoChart b := by
  simp only [pulled, commonBase_taut]
  exact Opens.map_id_obj _

/-- **Neither member of the pulled-back cover is `⊤`.** This is the first genuinely non-degenerate
conclusion under this umbrella: at `twoAdicIdeal` the analogous statement is false, because
`|Spf ℤ^|` is a one-point space and its only nonempty open is `⊤`. -/
theorem pulled_ne_top (b : Bool) : pulled b ≠ ⊤ := by
  rw [pulled_eq]
  exact twoChart_ne_top b

/-- **The basic-open refinement is non-degenerate too**: `exists_basicOpen_refinement`
instantiated at `ℤ⟦X⟧`, together with the fact that no member of the refinement is `⊤` — each is
contained in a member of the pulled-back cover, and those are not `⊤`. -/
theorem exists_refinement_ne_top :
    ∃ (r : FormalSpectrum formalLineIdeal → AdicCompletion polyXIdeal ℤ[X])
      (idx : FormalSpectrum formalLineIdeal → Bool),
      (⨆ x, basicOpen formalLineIdeal (r x)) = ⊤ ∧
        (∀ x, basicOpen formalLineIdeal (r x) ≤ pulled (idx x)) ∧
          ∀ x, basicOpen formalLineIdeal (r x) ≠ ⊤ := by
  obtain ⟨r, idx, hcov, hle⟩ :=
    exists_basicOpen_refinement formalLineIdeal (thickeningMap formalLineIdeal)
      twoChart iSup_twoChart
  refine ⟨r, idx, hcov, hle, fun x hx => pulled_ne_top (idx x) ?_⟩
  exact eq_top_iff.mpr (hx ▸ hle x)

/-- **At least two basic opens are needed.** `exists_finite_basicOpen_refinement` instantiated at
`ℤ⟦X⟧`, sharpened by `two_le_card_of_iSup_eq_top`: the finite refinement covers, no member of it is
`⊤`, and therefore it has at least two members. A statement of this shape is unavailable at the
`2`-adic witness, where the refinement is always the single open `⊤`. -/
theorem exists_finite_refinement_two_le_card :
    ∃ (r : FormalSpectrum formalLineIdeal → AdicCompletion polyXIdeal ℤ[X])
      (idx : FormalSpectrum formalLineIdeal → Bool)
      (s : Finset (FormalSpectrum formalLineIdeal)),
      (⨆ x ∈ s, basicOpen formalLineIdeal (r x)) = ⊤ ∧
        (∀ x, basicOpen formalLineIdeal (r x) ≤ pulled (idx x)) ∧
          (∀ x, basicOpen formalLineIdeal (r x) ≠ ⊤) ∧ 2 ≤ s.card := by
  haveI := nontrivial_formalSpectrum
  obtain ⟨r, idx, s, hcov, hle⟩ :=
    exists_finite_basicOpen_refinement formalLineIdeal (thickeningMap formalLineIdeal)
      twoChart iSup_twoChart
  have hne : ∀ x, basicOpen formalLineIdeal (r x) ≠ ⊤ :=
    fun x hx => pulled_ne_top (idx x) (eq_top_iff.mpr (hx ▸ hle x))
  exact ⟨r, idx, s, hcov, hle, hne, two_le_card_of_iSup_eq_top hcov hne⟩

end FormalSpectrum

end
