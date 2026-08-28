import FormalSchemes.ThickeningCoverPullback

set_option linter.style.header false

/-!
# Refining the pulled-back cover by basic opens (EGA I, 10.6.10)

`FormalSchemes/ThickeningCoverPullback.lean` shows that an open cover of `X` pulls back, along the
common base map of a compatible family `f n : Spec (R ⧸ I ^ (n + 1)) ⟶ X`, to an open cover of
`|Spf R|`. This file refines that cover by **basic** opens `D(r)`, `r : R`, and cuts it down to a
finite one.

## Why the raw pullback is not yet a chart decomposition

The opens produced by `iSup_map_commonBase_obj_eq_top` are arbitrary opens of `|Spf R|`, and the
affine theory of `Spf` does not apply to an arbitrary open. What it applies to is a basic open:
`FormalSpectrum.isOpenImmersion_basicOpenChart` (`FormalSchemes/BasicOpenImmersionLRS.lean`)
realises `D(r) ⊆ Spf R` as `Spf R{1/r}`, with `R{1/r} = awayCompletion I r` the completed
localization (`FormalSchemes/BasicOpenChart.lean`), and there is no such statement for a general
open. So between the pullback and the eventual construction of `Spf R ⟶ X` there is a refinement
step, and it is the step EGA takes: 10.6.10 works with the `D(f)` of the ring rather than with the
raw preimages.

The refinement is available because the `D(r)` form a basis of `|Spf R|`
(`FormalSpectrum.isTopologicalBasis_basicOpen`), and it can be taken finite because `|Spf R|` is
quasi-compact (`FormalSpectrum.instSpectralSpace`) — both already on the tree, so this file adds no
Mathlib import and imports nothing beyond `ThickeningCoverPullback`. Like its two predecessors it
is pure topology; the sheaf-theoretic half starts after it.

## Main results

* `FormalSpectrum.exists_basicOpen_le_map_commonBase`: every point of `|Spf R|` lies in a basic
  open contained in the pullback of some member of the cover. The other two are corollaries.
* `FormalSpectrum.exists_basicOpen_refinement`: the basic opens so chosen, one per point, are
  themselves a cover of `|Spf R|` refining the pulled-back one.
* `FormalSpectrum.exists_finite_basicOpen_refinement`: finitely many of them already suffice.

## Implementation notes

`isTopologicalBasis_basicOpen` is a basis of `Set (FormalSpectrum I)`, not of `Opens`
(`FormalSchemes/FormalSpectrum.lean`). Destructuring
`IsTopologicalBasis.exists_subset_of_mem_open` therefore yields an equation
`↑(basicOpen I r) = v` with the coercion on the left, against which `▸` fails — *"invalid `▸`
notation … does not contain the expected result type on either the left or the right hand side"*.
`subst` closes the gap, after which the `Set`-level membership and inclusion satisfy the
`Opens`-level goals definitionally. There is no transparency question here and this file sets no
options beyond the header linter.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6 (10.6.10).
* [The Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable {X : LocallyRingedSpace.{u}}

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Every point of `|Spf R|` lies in a basic open contained in one of the pulled-back charts.**
This is the whole content of the file; the two cover statements below are corollaries of it and of
choice.

No compatibility hypothesis on `f` is needed, for the same reason as in
`iSup_map_commonBase_obj_eq_top`: `commonBase` is read off from the level-`0` member alone. -/
theorem exists_basicOpen_le_map_commonBase {ι : Type*}
    (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X)
    (U : ι → Opens X.toTopCat) (hU : ⨆ i, U i = ⊤) (x : FormalSpectrum I) :
    ∃ (r : R) (i : ι), x ∈ basicOpen I r ∧
      basicOpen I r ≤ (Opens.map (commonBase I f)).obj (U i) := by
  have hx : x ∈ ⨆ i, (Opens.map (commonBase I f)).obj (U i) := by
    rw [iSup_map_commonBase_obj_eq_top I f U hU]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  -- The basis is a family of `Set`s, so `hr` carries a coercion and `▸` will not fire on it.
  obtain ⟨v, ⟨r, hr⟩, hxv, hv⟩ :=
    (isTopologicalBasis_basicOpen I).exists_subset_of_mem_open hi
      ((Opens.map (commonBase I f)).obj (U i)).isOpen
  subst hr
  exact ⟨r, i, hxv, hv⟩

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The pulled-back cover is refined by a cover by basic opens**, indexed by the points of
`|Spf R|`: one basic open `D(r x)` through each point `x`, each contained in the pullback of the
member `U (idx x)` it was chosen inside. -/
theorem exists_basicOpen_refinement {ι : Type*}
    (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X)
    (U : ι → Opens X.toTopCat) (hU : ⨆ i, U i = ⊤) :
    ∃ (r : FormalSpectrum I → R) (idx : FormalSpectrum I → ι),
      (⨆ x, basicOpen I (r x)) = ⊤ ∧
        ∀ x, basicOpen I (r x) ≤ (Opens.map (commonBase I f)).obj (U (idx x)) := by
  choose r idx hmem hle using exists_basicOpen_le_map_commonBase I f U hU
  refine ⟨r, idx, ?_, hle⟩
  rw [eq_top_iff]
  rintro x -
  exact Opens.mem_iSup.mpr ⟨x, hmem x⟩

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Finitely many basic opens already refine the pulled-back cover.** `|Spf R|` is quasi-compact,
being a spectral space (`FormalSpectrum.instSpectralSpace`), so the cover of
`exists_basicOpen_refinement` has a finite subcover — and the containment in the pulled-back charts
is unaffected, since it holds for every index. This is the form the eventual gluing wants: a
*finite* family of affine charts `Spf R{1/r x}` of `Spf R`, each landing in one member of the
original cover of `X`. -/
theorem exists_finite_basicOpen_refinement {ι : Type*}
    (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X)
    (U : ι → Opens X.toTopCat) (hU : ⨆ i, U i = ⊤) :
    ∃ (r : FormalSpectrum I → R) (idx : FormalSpectrum I → ι)
      (s : Finset (FormalSpectrum I)),
      (⨆ x ∈ s, basicOpen I (r x)) = ⊤ ∧
        ∀ x, basicOpen I (r x) ≤ (Opens.map (commonBase I f)).obj (U (idx x)) := by
  choose r idx hmem hle using exists_basicOpen_le_map_commonBase I f U hU
  have hcov : (Set.univ : Set (FormalSpectrum I)) ⊆
      ⋃ x, (basicOpen I (r x) : Set (FormalSpectrum I)) :=
    fun x _ => Set.mem_iUnion.mpr ⟨x, hmem x⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x => (basicOpen I (r x) : Set (FormalSpectrum I)))
    (fun x => (basicOpen I (r x)).isOpen) hcov
  refine ⟨r, idx, s, ?_, hle⟩
  rw [eq_top_iff]
  rintro x -
  obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  exact Opens.mem_iSup.mpr ⟨y, Opens.mem_iSup.mpr ⟨hy, hxy⟩⟩

section Witness

/-! ### A concrete witness

Two degeneracies to rule out, and — as in `ThickeningCoverPullback.lean` — only one of them can be.

`[IsAdicRing I]` holds at `I = ⊥`, where the tower is constant; the shared `2`-adic witness
rules that out, by `FormalSpectrum.twoAdicIdeal_ne_bot` (`FormalSchemes/TwoAdicWitness.lean`). And
the hypothesis `⨆ i, U i = ⊤` is satisfied by the one-member family `U = ⊤`, which would make the
statements say nothing about covers; the witness below therefore uses a genuine two-piece cover of
the target, `Spec ℤ = D(2) ∪ D(3)`, with neither member equal to `⊤`.

**What cannot be done at the witness used here.** `FormalSpectrum I` is *defined* as
`PrimeSpectrum (R ⧸ I)`, and `ℤ^ ⧸ 2ℤ^ = 𝔽₂`, so `|Spf ℤ^|` is a **one-point space**: the
refinement it produces is a single basic open equal to `⊤`, whatever cover of the target it starts
from. That is a fact about the `2`-adic witness below, not about the theorems, which quantify over
all `X` and all covers. It is proved as `FormalSpectrum.twoAdic_exists_eq_top` in
`FormalSchemes/TwoAdicDegeneracy.lean`, and applied to this file's conclusion in
`FormalSchemes/ThickeningNonDegenerateWitness.lean`.

A genuinely multi-piece refinement needs an adic ring whose `R ⧸ I` has **more than one prime
ideal** — equivalently, whose `Spec` is not a point. (Not "whose `R ⧸ I` is non-local": a DVR is
local and has two primes, so locality is the wrong criterion.) Such a ring is now on the tree:
`FormalSchemes/FormalLineWitness.lean` completes `ℤ[X]` at **`(X)`**, i.e. `ℤ⟦X⟧`, whose residue
ring is `ℤ`, and provides `homeoSpecInt`, `twoChart`, `iSup_twoChart`, `twoChart_ne_top` and
`nontrivial_formalSpectrum`. Note which ideal: `(X)`, not `(2)` — the `(2)` route would give
residue ring `𝔽₂[X]`, but it needs `Prime (2 : ℤ)`, which is not in this project's Mathlib import
closure. Re-running the witness below at `ℤ⟦X⟧`, where the refinement really is multi-piece, is
issue 1038; it is a statement change and needs a new import, so it is not done here.

The cover below mirrors the private witness of `ThickeningCoverPullback.lean`. It is duplicated
rather than shared because that one is `private`; if a third module needs `Spec ℤ = D(2) ∪ D(3)` it
should be lifted into a witness module of its own, the way `TwoAdicWitness.lean` was. -/

attribute [local instance] isAdicRing_twoAdicIdeal

/-- The witness target, `Spec ℤ` as a locally ringed space. -/
private abbrev specZ : LocallyRingedSpace.{0} := Spec.locallyRingedSpaceObj (CommRingCat.of ℤ)

/-- The family of structure maps `Spec (ℤ^ ⧸ (2ℤ^)ⁿ⁺¹) ⟶ Spec ℤ`. -/
private def familyZ : ∀ n : ℕ, Spec.locallyRingedSpaceObj
    (CommRingCat.of (AdicCompletion (Ideal.span {(2 : ℤ)}) ℤ ⧸ twoAdicIdeal ^ (n + 1))) ⟶ specZ :=
  fun n => Spec.locallyRingedSpaceMap (CommRingCat.ofHom
    (Int.castRingHom (AdicCompletion (Ideal.span {(2 : ℤ)}) ℤ ⧸ twoAdicIdeal ^ (n + 1))))

/-- The two-piece cover of `Spec ℤ` by `D(2)` and `D(3)`. -/
private def coverZ : Bool → Opens specZ.toTopCat
  | false => PrimeSpectrum.basicOpen (2 : ℤ)
  | true => PrimeSpectrum.basicOpen (3 : ℤ)

/-- `D(2)` and `D(3)` cover `Spec ℤ`, because `3 - 2 = 1`. -/
private theorem iSup_coverZ : ⨆ i, coverZ i = ⊤ := by
  have h : (⨆ i : Bool, PrimeSpectrum.basicOpen (if i then (3 : ℤ) else 2)) = ⊤ := by
    rw [PrimeSpectrum.iSup_basicOpen_eq_top_iff, Ideal.eq_top_iff_one,
      show (1 : ℤ) = 3 - 2 by norm_num]
    exact sub_mem (Ideal.subset_span ⟨true, rfl⟩) (Ideal.subset_span ⟨false, rfl⟩)
  refine Eq.trans ?_ h
  congr 1
  funext i
  cases i <;> rfl

/-- Neither member of the cover is the whole space, so it really is a two-piece cover: were
`D(m) = ⊤`, the singleton-family form of `iSup_basicOpen_eq_top_iff` would make `m` generate the
unit ideal of `ℤ`. -/
private theorem basicOpen_ne_top (m : ℤ) (hm : ¬ IsUnit m) :
    PrimeSpectrum.basicOpen m ≠ ⊤ := by
  intro h
  have hsup : (⨆ _ : Unit, PrimeSpectrum.basicOpen m) = ⊤ := by rw [iSup_const]; exact h
  have hspan : Ideal.span (Set.range fun _ : Unit => m) = ⊤ :=
    PrimeSpectrum.iSup_basicOpen_eq_top_iff.mp hsup
  have h1 : (1 : ℤ) ∈ Ideal.span (Set.range fun _ : Unit => m) := hspan ▸ Submodule.mem_top
  rw [Set.range_const, Ideal.mem_span_singleton] at h1
  exact hm (isUnit_of_dvd_one h1)

private theorem coverZ_false_ne_top : coverZ false ≠ ⊤ :=
  basicOpen_ne_top 2 (by decide)

private theorem coverZ_true_ne_top : coverZ true ≠ ⊤ :=
  basicOpen_ne_top 3 (by decide)

/-- **The refinement exists at a genuinely adic ring, over a genuinely two-piece cover.** -/
example : ∃ (r : FormalSpectrum twoAdicIdeal → AdicCompletion (Ideal.span {(2 : ℤ)}) ℤ)
    (idx : FormalSpectrum twoAdicIdeal → Bool),
    (⨆ x, basicOpen twoAdicIdeal (r x)) = ⊤ ∧
      ∀ x, basicOpen twoAdicIdeal (r x) ≤
        (Opens.map (commonBase twoAdicIdeal familyZ)).obj (coverZ (idx x)) :=
  exists_basicOpen_refinement twoAdicIdeal familyZ coverZ iSup_coverZ

/-- **And it can be taken finite.** -/
example : ∃ (r : FormalSpectrum twoAdicIdeal → AdicCompletion (Ideal.span {(2 : ℤ)}) ℤ)
    (idx : FormalSpectrum twoAdicIdeal → Bool) (s : Finset (FormalSpectrum twoAdicIdeal)),
    (⨆ x ∈ s, basicOpen twoAdicIdeal (r x)) = ⊤ ∧
      ∀ x, basicOpen twoAdicIdeal (r x) ≤
        (Opens.map (commonBase twoAdicIdeal familyZ)).obj (coverZ (idx x)) :=
  exists_finite_basicOpen_refinement twoAdicIdeal familyZ coverZ iSup_coverZ

end Witness

end FormalSpectrum
