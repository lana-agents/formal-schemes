import FormalSchemes.ThickeningCommonBase

set_option linter.style.header false

/-!
# Pulling an open cover of `X` back to `|Spf R|` (EGA I, 10.6.10)

`FormalSchemes/ThickeningCommonBase.lean` shows that a compatible family of morphisms out of the
infinitesimal thickenings, `f n : Spec (R ⧸ I ^ (n + 1)) ⟶ X`, has a single underlying map
`commonBase I f : |Spf R| ⟶ |X|`, for an **arbitrary** locally ringed space `X`. This file takes
the next topological step: an open cover of `X` pulls back along that map to an open cover of
`|Spf R|`, and the pulled-back opens are computed by *every* level of the tower, not just the one
`commonBase` was defined at.

That is the chart decomposition the eventual construction of a morphism `Spf R ⟶ X` from a
compatible family will induct over: cover `X` by affines, pull the cover back to `|Spf R|`, run the
affine case (`FormalSchemes/IndScheme.lean` and its successors) on each piece, glue. Only the first
two steps are topology; everything after them is the sheaf-theoretic half and is not here.

## The two statements

`map_commonBase_obj_eq` is the one with content. It says the open of `|Spf R|` lying over
`U : Opens X` is the level-`n` preimage `(f n)⁻¹ U` transported along `thickeningTopIso I n`, **for
every `n` simultaneously**. Without it an induction over a cover would have to carry a level index
and then prove the choice did not matter.

`iSup_map_commonBase_obj_eq_top` is the cover statement itself, and it deliberately takes **no**
compatibility hypothesis: `commonBase` is defined from the level-`0` member alone, so pulling a
cover back needs nothing about the tower. Do not add `hf` to it for symmetry.

## Non-vacuity, and one thing that is genuinely impossible here

Both results are equations, so the risk is not that they are unprovable but that they are only ever
instantiated trivially. Two separate degeneracies to rule out, and only one of them can be:

* `[IsAdicRing I]` holds at `I = ⊥`, where the tower is constant. The shared `2`-adic witness
  rules that out, by `FormalSpectrum.twoAdicIdeal_ne_bot` (`FormalSchemes/TwoAdicWitness.lean`),
  and the `example` below instantiates `map_commonBase_obj_eq` at a **nonzero** level, where its
  two sides are not syntactically equal.
* A "cover" with a single member `U = ⊤` satisfies `iSup_map_commonBase_obj_eq_top` trivially. The
  witness here is therefore a genuine two-piece cover of the target: `Spec ℤ = D(2) ∪ D(3)`, with
  `D(2) ≠ ⊤` and `D(3) ≠ ⊤` both proved.

**What cannot be done, and is not a gap in the file:** the *pulled-back* cover of `|Spf ℤ^|`
degenerates no matter which cover of the target is chosen, because `|Spf R| ≅ |Spec (R ⧸ I)|` and
`ℤ^ ⧸ 2ℤ^ = 𝔽₂` — the source is a one-point space, so every open cover of it has a member equal to
`⊤`. That is a fact about the witness, not about the theorem; the theorem quantifies over all `X`
and all covers, and the non-degeneracy that is available is on the hypothesis side, which is what is
exhibited. The degeneracy is proved as `FormalSpectrum.twoAdic_exists_eq_top` in
`FormalSchemes/TwoAdicDegeneracy.lean`, and this file's `iSup_map_commonBase_obj_eq_top` is
instantiated at the `2`-adic witness against it in
`FormalSchemes/ThickeningNonDegenerateWitness.lean`.

A witness with a genuinely multi-piece pulled-back cover needs an adic ring whose `R ⧸ I` has
**more than one prime ideal** — equivalently, whose `Spec` is not a point. (Not "whose `R ⧸ I` is
non-local": a DVR is local and has two primes, so locality is the wrong criterion.)
`FormalSchemes/FormalLineWitness.lean` supplies such a ring: `ℤ[X]` completed at `(X)`, i.e.
`ℤ⟦X⟧`, whose residue ring is `ℤ`, with `FormalSpectrum.homeoSpecInt : FormalSpectrum
formalLineIdeal ≃ₜ PrimeSpectrum ℤ` and an explicit two-piece cover (`FormalSpectrum.twoChart`,
`iSup_twoChart`, `twoChart_ne_top`). Re-running the witness below at that ring — where the
*pulled-back* cover really is two-piece — is issue 1038; it is a statement change and needs a new
import, so it is not done here.

## Main results

* `FormalSpectrum.map_commonBase_obj_eq`: the pullback of `U : Opens X` is the level-`n` preimage,
  transported, for every `n`.
* `FormalSpectrum.mem_map_commonBase_obj_iff`: its pointwise form.
* `FormalSpectrum.iSup_map_commonBase_obj_eq_top`: an open cover of `X` pulls back to an open cover
  of `|Spf R|`.

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
/-- **The open of `|Spf R|` lying over `U` is computed by any level of the tower**: it is the
preimage of `U` under the `n`-th member of the family, transported along the identification
`thickeningTopIso I n` of `|Spf R|` with the `n`-th thickening's space.

This is what makes a chart decomposition of `|Spf R|` level-independent, and it is immediate from
`commonBase_eq` — the map itself does not depend on `n`, so neither does anything computed from
it. -/
theorem map_commonBase_obj_eq
    (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X)
    (hf : ∀ n : ℕ, Spec.locallyRingedSpaceMap (stepRingHom I n) ≫ f (n + 1) = f n)
    (n : ℕ) (U : Opens X.toTopCat) :
    (Opens.map (commonBase I f)).obj U =
      (Opens.map (thickeningTopIso I n).hom).obj ((Opens.map (f n).base).obj U) := by
  rw [commonBase_eq I f hf n]
  rfl

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The pointwise form of `map_commonBase_obj_eq`: a point of `|Spf R|` lies over `U` exactly when
its image in the `n`-th thickening is carried into `U` by `f n`, for any `n`. -/
theorem mem_map_commonBase_obj_iff
    (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X)
    (hf : ∀ n : ℕ, Spec.locallyRingedSpaceMap (stepRingHom I n) ≫ f (n + 1) = f n)
    (n : ℕ) (U : Opens X.toTopCat) (x : FormalSpectrum I) :
    x ∈ (Opens.map (commonBase I f)).obj U ↔ (f n).base ((thickeningTopIso I n).hom x) ∈ U := by
  rw [commonBase_eq I f hf n]
  exact Iff.rfl

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **An open cover of `X` pulls back to an open cover of `|Spf R|`.** No compatibility hypothesis
is needed: `commonBase` is read off from the level-`0` member of the family alone.

Note that `Opens.map_iSup` is stated with a `Function.comp` on the right, so `rw [← Opens.map_iSup]`
will not match a goal spelled `⨆ i, (Opens.map _).obj (U i)`. Stating the equation as a `have` in
the goal's own spelling lets unification handle the composition. -/
theorem iSup_map_commonBase_obj_eq_top {ι : Type*}
    (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶ X)
    (U : ι → Opens X.toTopCat) (hU : ⨆ i, U i = ⊤) :
    ⨆ i, (Opens.map (commonBase I f)).obj (U i) = ⊤ := by
  have h : (Opens.map (commonBase I f)).obj (⨆ i, U i) =
      ⨆ i, (Opens.map (commonBase I f)).obj (U i) := Opens.map_iSup _ _
  rw [← h, hU]
  rfl

section Witness

/-! ### A concrete witness

`Spec ℤ` covered by `D(2)` and `D(3)`, with the `2`-adic integers as the adic ring. The cover is
genuinely two-piece — neither member is `⊤` — which is what stops
`iSup_map_commonBase_obj_eq_top` from being read as a statement about `⊤` alone. See the module
docstring for why the *pulled-back* cover necessarily degenerates at this witness. -/

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

/-- **Neither member of the cover is the whole space**, so it really is a two-piece cover: were
`D(f) = ⊤`, the singleton family form of `iSup_basicOpen_eq_top_iff` would make `f` generate the
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

/-- **The cover pulls back**, at a genuinely two-piece cover of a non-trivial target. -/
example : ⨆ i, (Opens.map (commonBase twoAdicIdeal familyZ)).obj (coverZ i) = ⊤ :=
  iSup_map_commonBase_obj_eq_top twoAdicIdeal familyZ coverZ iSup_coverZ

/-- **The level-independence is exercised away from level `0`**, where the two sides of
`map_commonBase_obj_eq` are not syntactically equal. The family used is the tautological one, whose
compatibility is `thickeningMap_comp`. -/
example (U : Opens (TopCat.of (FormalSpectrum twoAdicIdeal))) :
    (Opens.map (commonBase twoAdicIdeal (thickeningMap twoAdicIdeal))).obj U =
      (Opens.map (thickeningTopIso twoAdicIdeal 3).hom).obj
        ((Opens.map (thickeningMap twoAdicIdeal 3).base).obj U) :=
  map_commonBase_obj_eq twoAdicIdeal (thickeningMap twoAdicIdeal)
    (thickeningMap_comp twoAdicIdeal) 3 U

end Witness

end FormalSpectrum
