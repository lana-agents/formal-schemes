import FormalSchemes.TateShift

set_option linter.style.header false

/-!
# The `q^ℤ`-action on the formal Tate chain

Fix an adic base `(R, I)` with `I` finitely generated and Noetherian `R`, and a topologically
nilpotent Tate parameter `q ∈ I`. The formal Tate chain `T = tateChain R I q hq hI`
(`FormalSchemes.TateChainGlue`) carries the `+1`-index shift automorphism `tateShiftIso : T ≅ T`
(`FormalSchemes.TateShift`), the formal model of multiplication by the Tate parameter `q`.

This file upgrades that single automorphism to the full **`q^ℤ`-action**: the group homomorphism
`ℤ → Aut T`, `n ↦ σ^n`, and records the **proper discontinuity** of the action — for `|k| ≥ 2` the
patch `U_n` and its translate `σ^k(U_n) = U_{n+k}` have empty overlap in the glue datum, so only
consecutive patches meet. This is the separation datum that the quotient construction `T/q^ℤ`
(issue 69, the Tate elliptic curve formal model) consumes.

## What this file provides

* `tateShiftGenFun`: the `+m` index map `⟨n⟩ ↦ ⟨n + m⟩` on `ULift ℤ`, with `_zero` / `_add`
  compatibilities.
* `tateShiftGen m`: the `+m`-shift self-map `T ⟶ T`, generalising `tateShift` (`m = 1`), assembled
  from the shifted inclusions via `glueMorphisms` and the generic overlap cruxes
  `tateShift_overlap_{forward,backward}_gen`.
* `ι_tateShiftGen`, `tateShiftGen_zero`, `tateShiftGen_add`: the defining `ι`-restriction identity
  and the monoid laws `σ^0 = 𝟙`, `σ^m ≫ σ^n = σ^(m+n)`.
* `tateShiftGenIso m`: the `+m` shift packaged as an automorphism `T ≅ T` (inverse `σ^(-m)`).
* `tateShiftAut`: the group homomorphism `Multiplicative ℤ →* Aut T` — the `q^ℤ`-action.
* `tateChain_translate_overlap_isEmpty`: **proper discontinuity** — for a translation index
  `k ∉ {−1, 0, 1}` the overlap `V (i, σ^k i)` of the patch `U i` with its translate `U (i+k)` is
  empty (`IsEmpty`), so only consecutive patches meet.

## Remaining follow-up

Freeness of the action (`tateShiftAut` injective, equivalently `σ^m = 𝟙 ⟹ m = 0`) is not yet
proved: it needs the two ingredients (i) a *converse* of `LocallyRingedSpace.isEmpty_of_commSq` —
that the empty overlap `V (i, σ^k i)` (via `LocallyRingedSpace.GlueData.vPullbackConeIsLimit`,
which exhibits `V` as the pullback of `ι i`, `ι (σ^k i)`) forces the underlying-space ranges of the
two `ι`'s to be **disjoint** — and (ii) nonemptiness of a patch `Spf A` (`Nontrivial (A ⧸ I·A)`,
i.e. `I ≠ ⊤`). Given both, `σ^m = 𝟙` would give `ι (σ^{2m} i) = ι i` with disjoint nonempty ranges
for `m ≠ 0`, a contradiction. This is left for a follow-up (issue 135), together with the
range-disjointness restatement of proper discontinuity that the same converse yields.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-! ### The `+m` index shift on `ULift ℤ` -/

/-- The `+m` shift of the index type `ULift ℤ`, sending patch `U_n` to patch `U_{n+m}`. For `m = 1`
this is `tateShiftFun`. -/
def tateShiftGenFun (m : ℤ) (i : ULift.{u} ℤ) : ULift.{u} ℤ := ⟨i.down + m⟩

@[simp] theorem tateShiftGenFun_down (m : ℤ) (i : ULift.{u} ℤ) :
    (tateShiftGenFun m i).down = i.down + m := rfl

@[simp] theorem tateShiftGenFun_zero (i : ULift.{u} ℤ) : tateShiftGenFun (0 : ℤ) i = i := by
  apply ULift.down_injective; simp [tateShiftGenFun]

/-- Iterating the `+m` then `+n` shift is the `+(m+n)` shift. -/
theorem tateShiftGenFun_add (m n : ℤ) (i : ULift.{u} ℤ) :
    tateShiftGenFun n (tateShiftGenFun m i) = tateShiftGenFun (m + n) i := by
  apply ULift.down_injective; simp [tateShiftGenFun]; ring

/-! ### The `+m` shift self-map of `T` -/

variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R]

/-- **The `+m`-shift self-map of the formal Tate chain** `T ⟶ T`, assembled from the shifted
inclusions `ι (tateShiftGenFun m ·)` via `glueMorphisms`. Generalises `tateShift` (the case
`m = 1`). The compatibility obligation is discharged by the generic overlap cruxes for the
difference-preserving reindexing `tateShiftGenFun m`. -/
def tateShiftGen (hq : q ∈ I) (hI : I.FG) (m : ℤ) :
    (tateChain R I q hq hI).toLocallyRingedSpace ⟶ (tateChain R I q hq hI).toLocallyRingedSpace :=
  (tateChainFormalGlueData R I q hq hI).glueMorphisms
    (fun i => (tateChainFormalGlueData R I q hq hI).ι (tateShiftGenFun m i))
    (tateChain_glueMorphisms_compat R I q hq hI _
      (fun _ _ h => tateShift_overlap_forward_gen R I q hq hI (tateShiftGenFun m) (by
        simp only [tateShiftGenFun_down]; omega))
      (fun _ _ h => tateShift_overlap_backward_gen R I q hq hI (tateShiftGenFun m) (by
        simp only [tateShiftGenFun_down]; omega)))

/-- The `+m`-shift restricts along `ι i` to `ι (tateShiftGenFun m i)`. -/
@[reassoc (attr := simp)]
theorem ι_tateShiftGen (hq : q ∈ I) (hI : I.FG) (m : ℤ) (i : ULift.{u} ℤ) :
    (tateChainFormalGlueData R I q hq hI).ι i ≫ tateShiftGen R I q hq hI m =
      (tateChainFormalGlueData R I q hq hI).ι (tateShiftGenFun m i) := by
  rw [tateShiftGen, FormalScheme.GlueData.ι_glueMorphisms]

/-- `σ^0 = 𝟙`: the `+0` shift is the identity. -/
theorem tateShiftGen_zero (hq : q ∈ I) (hI : I.FG) :
    tateShiftGen R I q hq hI 0 = 𝟙 _ := by
  apply (tateChainFormalGlueData R I q hq hI).hom_ext
  intro i
  erw [ι_tateShiftGen, tateShiftGenFun_zero, Category.comp_id]

/-- `σ^m ≫ σ^n = σ^(m+n)`: composing the `+m` and `+n` shifts gives the `+(m+n)` shift. -/
theorem tateShiftGen_add (hq : q ∈ I) (hI : I.FG) (m n : ℤ) :
    tateShiftGen R I q hq hI m ≫ tateShiftGen R I q hq hI n = tateShiftGen R I q hq hI (m + n) := by
  apply (tateChainFormalGlueData R I q hq hI).hom_ext
  intro i
  erw [ι_tateShiftGen_assoc, ι_tateShiftGen, ι_tateShiftGen, tateShiftGenFun_add]

/-! ### The shift as an automorphism, and the group homomorphism -/

/-- **The `+m`-shift automorphism of the formal Tate chain** `T ≅ T`, with inverse the `−m` shift.
The triangle identities are the monoid laws `tateShiftGen_add` / `tateShiftGen_zero`. -/
def tateShiftGenIso (hq : q ∈ I) (hI : I.FG) (m : ℤ) :
    (tateChain R I q hq hI).toLocallyRingedSpace ≅
      (tateChain R I q hq hI).toLocallyRingedSpace where
  hom := tateShiftGen R I q hq hI m
  inv := tateShiftGen R I q hq hI (-m)
  hom_inv_id := by rw [tateShiftGen_add, add_neg_cancel, tateShiftGen_zero]
  inv_hom_id := by rw [tateShiftGen_add, neg_add_cancel, tateShiftGen_zero]

@[simp] theorem tateShiftGenIso_hom (hq : q ∈ I) (hI : I.FG) (m : ℤ) :
    (tateShiftGenIso R I q hq hI m).hom = tateShiftGen R I q hq hI m := rfl

/-- **The `q^ℤ`-action on the formal Tate chain**: the group homomorphism `ℤ → Aut T`,
`n ↦ σ^n` (`Multiplicative ℤ →* Aut T`), sending the generator to the `+1`-shift `tateShiftIso`.
The proper discontinuity of the action (non-adjacent patches do not overlap) is recorded in
`tateChain_translate_overlap_isEmpty`. -/
def tateShiftAut (hq : q ∈ I) (hI : I.FG) :
    Multiplicative ℤ →* Aut (tateChain R I q hq hI).toLocallyRingedSpace where
  toFun m := tateShiftGenIso R I q hq hI (Multiplicative.toAdd m)
  map_one' := by
    apply Iso.ext
    simp only [tateShiftGenIso_hom]
    exact tateShiftGen_zero R I q hq hI
  map_mul' x y := by
    apply Iso.ext
    change tateShiftGen R I q hq hI (Multiplicative.toAdd x + Multiplicative.toAdd y) =
      tateShiftGen R I q hq hI (Multiplicative.toAdd y) ≫
        tateShiftGen R I q hq hI (Multiplicative.toAdd x)
    rw [tateShiftGen_add, add_comm]

/-! ### Proper discontinuity: non-adjacent patches do not overlap -/

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Proper discontinuity of the `q^ℤ`-action.** For a translation index `k ∉ {−1, 0, 1}`
(equivalently `|k| ≥ 2`) the overlap `V (i, σ^k i)` of the patch `U i` with its translate
`U (i+k) = σ^k(U i)` in the Tate-chain glue datum is empty: only consecutive patches meet. This is
exactly the separation/disjointness datum the quotient construction `T/q^ℤ` (issue 69, the Tate
elliptic curve formal model) consumes — the quotient map is then a local isomorphism. -/
theorem tateChain_translate_overlap_isEmpty (hq : q ∈ I) (hI : I.FG) (k : ℤ)
    (hk0 : k ≠ 0) (hk1 : k ≠ 1) (hk2 : k ≠ -1) (i : ULift.{u} ℤ) :
    IsEmpty ((tateChainFormalGlueData R I q hq hI).toLocallyRingedSpaceGlueData.toGlueData.V
      (i, tateShiftGenFun k i)) := by
  have hne : ¬ @Eq (ULift.{u} ℤ) i (tateShiftGenFun k i) := by
    intro h
    have : i.down = i.down + k := congrArg ULift.down h
    omega
  have h1 : (tateShiftGenFun k i).down - i.down ≠ 1 := by simp only [tateShiftGenFun_down]; omega
  have h2 : (tateShiftGenFun k i).down - i.down ≠ -1 := by simp only [tateShiftGenFun_down]; omega
  simp only [tateChainFormalGlueData, tateChainLRSGlueData, CategoryTheory.GlueData.ofGlueData',
    dif_neg hne, tateChainGlueData']
  exact (tateV_far R I q h1 h2) ▸ inferInstance

end AlgebraicGeometry
