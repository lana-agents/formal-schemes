import FormalSchemes.TateSelfProductDSigmaInvSecond

set_option linter.style.header false
set_option linter.style.setOption false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The 𝔾m-inversion self-product cocycle payload `tateSelfProductD_eq_sigma_inv`

Fix an adic base `(R, I)` with `q ∈ I` finitely generated, `A = annulusAlgebra R I q`, and
`C = A ⊗̂_R A`. Unlike the swap, the 𝔾m inversion has **no `A`-algebra automorphism** (`rlsInv` is
`R`-linear, `X ↦ X⁻¹`), so the swap route through a common endomorphism `mapSpf hI (A-endo)
(A-endo)` of `Spf(A ⊗̂ A)` does not exist. The summand permutation is instead compared with
`tateSelfProductDInv` one *shape* at a time — first-factor, second-factor, both-factor — each shape
collapsing both sides, via `mapSpf_comp` and the `interchange…_eq_mapSpf` family, to `mapSpf hI u v`
for the same `annulusFibreChartTransitionInvAlg`-composite.

This file carries the **both-factor** shape lemma, the shape dispatch, and the headline

`tateSelfProductD_eq_sigma_inv : tateSelfProductDInv i j k = (tateSelfProductSigmaInv i j k).hom`

— the `GlueData'` cocycle payload for the corrected (separated, inversion) Tate self-fibre-product
`𝔈_q ×_{Spf R} 𝔈_q`. It imports the rest of the scaffold transitively, so importers of this module
see exactly what they saw when all six layers were one file.

**Why this is its own file.** Layers 1–6 of the inversion scaffold were a single module until
they no longer fit in memory: elaborating them together peaked above 17.8 GB of resident memory and
was OOM-killed on a shared box, and even layer 6 alone still peaked at 12.3 GB. The shape lemmas are
therefore one per file. No statement is changed — the declarations below are verbatim what they
were, in the same order and namespace. The only edit is that the ones a later file consumes are no
longer `private`, since `private` does not cross a module boundary; they remain internal by
convention and nothing outside this group should use them.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* Mathlib `CategoryTheory.GlueData'` (the `t'`/`t_fac`/`cocycle` fields).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
  CompletedTensorAwayInterchange CompletedTensorProduct
  AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- **Both shape (inversion).** When `i` and `j` differ in both coordinates the prefix `p` is forced
to be the identity (it factors through the mono `bothFactorOverlapChart`), and both the transition
and the permutation are `tateSelfProductBothTransitionInv`. -/
private theorem bothShapeDInv (hq : q ∈ I) (hI : I.FG)
    (p : ((dXX R I q ⨿ dXY R I q) ⨿ (dYX R I q ⨿ dYY R I q)) ⟶
        ((dXX R I q ⨿ dXY R I q) ⨿ (dYX R I q ⨿ dYY R I q)))
    (hp : p ≫ bothFactorOverlapChart R I q hI = bothFactorOverlapChart R I q hI) :
    p ≫ (tateSelfProductBothTransitionInv R I q hI).hom ≫ bothFactorOverlapChart R I q hI =
      (tateSelfProductBothTransitionInv R I q hI).hom ≫ bothFactorOverlapChart R I q hI := by
  haveI := isOpenImmersion_bothFactorOverlapChart R I q hq hI
  obtain rfl : p = 𝟙 _ := by
    rw [← cancel_mono (bothFactorOverlapChart R I q hI), Category.id_comp]; exact hp
  rw [Category.id_comp]

/-- **The shape-dispatched summand comparison.** For a prefix `p : bothOverlapObj ⟶ V i j` cut out
over the overlap chart `f i j` (`p ≫ f i j = bothChart`), the genuine transition `t_inv i j` on the
shared overlap, composed with the return chart `f j i`, agrees with the summand permutation
`σ_inv i j k` composed with the both-chart. Instance-free so the `Bool × Bool` case split reduces
the match definitions; each valid shape (first/second/both) is discharged by the corresponding shape
lemma, which is `k`-independent (the σ-permutation's `match` ignores `k`). -/
private theorem tateSelfProductDInv_dispatch (hq : q ∈ I) (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (p : ((dXX R I q ⨿ dXY R I q) ⨿ (dYX R I q ⨿ dYY R I q)) ⟶
      tateSelfProductGlueV R I q hI i j hij)
    (hp : p ≫ tateSelfProductGlueF R I q hI i j hij = bothFactorOverlapChart R I q hI) :
    p ≫ tateSelfProductGlueTInv R I q hI i j hij ≫
        tateSelfProductGlueF R I q hI j i hij.symm =
      (tateSelfProductSigmaInv R I q hI i j k hij hik hjk).hom ≫
        bothFactorOverlapChart R I q hI := by
  revert hij hik hjk p
  rcases i with ⟨_ | _, _ | _⟩ <;> rcases j with ⟨_ | _, _ | _⟩ <;>
    intro hij hik hjk p hp <;>
    first
      | exact absurd rfl hij
      | (simp only [tateSelfProductGlueTInv, tateSelfProductGlueF, tateSelfProductSigmaInv] at hp ⊢
         first
           | exact firstShapeDInv R I q hq hI p hp
           | exact secondShapeDInv R I q hq hI p hp
           | exact bothShapeDInv R I q hq hI p hp)

/-- **The 𝔾m-inversion self-product cocycle payload.** For every pairwise-distinct triple
`i j k : Bool × Bool` the conjugated self-map `tateSelfProductDInv i j k` equals the `hom` leg of
the explicit summand permutation `tateSelfProductSigmaInv i j k`. The inversion analogue of
`tateSelfProductD_eq_sigma`, proved by direct summand comparison. -/
theorem tateSelfProductD_eq_sigma_inv (hq : q ∈ I) (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i j hij)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i k hik)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI j k hjk)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI j i hij.symm)]
    [LocallyRingedSpace.IsOpenImmersion (bothFactorOverlapChart R I q hI)] :
    tateSelfProductDInv R I q hI i j k hij hik hjk =
      (tateSelfProductSigmaInv R I q hI i j k hij hik hjk).hom := by
  rw [← cancel_mono (bothFactorOverlapChart R I q hI),
    tateSelfProductDInv_comp_bothChart R I q hI i j k hij hik hjk, ← Category.assoc]
  refine tateSelfProductDInv_dispatch R I q hq hI i j k hij hik hjk
    ((tateSelfProductBothChartIso R I q hI i j k hij hik hjk).hom ≫
      pullback.fst (tateSelfProductGlueF R I q hI i j hij)
        (tateSelfProductGlueF R I q hI i k hik)) ?_
  rw [Category.assoc]
  exact tateSelfProductBothChartIso_hom_fst_comp R I q hI i j k hij hik hjk

end AlgebraicGeometry

end
