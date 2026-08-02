import FormalSchemes.TateSelfProductTPrimeSummandIdentify
import FormalSchemes.TateSelfProductSummandNaturality
import FormalSchemes.TateSelfProductSwapNaturality

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Identifying the conjugated self-map `t'` with the explicit summand permutation

Fix an adic base `(R, I)` with `q ∈ I` finitely generated, `A = annulusAlgebra R I q`, and
`C = A ⊗̂_R A`. Continuing `TateSelfProductTPrimeSummandIdentify`, this file discharges the
remaining payload of issue 237 brick (c3a): the conjugated self-map
`tateSelfProductD i j k : bothOverlapObj ⟶ bothOverlapObj` of the both-overlap object coincides,
for every pairwise-distinct triple `i j k : Bool × Bool`, with the `hom` leg of the explicit
summand permutation `tateSelfProductSigma i j k`:

`tateSelfProductD i j k = (tateSelfProductSigma i j k).hom`.

## The route

Since `bothFactorOverlapChart` is a monomorphism (each overlap chart is an open immersion when
`q ∈ I`), it suffices to compare both maps after composing with it. By
`tateSelfProductD_comp_bothChart` the left-hand side becomes `p ≫ t i j ≫ f j i`, where
`p = (tateSelfProductBothChartIso i j k).hom ≫ pullback.fst (f i j) (f i k)`.

Two *uniform* naturality squares — keyed on the same coordinate-wise combination of the coordinate
swap `annulusFlip` and the identity via `tateSelfProductSwapFactor` — do the shape bookkeeping once
and for all:

* `tateSelfProductGlueT_comp_glueF`: `t i j ≫ f j i = f i j ≫ mapSpf(combo i j)` (Family B);
* `tateSelfProductSigma_hom_comp_bothChart`:
  `σ.hom ≫ bothFactorOverlapChart = bothFactorOverlapChart ≫ mapSpf(combo i j)` (Family A, and
  Family B on the both-shape).

With these the main identification collapses without any case split: rewrite the left side by the
first square and the both-overlap iso leg law `tateSelfProductBothChartIso_hom_fst_comp`, rewrite
the right side by the second square; both sides become `bothFactorOverlapChart ≫ mapSpf(combo i j)`.

## Main results

* `AlgebraicGeometry.tateSelfProductD_eq_sigma`: the identification
  `tateSelfProductD i j k = (tateSelfProductSigma i j k).hom`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* Mathlib `CategoryTheory.GlueData'` (the `t'`/`t_fac`/`cocycle` fields).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
  CompletedTensorProduct
  AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- The per-tensor-factor coordinate map dispatched by a pair of `Bool` coordinates: the identity
when the two coordinates agree and the coordinate swap `annulusFlip` when they differ. Composing the
factorwise choices over the two coordinates of a pair `(i, j)` gives the completed-tensor
coordinate map `mapSpf hI …` that both the transition-through-chart square and the swap-involution
naturality square land in. -/
private abbrev tateSelfProductSwapFactor (hI : I.FG) (b c : Bool) :
    annulusAlgebra R I q →ₐ[R] annulusAlgebra R I q :=
  if b = c then AlgHom.id R (annulusAlgebra R I q) else (annulusFlip R I q hI).toAlgHom

/-- **The uniform transition-through-chart square (Family B).** For distinct charts `i j` the
overlap transition `t i j`, followed by the target overlap chart `f j i`, equals the source overlap
chart `f i j` followed by `mapSpf` of the coordinate-wise swap combination of `(i, j)`. Dispatched
by a single `Bool × Bool` case split onto the three Family-B naturality squares
(`TateSelfProductSummandNaturality`): first-, second- or both-factor according to which coordinates
of `(i, j)` differ. -/
theorem tateSelfProductGlueT_comp_glueF (hI : I.FG) (i j : Bool × Bool) (hij : i ≠ j) :
    tateSelfProductGlueT R I q hI i j hij ≫ tateSelfProductGlueF R I q hI j i hij.symm =
      tateSelfProductGlueF R I q hI i j hij ≫
        CompletedTensorProduct.mapSpf hI (tateSelfProductSwapFactor R I q hI i.1 j.1)
          (tateSelfProductSwapFactor R I q hI i.2 j.2) := by
  rcases i with ⟨_ | _, _ | _⟩ <;> rcases j with ⟨_ | _, _ | _⟩ <;>
    first
      | exact absurd rfl hij
      | exact tateSelfProductFirstTransition_naturality R I q hI
      | exact tateSelfProductRightTransition_naturality R I q hI
      | exact tateSelfProductBothTransition_naturality R I q hI

/-- **The uniform swap-involution naturality square (Family A).** For pairwise-distinct `i j k` the
summand permutation `σ = tateSelfProductSigma i j k`, followed by the both-factor overlap chart,
equals that chart followed by `mapSpf` of the *same* coordinate-wise swap combination of `(i, j)`
appearing in `tateSelfProductGlueT_comp_glueF`. Dispatched by a `Bool × Bool` case split onto the
two swap-naturality squares (`TateSelfProductSwapNaturality`) and — on the both-shape — the
both-factor Family-B square. -/
theorem tateSelfProductSigma_hom_comp_bothChart (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (tateSelfProductSigma R I q hI i j k hij hik hjk).hom ≫ bothFactorOverlapChart R I q hI =
      bothFactorOverlapChart R I q hI ≫
        CompletedTensorProduct.mapSpf hI (tateSelfProductSwapFactor R I q hI i.1 j.1)
          (tateSelfProductSwapFactor R I q hI i.2 j.2) := by
  rcases i with ⟨_ | _, _ | _⟩ <;> rcases j with ⟨_ | _, _ | _⟩ <;>
    first
      | exact absurd rfl hij
      | exact tateSelfProductSwapFirstTransition_naturality R I q hI
      | exact tateSelfProductSwapSecondTransition_naturality R I q hI
      | exact tateSelfProductBothTransition_naturality R I q hI

/-- **The identification of the conjugated self-map with the summand permutation.** For every
pairwise-distinct triple `i j k : Bool × Bool` the conjugated self-map `tateSelfProductD i j k` of
the both-overlap object equals the `hom` leg of the explicit summand permutation
`tateSelfProductSigma i j k`. This is the remaining payload of issue 237 brick (c3a): the
closed-form summand-permutation description of `t'` that brick (c3b) consumes to close the
`GlueData'` cocycle by `coprod.hom_ext`. -/
theorem tateSelfProductD_eq_sigma (hq : q ∈ I) (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i j hij)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i k hik)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI j k hjk)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI j i hij.symm)]
    [LocallyRingedSpace.IsOpenImmersion (bothFactorOverlapChart R I q hI)] :
    tateSelfProductD R I q hI i j k hij hik hjk =
      (tateSelfProductSigma R I q hI i j k hij hik hjk).hom := by
  have _hq := hq
  rw [← cancel_mono (bothFactorOverlapChart R I q hI),
    tateSelfProductD_comp_bothChart R I q hI i j k hij hik hjk,
    tateSelfProductGlueT_comp_glueF R I q hI i j hij,
    tateSelfProductSigma_hom_comp_bothChart R I q hI i j k hij hik hjk,
    tateSelfProductBothChartIso_hom_fst_comp_assoc R I q hI i j k hij hik hjk]

end AlgebraicGeometry

end
