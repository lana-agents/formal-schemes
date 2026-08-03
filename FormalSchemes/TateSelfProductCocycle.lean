import FormalSchemes.TateSelfProductDSigma
import FormalSchemes.TateSelfProductGlueDatum

set_option linter.style.header false
-- The completed-tensor interchange charts range over nested localization/completion towers of the
-- completed tensor product, which are slow for the elaborator and the kernel; raise the budgets
-- (matching `TateSelfProductDSigma.lean`).
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The four-chart Tate self-product `GlueData'` cocycle

Fix an adic base `(R, I)` with `q ∈ I` finitely generated, `A = annulusAlgebra R I q`, and
`C = A ⊗̂_R A`. This file closes issue 237 brick (c3): the `cocycle` field of the eventual
`GlueData'` on `J = Bool × Bool` for the Tate self-fibre-product,

`t' i j k ≫ t' j k i ≫ t' k i j = 𝟙`,

for every pairwise-distinct triple `i j k : Bool × Bool`, matching Mathlib's `GlueData'.cocycle`.

## The route

The lift-built transition-of-transitions `tateSelfProductGlueT'` cannot telescope its cocycle
through the lift/mono API alone (`t i j ≫ f j i ≠ f i j`: the underlying transitions genuinely
permute summands). Instead we pass through the closed-form summand permutation established in
`TateSelfProductDSigma`:

* conjugating `t'` by the uniform both-overlap isos `tateSelfProductBothChartIso` gives the
  self-map `tateSelfProductD`, and the three isos of a cyclic triple telescope, so the cocycle
  `t'-triple = 𝟙` is equivalent to `D i j k ≫ D j k i ≫ D k i j = 𝟙` on the both-overlap object;
* `tateSelfProductD_eq_sigma` rewrites each `D` to the explicit summand permutation
  `tateSelfProductSigma`, and the `D`-triple identity becomes the `σ`-triple identity
  `(σ i j k).hom ≫ (σ j k i).hom ≫ (σ k i j).hom = 𝟙`.

The `σ`-triple identity is proved *uniformly* (no `Bool × Bool` case split) by the naturality square
`tateSelfProductSigma_hom_comp_bothChart`: each `σ` moves the both-overlap chart to
`bothFactorOverlapChart ≫ mapSpf (combo)`, where `combo` is the coordinate-wise choice of the
identity or the coordinate swap `annulusFlip`. Since `bothFactorOverlapChart` is a monomorphism, the
`σ`-triple identity reduces to `mapSpf(combo i j) ≫ mapSpf(combo j k) ≫ mapSpf(combo k i) = 𝟙`,
which holds because on each tensor factor the three swap choices compose to the identity: the number
of `annulusFlip`s around the cycle is even (`swapFactor'_triple`), and `annulusFlip` is an
involution (`flip_comp_flip`).

## Main results

* `AlgebraicGeometry.tateSelfProductSigma_triple`: the `σ`-triple identity.
* `AlgebraicGeometry.tateSelfProductGlueCocycle`: the four-chart Tate self-product cocycle.

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

/-! ### The `mapSpf` coordinate-swap combination and its cyclic-triple identity -/

/-- The per-tensor-factor coordinate map dispatched by a pair of `Bool` coordinates: the identity
when the two coordinates agree and the coordinate swap `annulusFlip` when they differ. A public copy
of the (private) combination used by `tateSelfProductSigma_hom_comp_bothChart`; the two are
definitionally equal, so `swapFactor'` closes the coordinate-composite side conditions there. -/
abbrev swapFactor' (hI : I.FG) (b c : Bool) :
    annulusAlgebra R I q →ₐ[R] annulusAlgebra R I q :=
  if b = c then AlgHom.id R (annulusAlgebra R I q) else (annulusFlip R I q hI).toAlgHom

/-- **`annulusFlip` is an involution (algebra-hom form).** The coordinate swap composed with itself
is the identity, from `annulusFlipHom_annulusFlipHom`. -/
theorem flip_comp_flip (hI : I.FG) :
    (annulusFlip R I q hI).toAlgHom.comp (annulusFlip R I q hI).toAlgHom =
      AlgHom.id R (annulusAlgebra R I q) := by
  have h : (annulusFlip R I q hI).toAlgHom = annulusFlipHom R I q hI := rfl
  rw [h, annulusFlipHom_annulusFlipHom]

/-- **The cyclic-triple identity of the swap combination.** For any three `Bool` coordinates
`a b c`, composing the three swap choices around the cycle `a → b → c → a` is the identity: the
number of `annulusFlip`s is even, and `annulusFlip` is an involution. -/
theorem swapFactor'_triple (hI : I.FG) (a b c : Bool) :
    (swapFactor' R I q hI a b).comp
        ((swapFactor' R I q hI b c).comp (swapFactor' R I q hI c a)) =
      AlgHom.id R (annulusAlgebra R I q) := by
  cases a <;> cases b <;> cases c <;>
    simp [swapFactor', AlgHom.id_comp, AlgHom.comp_id, flip_comp_flip R I q hI]

/-- **Three `mapSpf`s compose to the identity** when their factorwise composites are the identity.
Direct from geometric functoriality `mapSpf_comp`/`mapSpf_id`. -/
theorem mapSpf_triple_eq_id (hI : I.FG)
    (f1 f2 f3 g1 g2 g3 : annulusAlgebra R I q →ₐ[R] annulusAlgebra R I q)
    (hf : f1.comp (f2.comp f3) = AlgHom.id R _) (hg : g1.comp (g2.comp g3) = AlgHom.id R _) :
    haveI := isAdicRing R I (annulusAlgebra R I q) (annulusAlgebra R I q) hI
    mapSpf hI f1 g1 ≫ mapSpf hI f2 g2 ≫ mapSpf hI f3 g3 = 𝟙 _ := by
  haveI := isAdicRing R I (annulusAlgebra R I q) (annulusAlgebra R I q) hI
  rw [← mapSpf_comp hI f3 g3 f2 g2, ← mapSpf_comp hI (f2.comp f3) (g2.comp g3) f1 g1, hf, hg,
    mapSpf_id]

/-! ### The `σ`-triple identity -/

/-- **The `σ`-triple identity.** For every pairwise-distinct triple `i j k : Bool × Bool` the three
summand permutations of the cyclic triple compose to the identity of the both-overlap object. Proved
uniformly by pushing the both-overlap chart through the three naturality squares
(`tateSelfProductSigma_hom_comp_bothChart`) and collapsing the resulting `mapSpf` triple to the
identity (`mapSpf_triple_eq_id` fed by `swapFactor'_triple`), using that `bothFactorOverlapChart` is
a monomorphism. -/
theorem tateSelfProductSigma_triple (hq : q ∈ I) (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (tateSelfProductSigma R I q hI i j k hij hik hjk).hom ≫
        (tateSelfProductSigma R I q hI j k i hjk hij.symm hik.symm).hom ≫
          (tateSelfProductSigma R I q hI k i j hik.symm hjk.symm hij).hom =
      𝟙 _ := by
  haveI := isOpenImmersion_bothFactorOverlapChart R I q hq hI
  rw [← cancel_mono (bothFactorOverlapChart R I q hI), Category.id_comp]
  slice_lhs 3 4 =>
    rw [tateSelfProductSigma_hom_comp_bothChart R I q hI k i j hik.symm hjk.symm hij]
  slice_lhs 2 3 =>
    rw [tateSelfProductSigma_hom_comp_bothChart R I q hI j k i hjk hij.symm hik.symm]
  slice_lhs 1 2 =>
    rw [tateSelfProductSigma_hom_comp_bothChart R I q hI i j k hij hik hjk]
  rw [Category.assoc, Category.assoc,
    mapSpf_triple_eq_id R I q hI _ _ _ _ _ _
      (swapFactor'_triple R I q hI i.1 j.1 k.1) (swapFactor'_triple R I q hI i.2 j.2 k.2),
    Category.comp_id]

/-! ### The cocycle -/

/-- **The four-chart Tate self-product `GlueData'` cocycle.** For every pairwise-distinct triple
`i j k : Bool × Bool` the three transitions-of-transitions of the cyclic triple compose to the
identity, matching the `GlueData'.cocycle` field. Obtained by conjugating to the both-overlap
object: the cyclic both-overlap isos telescope, `tateSelfProductD_eq_sigma` identifies each
conjugated factor with a summand permutation, and `tateSelfProductSigma_triple` closes the
`σ`-triple. This is the input brick (c4)/issue 303 consumes to assemble
`tateSelfProductGlueData'`. -/
theorem tateSelfProductGlueCocycle (hq : q ∈ I) (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i j hij)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i k hik)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI j k hjk)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI j i hij.symm)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI k i hik.symm)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI k j hjk.symm)] :
    tateSelfProductGlueT' R I q hI i j k hij hik hjk ≫
        tateSelfProductGlueT' R I q hI j k i hjk hij.symm hik.symm ≫
          tateSelfProductGlueT' R I q hI k i j hik.symm hjk.symm hij =
      𝟙 _ := by
  haveI := isOpenImmersion_bothFactorOverlapChart R I q hq hI
  have hσ := tateSelfProductSigma_triple R I q hq hI i j k hij hik hjk
  rw [← tateSelfProductD_eq_sigma R I q hq hI i j k hij hik hjk,
    ← tateSelfProductD_eq_sigma R I q hq hI j k i hjk hij.symm hik.symm,
    ← tateSelfProductD_eq_sigma R I q hq hI k i j hik.symm hjk.symm hij,
    tateSelfProductD, tateSelfProductD, tateSelfProductD] at hσ
  simp only [Category.assoc, Iso.inv_hom_id_assoc] at hσ
  rw [Iso.hom_comp_eq_id] at hσ
  rw [← cancel_mono (tateSelfProductBothChartIso R I q hI i j k hij hik hjk).inv,
    Category.id_comp, Category.assoc, Category.assoc]
  exact hσ

end AlgebraicGeometry

end
