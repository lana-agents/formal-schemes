import FormalSchemes.TateSelfProductTPrimeSummand
import FormalSchemes.CompletedTensorAwayInterchangeBothPullback

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# Per-summand embeddings of the both-overlap into the triple-overlap charts (Family A)

Fix an adic base `(R, I)` with `q ∈ I` finitely generated, `A = annulusAlgebra R I q`, and
`C = A ⊗̂_R A`. For pairwise-distinct charts `i j k : Bool × Bool` write
`f a b := tateSelfProductGlueF R I q hI a b` for the difference-shape-dispatched overlap chart into
`Spf C`, and `bothChart := bothFactorOverlapChart R I q hI` for the both-factor overlap chart, whose
domain is the four-fold coproduct `(dXX ⨿ dXY) ⨿ (dYX ⨿ dYY)`. The uniform both-overlap iso
`tateSelfProductBothChartIso i j k` (`TateSelfProductTPrimeSummand`) realises the both-overlap
object as `pullback (f i j) (f i k)`; composing its `hom` with `pullback.fst (f i j) (f i k)` gives
the canonical **embedding of the both-overlap into the `ij`-overlap object**

`p := (tateSelfProductBothChartIso R I q hI i j k hij hik hjk).hom ≫ pullback.fst (f i j) (f i k)`.

This file identifies the four summand restrictions `ιₛ ≫ p` (`s ∈ {xx, xy, yx, yy}`) of this
embedding, which a downstream `coprod.hom_ext` assembler (issue 335) consumes to close the
`GlueData'` cocycle.

## The route (the whole proof spine)

1. `tateSelfProductBothChartFst_comp` : `p ≫ f i j = bothChart` — a re-association of the
   already-proved leg law `tateSelfProductBothChartIso_hom_fst_comp`, uniform in the triple.
2. `f i j` is a monomorphism (an open immersion when `q ∈ I`).
3. Each summand chart `f_s = bothInterchange …` factors through exactly one leg of `f i j`'s
   `coprod.desc` by a *further-localization* `mapSpf` on the untouched tensor factor
   (`mapSpf_id_loc_comp_interchange` / `mapSpf_loc_id_comp_rightInterchange`), assembled into the
   embedding factorizations `firstFactorBothEmbedding_comp` / `secondFactorBothEmbedding_comp`:
   `embedding ≫ chart = bothChart`.
4. Since `f i j` is mono, `p` equals the shape-dispatched embedding `tateSelfProductBothEmbedding`
   (`tateSelfProductBothChartFst_eq_embedding`), whence each `ιₛ ≫ p` is the explicit `qₛ`.

The delicate `isDefEq` over the giant completed-tensor chart terms is avoided by cancelling the mono
`f i j` in term mode and reducing every square to `mapSpf`-functoriality (`mapSpf_comp`), never
`rw`-ing a big chart lemma under a motive.

## Main definitions / results

* `AlgebraicGeometry.tateSelfProductBothChartFst`: the embedding `p` of the both-overlap object into
  the `ij`-overlap object `V i j`.
* `AlgebraicGeometry.firstFactorBothEmbedding` / `secondFactorBothEmbedding`: the explicit
  four-summand embeddings into the first- and second-factor overlap objects.
* `AlgebraicGeometry.firstFactorBothEmbedding_comp` / `secondFactorBothEmbedding_comp`: the
  reusable factorizations `embedding ≫ chart = bothChart`.
* `AlgebraicGeometry.tateSelfProductBothEmbedding`: the shape-dispatched embedding.
* `AlgebraicGeometry.tateSelfProductBothChartFst_comp`: the uniform leg law `p ≫ f i j = bothChart`.
* `AlgebraicGeometry.tateSelfProductBothChartFst_eq_embedding`: `p = tateSelfProductBothEmbedding`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* Mathlib `CategoryTheory.GlueData'` (the `t'`/`t_fac`/`cocycle` fields).
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
  AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
  CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-! ### The localization `R`-algebra map and a `mapSpf` congruence -/

/-- The localization `R`-algebra map `A →ₐ[R] A{1/f}` (the scalar tower `A → A_f → A{1/f}`), the
building block of every summand embedding. -/
private abbrev locHom (f : annulusAlgebra R I q) :
    annulusAlgebra R I q →ₐ[R]
      awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) f :=
  IsScalarTower.toAlgHom R (annulusAlgebra R I q)
    (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) f)

/-- `mapSpf` depends only on the two `R`-algebra maps. -/
private theorem mapSpf_congr {A₀ B₀ A₁ B₁ : Type u} [CommRing A₀] [CommRing B₀] [CommRing A₁]
    [CommRing B₁] [Algebra R A₀] [Algebra R B₀] [Algebra R A₁] [Algebra R B₁] (hI : I.FG)
    {f₁ f₂ : A₀ →ₐ[R] A₁} {g₁ g₂ : B₀ →ₐ[R] B₁} (hf : f₁ = f₂) (hg : g₁ = g₂) :
    CompletedTensorProduct.mapSpf hI f₁ g₁ = CompletedTensorProduct.mapSpf hI f₂ g₂ := by
  subst hf hg
  rfl

/-! ### The two per-summand leg factorizations

Each both-localized chart `bothInterchange a b` factors through one leg of a triple-overlap chart by
localizing the *untouched* tensor factor. These are the residual analogues of `firstBoth_*_key` /
`rightBoth_*_key` (`CompletedTensorAwayInterchangeBothPullback`) but with an *identity* residual on
the localized factor rather than a `furtherLoc`, so no `mul` padding of the away element occurs. -/

/-- **First-factor leg factorization.** Localizing the second tensor factor `A → A{1/b}` (identity
on the first factor `A{1/a}`), then applying the first-factor interchange chart at `a`, gives the
both-localized chart at `(a, b)`. Pure `mapSpf`-functoriality. -/
theorem mapSpf_id_loc_comp_interchange (a b : annulusAlgebra R I q) (hI : I.FG) :
    CompletedTensorProduct.mapSpf hI
        (AlgHom.id R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) a))
        (locHom R I q b) ≫
      interchangeOpenImmersion (B := annulusAlgebra R I q) I a hI =
      bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I a b
        hI := by
  rw [interchangeOpenImmersion_eq_mapSpf (B := annulusAlgebra R I q) I a hI,
    bothInterchangeOpenImmersion_eq_mapSpf I a b hI, ← CompletedTensorProduct.mapSpf_comp]
  exact mapSpf_congr R I hI (AlgHom.id_comp _) (AlgHom.comp_id _)

/-- **Second-factor leg factorization.** Localizing the first tensor factor `A → A{1/a}` (identity
on the second factor `A{1/b}`), then applying the second-factor interchange chart at `b`, gives the
both-localized chart at `(a, b)`. Pure `mapSpf`-functoriality. -/
theorem mapSpf_loc_id_comp_rightInterchange (a b : annulusAlgebra R I q) (hI : I.FG) :
    CompletedTensorProduct.mapSpf hI (locHom R I q a)
        (AlgHom.id R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) b)) ≫
      rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I b hI =
      bothInterchangeOpenImmersion (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) I a b
        hI := by
  rw [rightInterchangeOpenImmersion_eq_mapSpf (A := annulusAlgebra R I q) I b hI,
    bothInterchangeOpenImmersion_eq_mapSpf I a b hI, ← CompletedTensorProduct.mapSpf_comp]
  exact mapSpf_congr R I hI (AlgHom.comp_id _) (AlgHom.id_comp _)

/-! ### The explicit four-summand embeddings and their chart factorizations -/

/-- **The first-factor both-embedding** `(dXX ⨿ dXY) ⨿ (dYX ⨿ dYY) ⟶ dXA ⨿ dYA`: on each summand
`d_{a,b}` it localizes the second tensor factor `A → A{1/b}` and lands in the `a`-summand of the
first-factor overlap object. It is the shape-dispatched embedding `p` for the chart pairs `(i, j)`
differing only in the first coordinate. -/
def firstFactorBothEmbedding (hI : I.FG) :
    ((dXX R I q ⨿ dXY R I q) ⨿ (dYX R I q ⨿ dYY R I q)) ⟶ (dXA R I q ⨿ dYA R I q) :=
  coprod.desc
    (coprod.desc
      (CompletedTensorProduct.mapSpf hI
          (AlgHom.id R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
            (overlapX R I q)))
          (locHom R I q (overlapX R I q)) ≫ coprod.inl)
      (CompletedTensorProduct.mapSpf hI
          (AlgHom.id R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
            (overlapX R I q)))
          (locHom R I q (overlapY R I q)) ≫ coprod.inl))
    (coprod.desc
      (CompletedTensorProduct.mapSpf hI
          (AlgHom.id R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
            (overlapY R I q)))
          (locHom R I q (overlapX R I q)) ≫ coprod.inr)
      (CompletedTensorProduct.mapSpf hI
          (AlgHom.id R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
            (overlapY R I q)))
          (locHom R I q (overlapY R I q)) ≫ coprod.inr))

/-- **The second-factor both-embedding** `(dXX ⨿ dXY) ⨿ (dYX ⨿ dYY) ⟶ dAX ⨿ dAY`: on each summand
`d_{a,b}` it localizes the first tensor factor `A → A{1/a}` and lands in the `b`-summand of the
second-factor overlap object. It is the shape-dispatched embedding `p` for the chart pairs `(i, j)`
differing only in the second coordinate. -/
def secondFactorBothEmbedding (hI : I.FG) :
    ((dXX R I q ⨿ dXY R I q) ⨿ (dYX R I q ⨿ dYY R I q)) ⟶ (dAX R I q ⨿ dAY R I q) :=
  coprod.desc
    (coprod.desc
      (CompletedTensorProduct.mapSpf hI (locHom R I q (overlapX R I q))
          (AlgHom.id R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
            (overlapX R I q))) ≫ coprod.inl)
      (CompletedTensorProduct.mapSpf hI (locHom R I q (overlapX R I q))
          (AlgHom.id R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
            (overlapY R I q))) ≫ coprod.inr))
    (coprod.desc
      (CompletedTensorProduct.mapSpf hI (locHom R I q (overlapY R I q))
          (AlgHom.id R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
            (overlapX R I q))) ≫ coprod.inl)
      (CompletedTensorProduct.mapSpf hI (locHom R I q (overlapY R I q))
          (AlgHom.id R (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
            (overlapY R I q))) ≫ coprod.inr))

/-- **First-factor embedding factorization.** Composing `firstFactorBothEmbedding` with the
first-factor overlap chart recovers the both-factor overlap chart. Proved summand-by-summand by
`coprod.hom_ext`, each summand collapsing by the leg factorization
`mapSpf_id_loc_comp_interchange`. -/
theorem firstFactorBothEmbedding_comp (hI : I.FG) :
    firstFactorBothEmbedding R I q hI ≫ firstFactorOverlapChart R I q hI =
      bothFactorOverlapChart R I q hI := by
  refine coprod.hom_ext (coprod.hom_ext ?_ ?_) (coprod.hom_ext ?_ ?_)
  · simp only [firstFactorBothEmbedding, firstFactorOverlapChart, bothFactorOverlapChart,
      coprod.inl_desc_assoc, coprod.inl_desc, Category.assoc]
    exact mapSpf_id_loc_comp_interchange R I q (overlapX R I q) (overlapX R I q) hI
  · simp only [firstFactorBothEmbedding, firstFactorOverlapChart, bothFactorOverlapChart,
      coprod.inl_desc_assoc, coprod.inr_desc_assoc, coprod.inl_desc, coprod.inr_desc,
      Category.assoc]
    exact mapSpf_id_loc_comp_interchange R I q (overlapX R I q) (overlapY R I q) hI
  · simp only [firstFactorBothEmbedding, firstFactorOverlapChart, bothFactorOverlapChart,
      coprod.inl_desc_assoc, coprod.inr_desc_assoc, coprod.inl_desc, coprod.inr_desc,
      Category.assoc]
    exact mapSpf_id_loc_comp_interchange R I q (overlapY R I q) (overlapX R I q) hI
  · simp only [firstFactorBothEmbedding, firstFactorOverlapChart, bothFactorOverlapChart,
      coprod.inr_desc_assoc, coprod.inr_desc, Category.assoc]
    exact mapSpf_id_loc_comp_interchange R I q (overlapY R I q) (overlapY R I q) hI

/-- **Second-factor embedding factorization.** Composing `secondFactorBothEmbedding` with the
second-factor overlap chart recovers the both-factor overlap chart. Proved summand-by-summand by
`coprod.hom_ext`, each summand collapsing by the leg factorization
`mapSpf_loc_id_comp_rightInterchange`. -/
theorem secondFactorBothEmbedding_comp (hI : I.FG) :
    secondFactorBothEmbedding R I q hI ≫ secondFactorOverlapChart R I q hI =
      bothFactorOverlapChart R I q hI := by
  refine coprod.hom_ext (coprod.hom_ext ?_ ?_) (coprod.hom_ext ?_ ?_)
  · simp only [secondFactorBothEmbedding, secondFactorOverlapChart, bothFactorOverlapChart,
      coprod.inl_desc_assoc, coprod.inl_desc, Category.assoc]
    exact mapSpf_loc_id_comp_rightInterchange R I q (overlapX R I q) (overlapX R I q) hI
  · simp only [secondFactorBothEmbedding, secondFactorOverlapChart, bothFactorOverlapChart,
      coprod.inl_desc_assoc, coprod.inr_desc_assoc, coprod.inl_desc, coprod.inr_desc,
      Category.assoc]
    exact mapSpf_loc_id_comp_rightInterchange R I q (overlapX R I q) (overlapY R I q) hI
  · simp only [secondFactorBothEmbedding, secondFactorOverlapChart, bothFactorOverlapChart,
      coprod.inl_desc_assoc, coprod.inr_desc_assoc, coprod.inl_desc, coprod.inr_desc,
      Category.assoc]
    exact mapSpf_loc_id_comp_rightInterchange R I q (overlapY R I q) (overlapX R I q) hI
  · simp only [secondFactorBothEmbedding, secondFactorOverlapChart, bothFactorOverlapChart,
      coprod.inr_desc_assoc, coprod.inr_desc, Category.assoc]
    exact mapSpf_loc_id_comp_rightInterchange R I q (overlapY R I q) (overlapY R I q) hI

/-! ### The embedding `p` and its uniform leg law -/

/-- **The both-overlap embedding** `p : bothOverlapObj ⟶ V i j` into the `ij`-overlap object: the
`hom` of the uniform both-overlap iso followed by `pullback.fst (f i j) (f i k)`. -/
def tateSelfProductBothChartFst (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i j hij)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i k hik)]
    [LocallyRingedSpace.IsOpenImmersion (bothFactorOverlapChart R I q hI)] :
    ((dXX R I q ⨿ dXY R I q) ⨿ (dYX R I q ⨿ dYY R I q)) ⟶
      tateSelfProductGlueV R I q hI i j hij :=
  (tateSelfProductBothChartIso R I q hI i j k hij hik hjk).hom ≫
    pullback.fst (tateSelfProductGlueF R I q hI i j hij)
      (tateSelfProductGlueF R I q hI i k hik)

/-- **The uniform leg law** `p ≫ f i j = bothChart`: the both-overlap embedding, followed by the
`ij`-overlap chart into `Spf C`, is the both-factor overlap chart. A re-association of the
already-proved `tateSelfProductBothChartIso_hom_fst_comp`; uniform in the triple. -/
theorem tateSelfProductBothChartFst_comp (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i j hij)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i k hik)]
    [LocallyRingedSpace.IsOpenImmersion (bothFactorOverlapChart R I q hI)] :
    tateSelfProductBothChartFst R I q hI i j k hij hik hjk ≫
        tateSelfProductGlueF R I q hI i j hij =
      bothFactorOverlapChart R I q hI := by
  rw [tateSelfProductBothChartFst, Category.assoc]
  exact tateSelfProductBothChartIso_hom_fst_comp R I q hI i j k hij hik hjk

/-! ### The shape-dispatched embedding and the identification `p = embedding` -/

/-- **The shape-dispatched both-embedding** `tateSelfProductBothEmbedding i j h : bothOverlapObj ⟶
V i j h`: the `firstFactorBothEmbedding`, the `secondFactorBothEmbedding`, or the identity
`𝟙 bothOverlapObj`, according to the difference type of `i` and `j` — mirroring the dispatch of
`tateSelfProductGlueV`/`tateSelfProductGlueF`. It is the closed form of the both-overlap embedding
`p`. -/
def tateSelfProductBothEmbedding (hI : I.FG) :
    ∀ (i j : Bool × Bool) (h : i ≠ j),
      ((dXX R I q ⨿ dXY R I q) ⨿ (dYX R I q ⨿ dYY R I q)) ⟶
        tateSelfProductGlueV R I q hI i j h :=
  fun i j h => match i, j, h with
  | (false, false), (false, false), h => (h rfl).elim
  | (false, false), (false, true), _ => secondFactorBothEmbedding R I q hI
  | (false, false), (true, false), _ => firstFactorBothEmbedding R I q hI
  | (false, false), (true, true), _ => 𝟙 _
  | (false, true), (false, false), _ => secondFactorBothEmbedding R I q hI
  | (false, true), (false, true), h => (h rfl).elim
  | (false, true), (true, false), _ => 𝟙 _
  | (false, true), (true, true), _ => firstFactorBothEmbedding R I q hI
  | (true, false), (false, false), _ => firstFactorBothEmbedding R I q hI
  | (true, false), (false, true), _ => 𝟙 _
  | (true, false), (true, false), h => (h rfl).elim
  | (true, false), (true, true), _ => secondFactorBothEmbedding R I q hI
  | (true, true), (false, false), _ => 𝟙 _
  | (true, true), (false, true), _ => firstFactorBothEmbedding R I q hI
  | (true, true), (true, false), _ => secondFactorBothEmbedding R I q hI
  | (true, true), (true, true), h => (h rfl).elim

/-- **The dispatched embedding leg law** `tateSelfProductBothEmbedding i j ≫ f i j = bothChart`.
Proved by a `Bool × Bool` case split on `(i, j)` (16 cases, four diagonal ones excluded by `hij`):
each shape collapses by the corresponding embedding factorization
`firstFactorBothEmbedding_comp`/`secondFactorBothEmbedding_comp`, the both-both shape being the
identity. Instance-free, so the case split does not disturb the open-immersion hypotheses. -/
theorem tateSelfProductBothEmbedding_comp (hI : I.FG) (i j : Bool × Bool) (hij : i ≠ j) :
    tateSelfProductBothEmbedding R I q hI i j hij ≫ tateSelfProductGlueF R I q hI i j hij =
      bothFactorOverlapChart R I q hI := by
  revert hij
  rcases i with ⟨(_ | _), (_ | _)⟩ <;> rcases j with ⟨(_ | _), (_ | _)⟩ <;> intro hij <;>
    first
      | exact absurd rfl hij
      | (dsimp only [tateSelfProductBothEmbedding, tateSelfProductGlueF]
         first
           | exact firstFactorBothEmbedding_comp R I q hI
           | exact secondFactorBothEmbedding_comp R I q hI
           | exact Category.id_comp _)

/-- **The identification `p = tateSelfProductBothEmbedding`.** For every pairwise-distinct triple
the both-overlap embedding `p` equals the shape-dispatched explicit embedding. Cancelling the
monomorphism `f i j`, the two sides agree by the uniform leg law `tateSelfProductBothChartFst_comp`
and the dispatched leg law `tateSelfProductBothEmbedding_comp`. Consequently each summand
restriction `ιₛ ≫ p` is the explicit `qₛ` read off `tateSelfProductBothEmbedding`. -/
theorem tateSelfProductBothChartFst_eq_embedding (hq : q ∈ I) (hI : I.FG) (i j k : Bool × Bool)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i j hij)]
    [LocallyRingedSpace.IsOpenImmersion (tateSelfProductGlueF R I q hI i k hik)]
    [LocallyRingedSpace.IsOpenImmersion (bothFactorOverlapChart R I q hI)] :
    tateSelfProductBothChartFst R I q hI i j k hij hik hjk =
      tateSelfProductBothEmbedding R I q hI i j hij := by
  haveI := tateSelfProductGlueF_mono R I q hq hI i j hij
  rw [← cancel_mono (tateSelfProductGlueF R I q hI i j hij),
    tateSelfProductBothChartFst_comp R I q hI i j k hij hik hjk,
    tateSelfProductBothEmbedding_comp R I q hI i j hij]

end AlgebraicGeometry

end
