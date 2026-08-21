import FormalSchemes.AdicCompletionCongrIdealAlg
import FormalSchemes.TateChartTransition
import FormalSchemes.TateChainStructMap
import FormalSchemes.CompletedTensorAwayInterchangeSpf
import FormalSchemes.CompletedTensorMapSpfIso
import FormalSchemes.Gluing

set_option linter.style.header false

/-!
# The base-changed chart transition of the two-patch fibre product `X ×_{Spf R} Spf B`

Fix an adic base `R` with finitely generated ideal of definition `I` and a Tate parameter `q : R`,
and let `A = R{x, y} / (x·y − q)` be the coordinate ring of the formal Tate annulus. The two-patch
formal scheme `X = AlgebraicGeometry.tateTwoPatch` (`FormalSchemes.TateGlueTwoPatch`) is glued from
two copies of `Spf A` along the geometric overlap transition
`annulusChartTransitionSpf : Spf A{1/x} ≅ Spf A{1/y}` (`FormalSchemes.TateChartTransition`).

For an affine base change `Y = Spf B`, the fibre product `X ×_{Spf R} Spf B` is again a two-chart
formal scheme, its charts `Spf(A ⊗̂_R B)` glued along the `⊗̂_R B` base change of the annulus
overlap transition. This file supplies the two ingredients that base change needs:

* `annulusChartTransitionAlg : A{1/x} ≃ₐ[R] A{1/y}` — the `R`-**algebra** upgrade of the chart
  transition. The geometric `annulusChartTransitionSpf` is assembled from bare ring isomorphisms and
  is *not* presented as an algebra isomorphism, but `CompletedTensorProduct.mapSpfIso`
  (`FormalSchemes.CompletedTensorMapSpfIso`) — which produces the base-changed transition — consumes
  an `R`-algebra isomorphism of the left factor. We build the upgrade as the composite of three
  `R`-algebra isomorphisms: the two chart-domain identifications `A{1/x} ≃ A[x⁻¹]^∧`,
  `A{1/y} ≃ A[y⁻¹]^∧` (each an `AdicCompletion.congrIdealₐ`, an *algebra* ideal-transport built by
  `subst`, so the pathologically expensive `congrIdeal` transport never has to be projected at a
  point) and the coordinate-swap overlap transition `annulusOverlapTransition : A[x⁻¹]^∧ ≃ A[y⁻¹]^∧`
  (whose `R`-linearity is its own `algebraMap` lemma).

* `twoPatchFibreTransition : Spf(A{1/x} ⊗̂_R B) ≅ Spf(A{1/y} ⊗̂_R B)` — the base-changed transition
  itself, obtained by feeding `annulusChartTransitionAlg` (and `AlgEquiv.refl R B` on the second
  factor) to `mapSpfIso`. This is precisely the double-overlap transition datum `t` of the two-patch
  fibre-product glue datum (issue 236), and the same recipe supplies the transitions of the glued
  fibre products of issues 227/228.

## Main definitions

* `AlgebraicGeometry.annulusChartTransitionAlg`: the `R`-algebra chart transition
  `A{1/x} ≃ₐ[R] A{1/y}`.
* `AlgebraicGeometry.twoPatchFibreTransition`: the base-changed transition of formal spectra
  `Spf(A{1/x} ⊗̂_R B) ≅ Spf(A{1/y} ⊗̂_R B)`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7, §9.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry FormalSpectrum

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-! ### The `R`-algebra chart transition `A{1/x} ≃ₐ[R] A{1/y}` -/

/-- The chart-domain identification `A{1/x} ≃ₐ[R] A[x⁻¹]^∧` as an `R`-algebra isomorphism, the
`R`-algebra upgrade of `awayCompletionEquivAnnulusOverlap`. -/
def annulusChartOverlapAlgX :
    awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q) ≃ₐ[R]
      annulusOverlap R I q :=
  AdicCompletion.congrIdealₐ R (annulusChart_locIdeal_eq R I q)

/-- The chart-domain identification `A{1/y} ≃ₐ[R] A[y⁻¹]^∧` as an `R`-algebra isomorphism, the
`y`-analogue of `annulusChartOverlapAlgX`. -/
def annulusChartOverlapAlgY :
    awayCompletion (annulusIdealOfDefinition R I q) (overlapY R I q) ≃ₐ[R]
      annulusOverlapY R I q :=
  AdicCompletion.congrIdealₐ R (annulusChartY_locIdeal_eq R I q)

/-- The coordinate-swap overlap transition `A[x⁻¹]^∧ ≃ₐ[R] A[y⁻¹]^∧` as an `R`-algebra isomorphism:
the `R`-algebra upgrade of `annulusOverlapTransition`; `R`-linearity comes from
`annulusOverlapTransitionHom_algebraMap` and `annulusLocTransition_algebraMap_R`. -/
def annulusOverlapTransitionAlg (hI : I.FG) :
    annulusOverlap R I q ≃ₐ[R] annulusOverlapY R I q :=
  AlgEquiv.ofRingEquiv (f := annulusOverlapTransition R I q hI) fun r => by
    rw [IsScalarTower.algebraMap_apply R (annulusLoc R I q) (annulusOverlap R I q),
      annulusOverlapTransition_apply, annulusOverlapTransitionHom_algebraMap,
      annulusLocTransition_algebraMap_R]
    exact (IsScalarTower.algebraMap_apply R (annulusLocY R I q) (annulusOverlapY R I q) r).symm

/-- **The `R`-algebra chart transition** `A{1/x} ≃ₐ[R] A{1/y}`: the composite of the two
chart-domain identifications with the coordinate-swap overlap transition. Feeding this to
`CompletedTensorProduct.mapSpfIso` produces the `⊗̂_R B` base-changed transition datum of the
two-patch fibre product `X ×_{Spf R} Spf B` (see `twoPatchFibreTransition`). -/
def annulusChartTransitionAlg (hI : I.FG) :
    awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q) ≃ₐ[R]
      awayCompletion (annulusIdealOfDefinition R I q) (overlapY R I q) :=
  (annulusChartOverlapAlgX R I q).trans
    ((annulusOverlapTransitionAlg R I q hI).trans (annulusChartOverlapAlgY R I q).symm)

/-! ### The base-changed transition of the two-patch fibre product -/

variable (B : Type u) [CommRing B] [Algebra R B]

/-- **The base-changed chart transition of `X ×_{Spf R} Spf B`**:
`Spf(A{1/x} ⊗̂_R B) ≅ Spf(A{1/y} ⊗̂_R B)`, the `⊗̂_R B` base change of the annulus overlap
transition, obtained by feeding `annulusChartTransitionAlg` and `AlgEquiv.refl R B` to
`CompletedTensorProduct.mapSpfIso`. This is the double-overlap transition datum `t` of the two-patch
fibre-product glue datum (issue 236). -/
def twoPatchFibreTransition (hI : I.FG) :
    haveI := CompletedTensorProduct.isAdicRing R I
      (awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q)) B hI
    haveI := CompletedTensorProduct.isAdicRing R I
      (awayCompletion (annulusIdealOfDefinition R I q) (overlapY R I q)) B hI
    FormalSpectrum.locallyRingedSpaceObj
        (CompletedTensorProduct.idealOfDefinition R I
          (awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q)) B) ≅
      FormalSpectrum.locallyRingedSpaceObj
        (CompletedTensorProduct.idealOfDefinition R I
          (awayCompletion (annulusIdealOfDefinition R I q) (overlapY R I q)) B) :=
  CompletedTensorProduct.mapSpfIso hI (annulusChartTransitionAlg R I q hI)
    (AlgEquiv.refl (R := R) (A₁ := B))

end AlgebraicGeometry
