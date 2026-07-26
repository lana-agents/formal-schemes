import FormalSchemes.TwoPatchFibreProduct

set_option linter.style.header false

/-!
# The two-patch fibre product `X ×_{Spf R} Spf B` as a glued formal scheme

Fix an adic base `R` with finitely generated ideal of definition `I` and a Tate parameter `q : R`,
and let `A = R{x, y} / (x·y − q)` be the coordinate ring of the formal Tate annulus. The two-patch
formal scheme `X = AlgebraicGeometry.tateTwoPatch` (`FormalSchemes.TateGlueTwoPatch`) is glued from
two copies of `Spf A` along the geometric overlap transition `annulusChartTransitionSpf`.

For an affine base change `Y = Spf B` this file assembles the **fibre product** `X ×_{Spf R} Spf B`
as a glued formal scheme: two copies of the affine chart `Spf(A ⊗̂_R B)` glued along the `⊗̂_R B`
base change of the annulus overlap transition. It is the direct base change of `TateGlueTwoPatch`,
and de-risks the `GlueData'` → `FormalScheme` pipeline that the general fibre products of issues
227/228 also flow through.

The two chart-overlap immersions `f` are the interchange open immersions
`interchangeOpenImmersion` (`FormalSchemes.CompletedTensorAwayInterchangeSpf`), realising
`Spf(A{1/x} ⊗̂_R B)` / `Spf(A{1/y} ⊗̂_R B)` as the basic opens `D(x̄)`, `D(ȳ)` of `Spf(A ⊗̂_R B)`.
The transition `t` is the base-changed overlap transition
`twoPatchFibreProductTransition : Spf(A{1/x} ⊗̂_R B) ≅ Spf(A{1/y} ⊗̂_R B)`, built by feeding the
`R`-algebra chart transition `annulusChartTransitionAlg` to `CompletedTensorProduct.mapSpfIso`.
Because the index type is `Bool`, no triple of indices is pairwise distinct, so the cocycle fields
`t'`, `t_fac`, `cocycle` of the `GlueData'` are vacuous — the same simplification that makes
`TateGlueTwoPatch` tractable.

The interchange immersions are indexed by the ideal of definition `I·A` of the annulus written as
the extension `I.map (algebraMap R A)`, whereas `TwoPatchFibreProduct` phrases its transition over
`annulusIdealOfDefinition`. The two ideals coincide by `annulus_map_eq`; the identification is
transported cheaply through `AdicCompletion.congrIdealₐ` (an *algebra* ideal-transport built by
`subst`), giving `annulusFibreChartTransitionAlg`, the chart transition presented over the ideal
convention the interchange immersions use, so no `eqToHom` bookkeeping is needed on the glue datum.

## Main definitions

* `AlgebraicGeometry.annulusFibreChartTransitionAlg`: the `R`-algebra chart transition
  `A{1/x} ≃ₐ[R] A{1/y}` presented over the ideal `I.map (algebraMap R A)`.
* `AlgebraicGeometry.twoPatchFibreProductTransition`: the base-changed transition of formal spectra
  `Spf(A{1/x} ⊗̂_R B) ≅ Spf(A{1/y} ⊗̂_R B)`, the transition datum `t` of the glue.
* `AlgebraicGeometry.twoPatchFibreProductGlueData'`, `...LRSGlueData`, `...FormalGlueData`: the glue
  datum in its three incarnations.
* `AlgebraicGeometry.twoPatchFibreProduct`: the glued fibre product `X ×_{Spf R} Spf B`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
open CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable (B : Type u) [CommRing B] [Algebra R B]

/-! ### The chart transition over the `I.map (algebraMap R A)` ideal convention -/

/-- The ideal-convention bridge on the `x`-chart: `A{1/x}` presented over `I.map (algebraMap R A)`
is identified as an `R`-algebra with the same completion presented over `annulusIdealOfDefinition`,
via `annulus_map_eq`. It is an `AdicCompletion.congrIdealₐ`, so the ideal transport never has to be
projected at a point. -/
def annulusFibreChartBridgeX :
    awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q) ≃ₐ[R]
      awayCompletion (annulusIdealOfDefinition R I q) (overlapX R I q) :=
  AdicCompletion.congrIdealₐ R
    (congrArg (Ideal.map (algebraMap (annulusAlgebra R I q) (Localization.Away (overlapX R I q))))
      (annulus_map_eq R I q))

/-- The `y`-analogue of `annulusFibreChartBridgeX`. -/
def annulusFibreChartBridgeY :
    awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q) ≃ₐ[R]
      awayCompletion (annulusIdealOfDefinition R I q) (overlapY R I q) :=
  AdicCompletion.congrIdealₐ R
    (congrArg (Ideal.map (algebraMap (annulusAlgebra R I q) (Localization.Away (overlapY R I q))))
      (annulus_map_eq R I q))

/-- **The `R`-algebra chart transition `A{1/x} ≃ₐ[R] A{1/y}`, over the `I.map (algebraMap R A)`
ideal convention** the interchange immersions use: the composite of the two ideal-convention bridges
with `annulusChartTransitionAlg`. -/
def annulusFibreChartTransitionAlg (hI : I.FG) :
    awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q) :=
  (annulusFibreChartBridgeX R I q).trans
    ((annulusChartTransitionAlg R I q hI).trans (annulusFibreChartBridgeY R I q).symm)

/-! ### The base-changed transition of the two-patch fibre product -/

/-- **The base-changed chart transition of `X ×_{Spf R} Spf B`**:
`Spf(A{1/x} ⊗̂_R B) ≅ Spf(A{1/y} ⊗̂_R B)`, the transition datum `t` of the two-patch fibre-product
glue, obtained by feeding `annulusFibreChartTransitionAlg` (and `AlgEquiv.refl R B`) to
`CompletedTensorProduct.mapSpfIso`. Its source and target are, definitionally, the domains of the
two interchange open immersions, so it slots into the glue datum without any transport. -/
def twoPatchFibreProductTransition (hI : I.FG) :
    haveI := CompletedTensorProduct.isAdicRing R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)) B hI
    haveI := CompletedTensorProduct.isAdicRing R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)) B hI
    FormalSpectrum.locallyRingedSpaceObj
        (CompletedTensorProduct.idealOfDefinition R I
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)) B) ≅
      FormalSpectrum.locallyRingedSpaceObj
        (CompletedTensorProduct.idealOfDefinition R I
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)) B) :=
  CompletedTensorProduct.mapSpfIso hI (annulusFibreChartTransitionAlg R I q hI)
    (AlgEquiv.refl (R := R) (A₁ := B))

/-! ### The glue datum -/

/-- The base chart `Spf(A ⊗̂_R B)`, the two patches to be glued. -/
private abbrev fpU : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q) B)

/-- The `x`-overlap `Spf(A{1/x} ⊗̂_R B)` (the `false`-side intersection). -/
private abbrev fpVx : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
    (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)) B)

/-- The `y`-overlap `Spf(A{1/y} ⊗̂_R B)` (the `true`-side intersection). -/
private abbrev fpVy : LocallyRingedSpace.{u} :=
  locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
    (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)) B)

/-- On a two-element index type no triple is pairwise distinct: this discharges the vacuous
`t'`, `t_fac` and `cocycle` fields of the two-patch glue data. -/
private theorem fpBool_not_pairwise_distinct {i j k : ULift.{u} Bool}
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) : False := by
  obtain ⟨i⟩ := i
  obtain ⟨j⟩ := j
  obtain ⟨k⟩ := k
  cases i <;> cases j <;> cases k <;> simp_all

/-- **The two-patch fibre-product glue datum** as a `CategoryTheory.GlueData'` on `ULift Bool`: two
copies of `Spf(A ⊗̂_R B)` glued along the interchange open immersions `f` and the base-changed
overlap transition `t = twoPatchFibreProductTransition`. The fields `t'`, `t_fac`, `cocycle` are
vacuous because no triple of `Bool`-indices is pairwise distinct. -/
def twoPatchFibreProductGlueData' (hI : I.FG) :
    CategoryTheory.GlueData' LocallyRingedSpace.{u} where
  J := ULift.{u} Bool
  U := fun _ => fpU R I q B
  V := fun i _ _ => cond i.down (fpVy R I q B) (fpVx R I q B)
  f := fun i j h => match i, j, h with
    | ⟨false⟩, ⟨true⟩, _ => interchangeOpenImmersion (B := B) I (overlapX R I q) hI
    | ⟨true⟩, ⟨false⟩, _ => interchangeOpenImmersion (B := B) I (overlapY R I q) hI
    | ⟨false⟩, ⟨false⟩, h => (h rfl).elim
    | ⟨true⟩, ⟨true⟩, h => (h rfl).elim
  f_mono := by
    haveI := isOpenImmersion_interchangeOpenImmersion (B := B) I (overlapX R I q) hI
    haveI := isOpenImmersion_interchangeOpenImmersion (B := B) I (overlapY R I q) hI
    rintro ⟨_ | _⟩ ⟨_ | _⟩ h
    · exact absurd rfl h
    · exact inferInstanceAs (Mono (interchangeOpenImmersion (B := B) I (overlapX R I q) hI))
    · exact inferInstanceAs (Mono (interchangeOpenImmersion (B := B) I (overlapY R I q) hI))
    · exact absurd rfl h
  f_hasPullback := by
    haveI := isOpenImmersion_interchangeOpenImmersion (B := B) I (overlapX R I q) hI
    haveI := isOpenImmersion_interchangeOpenImmersion (B := B) I (overlapY R I q) hI
    rintro ⟨_ | _⟩ ⟨_ | _⟩ ⟨_ | _⟩ hij hik
    · exact absurd rfl hij
    · exact absurd rfl hij
    · exact absurd rfl hik
    · exact inferInstanceAs (HasPullback
        (interchangeOpenImmersion (B := B) I (overlapX R I q) hI)
        (interchangeOpenImmersion (B := B) I (overlapX R I q) hI))
    · exact inferInstanceAs (HasPullback
        (interchangeOpenImmersion (B := B) I (overlapY R I q) hI)
        (interchangeOpenImmersion (B := B) I (overlapY R I q) hI))
    · exact absurd rfl hik
    · exact absurd rfl hij
    · exact absurd rfl hij
  t := fun i j h => match i, j, h with
    | ⟨false⟩, ⟨true⟩, _ => (twoPatchFibreProductTransition R I q B hI).hom
    | ⟨true⟩, ⟨false⟩, _ => (twoPatchFibreProductTransition R I q B hI).inv
    | ⟨false⟩, ⟨false⟩, h => (h rfl).elim
    | ⟨true⟩, ⟨true⟩, h => (h rfl).elim
  t' := fun _ _ _ hij hik hjk => (fpBool_not_pairwise_distinct hij hik hjk).elim
  t_fac := fun _ _ _ hij hik hjk => (fpBool_not_pairwise_distinct hij hik hjk).elim
  t_inv := by
    rintro ⟨_ | _⟩ ⟨_ | _⟩ h
    · exact absurd rfl h
    · exact (twoPatchFibreProductTransition R I q B hI).hom_inv_id
    · exact (twoPatchFibreProductTransition R I q B hI).inv_hom_id
    · exact absurd rfl h
  cocycle := fun _ _ _ hij hik hjk => (fpBool_not_pairwise_distinct hij hik hjk).elim

/-- **The two-patch fibre-product glue datum as a `LocallyRingedSpace.GlueData`**, via
`GlueData.ofGlueData'` together with the open-immersion field `f_open`. Off the diagonal each glue
map is `eqToHom ≫ (interchange immersion)`, a composite of an isomorphism with an open immersion; on
the diagonal it is `eqToHom`, an isomorphism. -/
def twoPatchFibreProductLRSGlueData (hI : I.FG) : LocallyRingedSpace.GlueData.{u} :=
  { CategoryTheory.GlueData.ofGlueData' (twoPatchFibreProductGlueData' R I q B hI) with
    f_open := by
      haveI := isOpenImmersion_interchangeOpenImmersion (B := B) I (overlapX R I q) hI
      haveI := isOpenImmersion_interchangeOpenImmersion (B := B) I (overlapY R I q) hI
      rintro i j
      simp only [CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f']
      split_ifs with h
      · exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (eqToHom _))
      · rcases i with ⟨_ | _⟩ <;> rcases j with ⟨_ | _⟩
        · exact absurd rfl h
        · exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
            (eqToHom _ ≫ interchangeOpenImmersion (B := B) I (overlapX R I q) hI))
        · exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
            (eqToHom _ ≫ interchangeOpenImmersion (B := B) I (overlapY R I q) hI))
        · exact absurd rfl h }

/-- **The two-patch fibre-product glue datum as a `FormalScheme.GlueData`**: each of the two pieces
is the affine formal scheme `Spf(A ⊗̂_R B)`, whose underlying locally ringed space is definitionally
the object `locallyRingedSpaceObj (I·(A ⊗̂_R B))` used as a patch. -/
def twoPatchFibreProductFormalGlueData (hI : I.FG) : FormalScheme.GlueData.{u} :=
  haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q) B) :=
    CompletedTensorProduct.isAdicRing R I (annulusAlgebra R I q) B hI
  { toLocallyRingedSpaceGlueData := twoPatchFibreProductLRSGlueData R I q B hI
    isFormalScheme := fun _ =>
      ⟨FormalScheme.Spf (CompletedTensorProduct.idealOfDefinition R I (annulusAlgebra R I q) B),
        ⟨Iso.refl _⟩⟩ }

/-- **The two-patch fibre product `X ×_{Spf R} Spf B`**: the (non-affine) formal scheme obtained by
gluing two copies of the affine chart `Spf(A ⊗̂_R B)` along the base-changed annulus overlap
transition. This is the fibre product of the two-patch Tate model `X = tateTwoPatch` with the affine
base `Spf B` over `Spf R`; the same recipe supplies the glued objects of issues 227/228. -/
def twoPatchFibreProduct (hI : I.FG) : FormalScheme.{u} :=
  (twoPatchFibreProductFormalGlueData R I q B hI).gluedFormalScheme

end AlgebraicGeometry
