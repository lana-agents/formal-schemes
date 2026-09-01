import FormalSchemes.TwoPatchFibreProductObject

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The general fibre product `X ×_{Spf R} Spf B` of an affine-charted glued `X` over an affine base

Fix an adic base `(R, I)` with `I` finitely generated, and an affine base change `Y = Spf B`. Let
`X` be a formal scheme glued from **affine charts** `Spf A_i` (`i : J`) over `Spf R`, whose double
overlaps are the away-completions `Spf(A_i{1/g_ij})` and whose transition isomorphisms come from
`R`-algebra isomorphisms `τ_ij : A_i{1/g_ij} ≃ₐ[R] A_j{1/g_ji}`. This file generalises the two-patch
template `AlgebraicGeometry.twoPatchFibreProduct`
(`FormalSchemes.TwoPatchFibreProductObject`, `X = tateTwoPatch`, `J = Bool`) to an **arbitrary**
index type `J`, delivering the fibre product `X ×_{Spf R} Spf B` as a glued `FormalScheme`.

## What is new over the template

The template lives on `J = ULift Bool`, where no triple of indices is pairwise distinct, so the
cocycle fields `t'`, `t_fac`, `cocycle` of the underlying `CategoryTheory.GlueData'` are
**vacuous** (`uliftBool_not_pairwise_distinct`). For a general index type the cocycle is genuine,
and its content is transported from `X`'s own transition data by the `⊗̂_R B` functoriality of
the fibre-product map `CompletedTensorProduct.mapSpf`. The *engine* of that transport is recorded
here as two reusable, standalone lemmas over `mapSpf`:

* `CompletedTensorProduct.mapSpfIso_symm`: the `mapSpf`-isomorphism of a pair of *inverse* algebra
  isomorphisms is the inverse isomorphism, so the self-inverse law `t i j ≫ t j i = 𝟙` of a glue
  transition built as `mapSpfIso τ` reduces to `τ_ji = τ_ij⁻¹` at the algebra level;
* `CompletedTensorProduct.mapSpf_comp₃`: three `mapSpf`'s whose underlying `R`-algebra maps compose
  (cyclically) to the identity pair compose to the identity morphism of formal spectra — the
  geometric **triple cocycle** carried by `mapSpf_comp`/`mapSpf_id`. This is exactly the reduction
  that turns `X`'s algebra-level cocycle into the geometric `cocycle` of `X ×_{Spf R} Spf B`, and it
  is *not* `⊗̂`-associativity (which is a separate later brick).

These are the `⊗̂_R B` base-change transport of a `GlueData'` cocycle. They are stated purely over
`mapSpf` (no pullbacks), so they apply verbatim to the self-inverse `t_inv` law of the general glue
datum below and are the intended inputs to the geometric `t'`/`cocycle` fields.

## The general input datum and the assembled fibre product

`AlgebraicGeometry.AffineChartedFibreDatum` packages a general affine-charted `X` over `Spf R`
together with the affine base `B`: the index `J`, the chart `R`-algebras `A i`, the away elements
`g i j : A i` cutting out the overlaps, the `R`-algebra transitions `τ i j` (with the symmetry
`τ_symm`), and — as data — the geometric triple-overlap fields `t'`, `t_fac`, `cocycle` of the
fibre-product glue (the pullback-level datum whose *construction* from `τ` is the deferred
interchange-pullback brick, but whose *laws* are the transported cocycle above). From it we build,
mirroring the template:

* `AffineChartedFibreDatum.glueData'`: the `CategoryTheory.GlueData'` on `LocallyRingedSpace` whose
  charts are `Spf(A_i ⊗̂_R B)`, whose overlap immersions `f` are `interchangeOpenImmersion`, and
  whose transitions `t = (mapSpfIso τ (AlgEquiv.refl R B)).hom`; the structural laws `f_mono`,
  `f_hasPullback` and `t_inv` are discharged uniformly (the last via `mapSpfIso_refl_inv`);
* `AffineChartedFibreDatum.lrsGlueData`, `...formalGlueData`: the glue datum as a
  `LocallyRingedSpace.GlueData` (via `GlueData.ofGlueData'` + `f_open`) and as a
  `FormalScheme.GlueData`;
* `AffineChartedFibreDatum.fibreProduct`: the glued fibre product `X ×_{Spf R} Spf B`.

The template's `twoPatchFibreProduct` is the specialisation of this construction to the two-chart
Tate datum; see `AlgebraicGeometry.twoPatchFibreProductDatum` at the end of the file.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
open CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace CompletedTensorProduct

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {A B A' B' A'' B'' : Type u}
variable [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable [CommRing A'] [CommRing B'] [Algebra R A'] [Algebra R B']
variable [CommRing A''] [CommRing B''] [Algebra R A''] [Algebra R B'']

/-- **The `mapSpf`-isomorphism of a pair of inverse algebra isomorphisms is the inverse
isomorphism.** Equivalently, `mapSpfIso` sends `AlgEquiv.symm` to `Iso.symm`. This is the
algebra-level reduction of the self-inverse law `t i j ≫ t j i = 𝟙` for a glue transition built as
`t = (mapSpfIso τ).hom`: it holds as soon as `τ_ji = τ_ij⁻¹`. -/
theorem mapSpfIso_symm (hI : I.FG) (e₁ : A ≃ₐ[R] A') (e₂ : B ≃ₐ[R] B') :
    haveI := isAdicRing R I A B hI
    haveI := isAdicRing R I A' B' hI
    mapSpfIso hI e₁.symm e₂.symm = (mapSpfIso hI e₁ e₂).symm := by
  haveI := isAdicRing R I A B hI
  haveI := isAdicRing R I A' B' hI
  apply Iso.ext
  simp only [mapSpfIso_hom, mapSpfIso_inv, Iso.symm_hom, AlgEquiv.symm_symm]

/-- **Geometric triple cocycle for `mapSpf`.** If the three underlying `R`-algebra maps compose
(cyclically) to the identity pair, then the three induced morphisms of formal spectra compose to the
identity morphism. This is the `⊗̂_R B` base-change transport of a `GlueData'` triple cocycle:
`mapSpf_comp` collapses the composite to `mapSpf` of the algebra composite, which is `mapSpf` of the
identity pair, hence `𝟙` by `mapSpf_id`. -/
theorem mapSpf_comp₃ (hI : I.FG) (f : A →ₐ[R] A') (g : B →ₐ[R] B') (f' : A' →ₐ[R] A'')
    (g' : B' →ₐ[R] B'') (f'' : A'' →ₐ[R] A) (g'' : B'' →ₐ[R] B)
    (hf : f''.comp (f'.comp f) = AlgHom.id R A) (hg : g''.comp (g'.comp g) = AlgHom.id R B) :
    haveI := isAdicRing R I A B hI
    haveI := isAdicRing R I A' B' hI
    haveI := isAdicRing R I A'' B'' hI
    mapSpf hI f'' g'' ≫ mapSpf hI f' g' ≫ mapSpf hI f g = 𝟙 _ := by
  haveI := isAdicRing R I A B hI
  haveI := isAdicRing R I A' B' hI
  haveI := isAdicRing R I A'' B'' hI
  rw [← mapSpf_comp hI f g f' g', ← mapSpf_comp hI (f'.comp f) (g'.comp g) f'' g'', hf, hg,
    mapSpf_id]

/-- **Self-inverse law for a base-changed transition.** When the second factor is fixed to the
identity of the base `B`, the `mapSpfIso` of an algebra isomorphism `e` and of its inverse `e.symm`
compose (as `hom`s) to the identity. This is the reduction of the `t_inv` field of the general glue
datum below: the transition `t i j = (mapSpfIso τ_ij).hom` and its opposite `t j i` are mutually
inverse because `τ_ji = τ_ij⁻¹`. -/
theorem mapSpfIso_refl_inv (hI : I.FG) (e : A ≃ₐ[R] A') :
    haveI := isAdicRing R I A B hI
    haveI := isAdicRing R I A' B hI
    (mapSpfIso hI e (AlgEquiv.refl (R := R) (A₁ := B))).hom ≫
      (mapSpfIso hI e.symm (AlgEquiv.refl (R := R) (A₁ := B))).hom = 𝟙 _ := by
  haveI := isAdicRing R I A B hI
  haveI := isAdicRing R I A' B hI
  rw [mapSpfIso_hom, mapSpfIso_hom, ← mapSpf_comp]
  have hf : e.symm.toAlgHom.comp e.symm.symm.toAlgHom = AlgHom.id R A := by
    ext x
    simp
  have hg : (AlgEquiv.refl (R := R) (A₁ := B)).symm.toAlgHom.comp
      (AlgEquiv.refl (R := R) (A₁ := B)).symm.toAlgHom = AlgHom.id R B := by
    ext x
    simp
  rw [hf, hg, mapSpf_id]

end CompletedTensorProduct

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (hI : I.FG)
variable (B : Type u) [CommRing B] [Algebra R B]

/-! ### The general affine-charted fibre-product input datum -/

set_option linter.unusedVariables false in
/-- **A general affine-charted glued `X` over `Spf R`, together with an affine base `Spf B`.**
This is the input datum for the fibre product `X ×_{Spf R} Spf B`. It records:

* an index type `J` and, for each `i`, a chart `R`-algebra `A i` (so the `i`-th chart of `X` is
  `Spf (A i)`);
* for each ordered pair `i j` an away element `g i j : A i`, cutting out the double overlap
  `Spf (A_i{1/g_ij})` of the `i`-th chart;
* the `R`-algebra transition isomorphisms `τ i j : A_i{1/g_ij} ≃ₐ[R] A_j{1/g_ji}` between the two
  presentations of the overlap, with the symmetry `τ_symm : τ j i = (τ i j)⁻¹`;
* the *geometric* triple-overlap datum `t'`, together with its two laws `t_fac` and `cocycle`, of
  the **fibre-product** glue (the pullback-level maps whose construction from `τ` is the deferred
  interchange-pullback identification, but whose cocycle law is the `⊗̂_R B`-transport
  `CompletedTensorProduct.mapSpf_comp₃`).

Everything else — the charts `Spf(A_i ⊗̂_R B)`, the overlap immersions `interchangeOpenImmersion`,
the base-changed transitions `mapSpfIso τ`, and the structural laws `f_mono`, `f_hasPullback`,
`t_inv` — is derived uniformly from this datum in `AffineChartedFibreDatum.glueData'`. -/
structure AffineChartedFibreDatum where
  /-- The index type of the charts of `X`. -/
  J : Type u
  /-- The chart `R`-algebra of the `i`-th affine chart `Spf (A i)` of `X`. -/
  A : J → Type u
  [commRing : ∀ i, CommRing (A i)]
  [algebra : ∀ i, Algebra R (A i)]
  /-- The away element cutting out the overlap of the `i`-th chart with the `j`-th. -/
  g : ∀ (i j : J), A i
  /-- The `R`-algebra transition `A_i{1/g_ij} ≃ₐ[R] A_j{1/g_ji}` between the two presentations of
  the double overlap. -/
  τ : ∀ (i j : J), i ≠ j →
    (awayCompletion (I.map (algebraMap R (A i))) (g i j) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (A j))) (g j i))
  /-- The transitions are mutually inverse: `τ j i = (τ i j)⁻¹`. -/
  τ_symm : ∀ (i j : J) (h : i ≠ j), τ j i h.symm = (τ i j h).symm
  /-- The geometric triple-overlap transition of the fibre-product glue. -/
  t' : ∀ (i j k : J) (_hij : i ≠ j) (_hik : i ≠ k) (_hjk : j ≠ k),
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g i j) hI
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g i k) hI
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g j k) hI
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g j i) hI
    (pullback (interchangeOpenImmersion (B := B) I (g i j) hI)
        (interchangeOpenImmersion (B := B) I (g i k) hI) ⟶
      pullback (interchangeOpenImmersion (B := B) I (g j k) hI)
        (interchangeOpenImmersion (B := B) I (g j i) hI))
  /-- Compatibility of `t'` with the transition `t = (mapSpfIso τ).hom` (the `t_fac` law). -/
  t_fac : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g i j) hI
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g i k) hI
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g j k) hI
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g j i) hI
    t' i j k hij hik hjk ≫
        pullback.snd (interchangeOpenImmersion (B := B) I (g j k) hI)
          (interchangeOpenImmersion (B := B) I (g j i) hI) =
      pullback.fst (interchangeOpenImmersion (B := B) I (g i j) hI)
          (interchangeOpenImmersion (B := B) I (g i k) hI) ≫
        (mapSpfIso hI (τ i j hij) (AlgEquiv.refl (R := R) (A₁ := B))).hom
  /-- The triple cocycle of the fibre-product glue. -/
  cocycle : ∀ (i j k : J) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k),
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g i j) hI
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g i k) hI
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g j k) hI
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g j i) hI
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g k i) hI
    letI := isOpenImmersion_interchangeOpenImmersion (B := B) I (g k j) hI
    t' i j k hij hik hjk ≫ t' j k i hjk hij.symm hik.symm ≫
      t' k i j hik.symm hjk.symm hij = 𝟙 _

namespace AffineChartedFibreDatum

variable {R I hI B}
variable (D : AffineChartedFibreDatum R I hI B)

/-- **The affine-charted fibre-product glue datum** as a `CategoryTheory.GlueData'` on `D.J`: the
`i`-th chart is `Spf(A_i ⊗̂_R B)`, the overlap immersion `f i j` is `interchangeOpenImmersion`, the
transition `t i j` is `(mapSpfIso τ_ij (refl B)).hom`, and the cocycle fields `t'`, `t_fac`,
`cocycle` are the carried geometric datum of `D`. The structural laws `f_mono`, `f_hasPullback`
and `t_inv` are discharged uniformly (the latter via `mapSpfIso_refl_inv` and `τ_symm`). -/
def glueData' : CategoryTheory.GlueData' LocallyRingedSpace.{u} :=
  letI := D.commRing
  letI := D.algebra
  { J := D.J
    U := fun i => locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I (D.A i) B)
    V := fun i j _ => locallyRingedSpaceObj (CompletedTensorProduct.idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (D.A i))) (D.g i j)) B)
    f := fun i j _ => interchangeOpenImmersion (B := B) I (D.g i j) hI
    f_mono := fun i j _ => by
      haveI := isOpenImmersion_interchangeOpenImmersion (B := B) I (D.g i j) hI
      infer_instance
    f_hasPullback := fun i j k _ _ => by
      haveI := isOpenImmersion_interchangeOpenImmersion (B := B) I (D.g i j) hI
      infer_instance
    t := fun i j h => (mapSpfIso hI (D.τ i j h) (AlgEquiv.refl (R := R) (A₁ := B))).hom
    t' := D.t'
    t_fac := D.t_fac
    t_inv := fun i j h => by
      rw [D.τ_symm i j h]
      exact mapSpfIso_refl_inv hI (D.τ i j h)
    cocycle := D.cocycle }

/-- **The affine-charted fibre-product glue datum as a `LocallyRingedSpace.GlueData`**, via
`GlueData.ofGlueData'` and the open-immersion field `f_open`. Off the diagonal each glue map is
`eqToHom ≫ (interchange immersion)`; on the diagonal it is `eqToHom`. -/
def lrsGlueData : LocallyRingedSpace.GlueData.{u} :=
  letI := D.commRing
  letI := D.algebra
  { CategoryTheory.GlueData.ofGlueData' D.glueData' with
    f_open := by
      rintro i j
      simp only [glueData', CategoryTheory.GlueData.ofGlueData', CategoryTheory.GlueData'.f']
      split_ifs with h
      · exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (eqToHom _))
      · haveI := isOpenImmersion_interchangeOpenImmersion (B := B) I (D.g i j) hI
        exact inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
          (eqToHom _ ≫ interchangeOpenImmersion (B := B) I (D.g i j) hI)) }

/-- **The affine-charted fibre-product glue datum as a `FormalScheme.GlueData`**: each chart is the
affine formal scheme `Spf(A_i ⊗̂_R B)`. -/
def formalGlueData : FormalScheme.GlueData.{u} :=
  letI := D.commRing
  letI := D.algebra
  { toLocallyRingedSpaceGlueData := D.lrsGlueData
    isFormalScheme := fun i =>
      haveI : IsAdicRing (CompletedTensorProduct.idealOfDefinition R I (D.A i) B) :=
        CompletedTensorProduct.isAdicRing R I (D.A i) B hI
      ⟨FormalScheme.Spf (CompletedTensorProduct.idealOfDefinition R I (D.A i) B),
        ⟨Iso.refl _⟩⟩ }

/-- **The general fibre product `X ×_{Spf R} Spf B`** of an affine-charted glued `X` over the affine
base `Spf B`, as a glued formal scheme. Specialises to `twoPatchFibreProduct` on the two-chart Tate
datum. -/
def fibreProduct : FormalScheme.{u} :=
  D.formalGlueData.gluedFormalScheme

end AffineChartedFibreDatum

/-! ### Validation: the two-patch template as a special case

We exhibit the two-chart Tate fibre product `twoPatchFibreProduct`
(`FormalSchemes.TwoPatchFibreProductObject`) as an instance of the general construction, by
packaging its chart/overlap/transition data into an `AffineChartedFibreDatum` on `J = ULift Bool`.
Because no
triple of `Bool`-indices is pairwise distinct, the geometric cocycle fields `t'`, `t_fac`, `cocycle`
of the datum are vacuous, exactly as in the template. -/

/-- **The two-chart Tate fibre product as an `AffineChartedFibreDatum`.** The charts are two copies
of `Spf(annulusAlgebra R I q)`, the away elements are the annulus overlap parameters `overlapX` /
`overlapY`, and the transition is the base-change chart transition `annulusFibreChartTransitionAlg`
(and its inverse). This witnesses that the general `AffineChartedFibreDatum.fibreProduct` subsumes
the two-patch template `twoPatchFibreProduct`. -/
def twoPatchFibreProductDatum (R : Type u) [CommRing R] (I : Ideal R) (q : R) (hI : I.FG)
    (B : Type u) [CommRing B] [Algebra R B] : AffineChartedFibreDatum R I hI B where
  J := ULift.{u} Bool
  A := fun _ => annulusAlgebra R I q
  g := fun i _ => cond i.down (overlapY R I q) (overlapX R I q)
  τ := fun i j h => match i, j, h with
    | ⟨false⟩, ⟨true⟩, _ => annulusFibreChartTransitionAlg R I q hI
    | ⟨true⟩, ⟨false⟩, _ => (annulusFibreChartTransitionAlg R I q hI).symm
    | ⟨false⟩, ⟨false⟩, h => (h rfl).elim
    | ⟨true⟩, ⟨true⟩, h => (h rfl).elim
  τ_symm := by
    rintro ⟨_ | _⟩ ⟨_ | _⟩ h
    · exact absurd rfl h
    · rfl
    · exact ((annulusFibreChartTransitionAlg R I q hI).symm_symm).symm
    · exact absurd rfl h
  t' := fun _ _ _ hij hik hjk => (uliftBool_not_pairwise_distinct hij hik hjk).elim
  t_fac := fun _ _ _ hij hik hjk => (uliftBool_not_pairwise_distinct hij hik hjk).elim
  cocycle := fun _ _ _ hij hik hjk => (uliftBool_not_pairwise_distinct hij hik hjk).elim

end AlgebraicGeometry
