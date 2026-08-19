import FormalSchemes.GraphCodiagonalClosedEmbedding
import FormalSchemes.TateSeparated

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000
set_option maxRecDepth 8000

/-!
# The two chart bridges of the Tate graph codiagonals

Fix an adic base `(R, I)` with `I` finitely generated and a Tate parameter `q ∈ R`, write
`A = annulusAlgebra R I q` and `Ω = annulusOverlap R I q = A[x⁻¹]^∧`.

The graph codiagonals `∇ˣ, ∇ʸ` of `GraphCodiagonalClosedEmbedding` live over the *curve* ideal
convention (`Ω`, `annulusOverlapIdeal`), while the interchange / `mapSpf` layer that computes inside
the four-chart Tate self-product uses the `I·A` convention `A{1/x} = awayCompletion (I·A) x`. This
file records the two `R`-algebra bridges relating them,

```
ψˣ : A{1/x} ≃ₐ[R] Ω        ψʸ : A{1/y} ≃ₐ[R] Ω
```

(the second one twisted by the inverse of the 𝔾m-inversion `Ω ≃ Ω_y`), together with the two facts
the geometric factorisation of the mixed-chart graph pieces consumes: the 𝔾m-inversion chart
transition intertwines `ψˣ` and `ψʸ`, and each bridge computes the structural map of `A`.

## Main results

* `graphChartAlgX`, `graphChartAlgY`: the two bridges.
* `annulusFibreChartTransitionInvAlg_trans_graphChartAlgY`: `τ⁻¹ ≫ ψʸ = ψˣ`.
* `graphChartAlgX_comp_algebraMap`: `ψˣ ∘ (A → A{1/x}) = (A → Ω)`.
* `graphChartAlgY_comp_algebraMap`: `ψʸ ∘ (A → A{1/y}) = invˣ ∘ (A → Ω) ∘ flip`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
-/

noncomputable section

open Ideal AlgebraicGeometry CategoryTheory FormalSpectrum CompletedTensorProduct

universe u

namespace AlgEquiv

variable {R A B C D : Type u} [CommSemiring R] [Semiring A] [Semiring B] [Semiring C] [Semiring D]
variable [Algebra R A] [Algebra R B] [Algebra R C] [Algebra R D]

/-- Composition of `R`-algebra equivalences is associative. -/
theorem trans_assoc' (e₁ : A ≃ₐ[R] B) (e₂ : B ≃ₐ[R] C) (e₃ : C ≃ₐ[R] D) :
    (e₁.trans e₂).trans e₃ = e₁.trans (e₂.trans e₃) :=
  AlgEquiv.ext fun _ => rfl

/-- The identity is a right unit for `trans`. -/
theorem trans_refl' (e : A ≃ₐ[R] B) : e.trans (AlgEquiv.refl : B ≃ₐ[R] B) = e :=
  AlgEquiv.ext fun _ => rfl

/-- The identity is a left unit for `trans`. -/
theorem refl_trans' (e : A ≃ₐ[R] B) : (AlgEquiv.refl : A ≃ₐ[R] A).trans e = e :=
  AlgEquiv.ext fun _ => rfl

/-- `e⁻¹ ≫ e ≫ f = f`, in the right-associated form `simp` normalises to. -/
theorem symm_trans_cancel (e : A ≃ₐ[R] B) (f : B ≃ₐ[R] C) : e.symm.trans (e.trans f) = f := by
  rw [← trans_assoc', AlgEquiv.symm_trans_self, refl_trans']

end AlgEquiv

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-! ### The two bridges -/

/-- **The `x`-side graph chart bridge** `ψˣ : A{1/x} ≃ₐ[R] A[x⁻¹]^∧`: the ideal-convention bridge
`annulusFibreChartBridgeX` followed by the chart-domain identification. -/
def graphChartAlgX :
    awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q) ≃ₐ[R]
      annulusOverlap R I q :=
  (annulusFibreChartBridgeX R I q).trans (annulusChartOverlapAlgX R I q)

/-- **The `y`-side graph chart bridge** `ψʸ : A{1/y} ≃ₐ[R] A[x⁻¹]^∧`: the `y`-side ideal-convention
bridge and chart-domain identification, followed by the inverse of the 𝔾m-inversion
`A[x⁻¹]^∧ ≃ A[y⁻¹]^∧`. -/
def graphChartAlgY (hI : I.FG) :
    awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q) ≃ₐ[R]
      annulusOverlap R I q :=
  ((annulusFibreChartBridgeY R I q).trans (annulusChartOverlapAlgY R I q)).trans
    (annulusOverlapInversionAlg R I q hI).symm

/-- **The 𝔾m-inversion chart transition intertwines the two bridges**: `τ⁻¹ ≫ ψʸ = ψˣ`. Both sides
are composites of the same four `AlgEquiv`s; the two chart-domain transports and the inversion
cancel in pairs. -/
theorem annulusFibreChartTransitionInvAlg_trans_graphChartAlgY (hI : I.FG) :
    (annulusFibreChartTransitionInvAlg R I q hI).trans (graphChartAlgY R I q hI) =
      graphChartAlgX R I q := by
  rw [graphChartAlgY, graphChartAlgX, annulusFibreChartTransitionInvAlg,
    annulusChartTransitionInvAlg]
  simp only [AlgEquiv.trans_assoc', AlgEquiv.symm_trans_cancel, AlgEquiv.self_trans_symm,
    AlgEquiv.trans_refl']

/-! ### The bridges on the structural map of `A` -/

/-- The `y`-side ideal-convention bridge intertwines the two structural completion maps
(`y`-analogue of `bridgeX_comp_awayCompletionHom`). -/
theorem bridgeY_comp_awayCompletionHom :
    (annulusFibreChartBridgeY R I q).toRingHom.comp
        (awayCompletionHom (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)) =
      awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q) := by
  simp only [awayCompletionHom, annulusFibreChartBridgeY,
    AdicCompletion.congrIdealₐ_toRingHom]
  rw [← RingHom.comp_assoc, AdicCompletion.congrIdeal_toRingHom_comp_algebraMap]

/-- The `x`-side chart-domain identification carries the structural map of `A` to the structural map
into `A[x⁻¹]^∧`. -/
theorem chartOverlapAlgX_comp_awayCompletionHom :
    (annulusChartOverlapAlgX R I q).toRingHom.comp
        (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapX R I q)) =
      algebraMap (annulusAlgebra R I q) (annulusOverlap R I q) := by
  rw [annulusChartOverlapAlgX, AdicCompletion.congrIdealₐ_toRingHom, awayCompletionHom,
    ← RingHom.comp_assoc, AdicCompletion.congrIdeal_toRingHom_comp_algebraMap]
  exact (IsScalarTower.algebraMap_eq (annulusAlgebra R I q) (annulusLoc R I q)
    (annulusOverlap R I q)).symm

/-- The `y`-analogue of `chartOverlapAlgX_comp_awayCompletionHom`. -/
theorem chartOverlapAlgY_comp_awayCompletionHom :
    (annulusChartOverlapAlgY R I q).toRingHom.comp
        (awayCompletionHom (annulusIdealOfDefinition R I q) (overlapY R I q)) =
      algebraMap (annulusAlgebra R I q) (annulusOverlapY R I q) := by
  rw [annulusChartOverlapAlgY, AdicCompletion.congrIdealₐ_toRingHom, awayCompletionHom,
    ← RingHom.comp_assoc, AdicCompletion.congrIdeal_toRingHom_comp_algebraMap]
  exact (IsScalarTower.algebraMap_eq (annulusAlgebra R I q) (annulusLocY R I q)
    (annulusOverlapY R I q)).symm

/-- **The `x`-side bridge computes the structural map**: `ψˣ ∘ (A → A{1/x}) = (A → A[x⁻¹]^∧)`. -/
theorem graphChartAlgX_comp_awayCompletionHom :
    (graphChartAlgX R I q).toRingHom.comp
        (awayCompletionHom (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)) =
      algebraMap (annulusAlgebra R I q) (annulusOverlap R I q) := by
  rw [graphChartAlgX, algEquiv_trans_toRingHom, RingHom.comp_assoc,
    bridgeX_comp_awayCompletionHom, chartOverlapAlgX_comp_awayCompletionHom]

/-- The inverse 𝔾m-inversion carries the structural map of `A` into `A[y⁻¹]^∧` to the `x`-side
inversion of the structural map precomposed with the coordinate swap. -/
theorem inversionAlg_symm_comp_algebraMap (hI : I.FG) :
    (annulusOverlapInversionAlg R I q hI).symm.toRingHom.comp
        (algebraMap (annulusAlgebra R I q) (annulusOverlapY R I q)) =
      (annulusOverlapInvX R I q hI).toRingHom.comp
        ((algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)).comp
          (annulusFlipHom R I q hI).toRingHom) := by
  refine RingHom.ext fun a => ?_
  simp only [RingHom.comp_apply]
  refine (AlgEquiv.symm_apply_eq _).mpr ?_
  change algebraMap (annulusAlgebra R I q) (annulusOverlapY R I q) a =
    annulusOverlapInversion R I q hI
      (annulusOverlapInvX R I q hI
        (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)
          (annulusFlipHom R I q hI a)))
  rw [annulusOverlapInversion_annulusOverlapInvX, annulusOverlapTransition_algebraMap_annulus,
    annulusFlip_apply, ← AlgHom.comp_apply, annulusFlipHom_annulusFlipHom, AlgHom.id_apply]

/-- **The `y`-side bridge computes the structural map**: `ψʸ ∘ (A → A{1/y}) = invˣ ∘ (A → A[x⁻¹]^∧)
∘ flip`. -/
theorem graphChartAlgY_comp_awayCompletionHom (hI : I.FG) :
    (graphChartAlgY R I q hI).toRingHom.comp
        (awayCompletionHom (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)) =
      (annulusOverlapInvX R I q hI).toRingHom.comp
        ((algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)).comp
          (annulusFlipHom R I q hI).toRingHom) := by
  rw [graphChartAlgY, algEquiv_trans_toRingHom, algEquiv_trans_toRingHom, RingHom.comp_assoc,
    RingHom.comp_assoc, bridgeY_comp_awayCompletionHom, chartOverlapAlgY_comp_awayCompletionHom,
    inversionAlg_symm_comp_algebraMap]

/-! ### Pointwise forms of the bridge computations -/

theorem graphChartAlgX_algebraMap (a : annulusAlgebra R I q) :
    graphChartAlgX R I q
        (algebraMap (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)) a) =
      algebraMap (annulusAlgebra R I q) (annulusOverlap R I q) a := by
  have h := RingHom.congr_fun (graphChartAlgX_comp_awayCompletionHom R I q) a
  rwa [RingHom.comp_apply, FormalSpectrum.awayCompletionHom_eq_algebraMap] at h

theorem graphChartAlgY_algebraMap (hI : I.FG) (a : annulusAlgebra R I q) :
    graphChartAlgY R I q hI
        (algebraMap (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)) a) =
      annulusOverlapInvX R I q hI
        (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)
          (annulusFlipHom R I q hI a)) := by
  have h := RingHom.congr_fun (graphChartAlgY_comp_awayCompletionHom R I q hI) a
  rwa [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply,
    FormalSpectrum.awayCompletionHom_eq_algebraMap] at h

theorem graphChartAlgY_comp_transitionInv (hI : I.FG) :
    (graphChartAlgY R I q hI).toRingHom.comp
        (annulusFibreChartTransitionInvAlg R I q hI).toRingHom =
      (graphChartAlgX R I q).toRingHom := by
  rw [← algEquiv_trans_toRingHom, annulusFibreChartTransitionInvAlg_trans_graphChartAlgY]

theorem graphChartAlgY_transition_apply (hI : I.FG)
    (z : awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)) :
    graphChartAlgY R I q hI (annulusFibreChartTransitionInvAlg R I q hI z) =
      graphChartAlgX R I q z := by
  have h := RingHom.congr_fun (graphChartAlgY_comp_transitionInv R I q hI) z
  rwa [RingHom.comp_apply] at h

variable [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R]

/-- The `x`-side graph lift `A ⊗̂_R A{1/y} →+* A[x⁻¹]^∧`. -/
def graphLiftX (hI : I.FG) :
    CompletedTensorProduct R I (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)) →+*
      annulusOverlap R I q :=
  haveI : IsAdicComplete (annulusOverlapIdeal R I q) (annulusOverlap R I q) :=
    (annulusOverlap_isAdicRing R I q hI).toIsAdicComplete
  CompletedTensorProduct.lift (annulusOverlapIdeal R I q)
    (le_of_eq (overlapIdeal_eq_map R I q).symm)
    (IsScalarTower.toAlgHom R (annulusAlgebra R I q) (annulusOverlap R I q))
    (graphChartAlgY R I q hI).toAlgHom

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
theorem graphLiftX_inl (hI : I.FG) (a : annulusAlgebra R I q) :
    graphLiftX R I q hI (inl R I _ _ a) =
      algebraMap (annulusAlgebra R I q) (annulusOverlap R I q) a := by
  haveI : IsAdicComplete (annulusOverlapIdeal R I q) (annulusOverlap R I q) :=
    (annulusOverlap_isAdicRing R I q hI).toIsAdicComplete
  rw [graphLiftX, lift_inl]
  rfl

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
theorem graphLiftX_inr (hI : I.FG)
    (z : awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)) :
    graphLiftX R I q hI (inr R I _ _ z) = graphChartAlgY R I q hI z := by
  haveI : IsAdicComplete (annulusOverlapIdeal R I q) (annulusOverlap R I q) :=
    (annulusOverlap_isAdicRing R I q hI).toIsAdicComplete
  rw [graphLiftX, lift_inr]
  rfl

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
theorem graphLiftX_mem_pow (hI : I.FG) (m : ℕ)
    {x : CompletedTensorProduct R I (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))}
    (hx : x ∈ (idealOfDefinition R I (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))) ^ m) :
    graphLiftX R I q hI x ∈ (annulusOverlapIdeal R I q) ^ m := by
  haveI : IsAdicComplete (annulusOverlapIdeal R I q) (annulusOverlap R I q) :=
    (annulusOverlap_isAdicRing R I q hI).toIsAdicComplete
  exact lift_mem_pow _ _ _ _ hI m hx

/-! ### The two ring identities -/

set_option linter.unusedSectionVars false in
theorem graphLiftX_comp_map (hI : I.FG) :
    (graphLiftX R I q hI).comp
        (map hI (AlgHom.id R (annulusAlgebra R I q))
          (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))) =
      graphCodiagX R I q hI := by
  haveI : IsAdicComplete (annulusOverlapIdeal R I q) (annulusOverlap R I q) :=
    (annulusOverlap_isAdicRing R I q hI).toIsAdicComplete
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicComplete (I.map (algebraMap R (annulusAlgebra R I q))) (annulusAlgebra R I q) :=
    (annulus_isAdicRing_map R I q hI).toIsAdicComplete
  refine hom_ext (annulusOverlapIdeal R I q) hI (fun m x hx => ?_) (fun m x hx => ?_)
    (fun a => ?_) (fun b => ?_)
  · exact graphLiftX_mem_pow R I q hI m (map_mem_pow hI _ _ m hx)
  · rw [graphCodiagX, RingHom.comp_apply, localizedCodiagInvX]
    exact lift_mem_pow _ _ _ _ hI m (map_mem_pow hI _ _ m hx)
  · rw [RingHom.comp_apply, map_inl, AlgHom.id_apply, graphLiftX_inl, graphCodiagX_inl]
    rfl
  · rw [RingHom.comp_apply, map_inr, graphLiftX_inr, IsScalarTower.coe_toAlgHom',
      graphChartAlgY_algebraMap, graphCodiagX_inr]
    rfl

theorem graphLiftX_comp_map_transition (hI : I.FG) :
    haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
      annulus_isAdicRing_map R I q hI
    ((graphLiftX R I q hI).comp
        (map hI (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).toAlgHom
          (annulusFibreChartTransitionInvAlg R I q hI).toAlgHom)).comp
      (map hI (AlgHom.id R (annulusAlgebra R I q))
        (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))) =
      (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)).comp
        (codiagonal R I (annulusAlgebra R I q)) := by
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicComplete (annulusOverlapIdeal R I q) (annulusOverlap R I q) :=
    (annulusOverlap_isAdicRing R I q hI).toIsAdicComplete
  haveI : IsAdicComplete (I.map (algebraMap R (annulusAlgebra R I q))) (annulusAlgebra R I q) :=
    (annulus_isAdicRing_map R I q hI).toIsAdicComplete
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  have hid : (I.map (algebraMap R (annulusAlgebra R I q))).map
      (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)) = annulusOverlapIdeal R I q := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R (annulusAlgebra R I q)
      (annulusOverlap R I q), overlapIdeal_eq_map]
  refine hom_ext (annulusOverlapIdeal R I q) hI (fun m x hx => ?_) (fun m x hx => ?_)
    (fun a => ?_) (fun b => ?_)
  · exact graphLiftX_mem_pow R I q hI m (map_mem_pow hI _ _ m (map_mem_pow hI _ _ m hx))
  · have h1 : codiagonal R I (annulusAlgebra R I q) x ∈
        (I.map (algebraMap R (annulusAlgebra R I q))) ^ m :=
      lift_mem_pow _ (le_refl _) (AlgHom.id R _) (AlgHom.id R _) hI m hx
    have h2 : ((I.map (algebraMap R (annulusAlgebra R I q))) ^ m).map
        (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)) =
        (annulusOverlapIdeal R I q) ^ m := by rw [Ideal.map_pow, hid]
    exact h2.le (Ideal.mem_map_of_mem _ h1)
  · rw [RingHom.comp_apply, RingHom.comp_apply, map_inl, AlgHom.id_apply, map_inl,
      graphLiftX_inl, RingHom.comp_apply, codiagonal_inl]
    rfl
  · rw [RingHom.comp_apply, RingHom.comp_apply, map_inr, map_inr, graphLiftX_inr]
    simp only [AlgEquiv.coe_toAlgHom, IsScalarTower.coe_toAlgHom']
    rw [graphChartAlgY_transition_apply, graphChartAlgX_algebraMap, RingHom.comp_apply,
      codiagonal_inr]


/-! ### The plain `y`-chart bridge and the `y`-side lifts -/

/-- **The plain `y`-side chart bridge** `A{1/y} ≃ₐ[R] A[y⁻¹]^∧` (no inversion twist). -/
def chartBridgeY :
    awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q) ≃ₐ[R]
      annulusOverlapY R I q :=
  (annulusFibreChartBridgeY R I q).trans (annulusChartOverlapAlgY R I q)

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
theorem chartBridgeY_comp_awayCompletionHom :
    (chartBridgeY R I q).toRingHom.comp
        (awayCompletionHom (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)) =
      algebraMap (annulusAlgebra R I q) (annulusOverlapY R I q) := by
  rw [chartBridgeY, algEquiv_trans_toRingHom, RingHom.comp_assoc,
    bridgeY_comp_awayCompletionHom, chartOverlapAlgY_comp_awayCompletionHom]

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
theorem chartBridgeY_algebraMap (a : annulusAlgebra R I q) :
    chartBridgeY R I q
        (algebraMap (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)) a) =
      algebraMap (annulusAlgebra R I q) (annulusOverlapY R I q) a := by
  have h := RingHom.congr_fun (chartBridgeY_comp_awayCompletionHom R I q) a
  rwa [RingHom.comp_apply, FormalSpectrum.awayCompletionHom_eq_algebraMap] at h

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
/-- **The 𝔾m-inversion chart transition, read through the plain bridges**: `τ⁻¹ ≫ ψʸ_plain`
is `ψˣ` followed by the inversion. -/
theorem annulusFibreChartTransitionInvAlg_trans_chartBridgeY (hI : I.FG) :
    (annulusFibreChartTransitionInvAlg R I q hI).trans (chartBridgeY R I q) =
      (graphChartAlgX R I q).trans (annulusOverlapInversionAlg R I q hI) := by
  rw [chartBridgeY, graphChartAlgX, annulusFibreChartTransitionInvAlg,
    annulusChartTransitionInvAlg]
  simp only [AlgEquiv.trans_assoc', AlgEquiv.symm_trans_cancel, AlgEquiv.symm_trans_self,
    AlgEquiv.trans_refl']

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
theorem chartBridgeY_comp_transitionInv (hI : I.FG) :
    (chartBridgeY R I q).toRingHom.comp
        (annulusFibreChartTransitionInvAlg R I q hI).toRingHom =
      (annulusOverlapInversionAlg R I q hI).toRingHom.comp (graphChartAlgX R I q).toRingHom := by
  rw [← algEquiv_trans_toRingHom, ← algEquiv_trans_toRingHom,
    annulusFibreChartTransitionInvAlg_trans_chartBridgeY]

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
theorem chartBridgeY_transition_apply (hI : I.FG)
    (z : awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)) :
    chartBridgeY R I q (annulusFibreChartTransitionInvAlg R I q hI z) =
      annulusOverlapInversion R I q hI (graphChartAlgX R I q z) := by
  have h := RingHom.congr_fun (chartBridgeY_comp_transitionInv R I q hI) z
  rwa [RingHom.comp_apply, RingHom.comp_apply] at h

/-! ### The three remaining graph lifts -/

/-- `A →ₐ[R] A[y⁻¹]^∧`, the structural map of `A` into the `x`-overlap followed by the
𝔾m-inversion: the coordinate map of the partner point of the gluing. -/
def invLocXY (hI : I.FG) : annulusAlgebra R I q →ₐ[R] annulusOverlapY R I q :=
  (annulusOverlapInversionAlg R I q hI).toAlgHom.comp
    (IsScalarTower.toAlgHom R (annulusAlgebra R I q) (annulusOverlap R I q))

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
@[simp] theorem invLocXY_apply (hI : I.FG) (a : annulusAlgebra R I q) :
    invLocXY R I q hI a =
      annulusOverlapInversion R I q hI
        (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q) a) := rfl

/-- The `y`-side graph lift `A{1/y} ⊗̂_R A →+* A[y⁻¹]^∧`. -/
def graphLiftY (hI : I.FG) :
    CompletedTensorProduct R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
        (annulusAlgebra R I q) →+* annulusOverlapY R I q :=
  haveI : IsAdicComplete (annulusOverlapIdealY R I q) (annulusOverlapY R I q) :=
    (annulusOverlapY_isAdicRing R I q hI).toIsAdicComplete
  CompletedTensorProduct.lift (annulusOverlapIdealY R I q)
    (le_of_eq (overlapIdealY_eq_map R I q).symm)
    (chartBridgeY R I q).toAlgHom (invLocXY R I q hI)

/-- The mixed graph lift `A{1/y} ⊗̂_R A →+* A[x⁻¹]^∧` (first factor localized). -/
def graphLiftXY (hI : I.FG) :
    CompletedTensorProduct R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
        (annulusAlgebra R I q) →+* annulusOverlap R I q :=
  haveI : IsAdicComplete (annulusOverlapIdeal R I q) (annulusOverlap R I q) :=
    (annulusOverlap_isAdicRing R I q hI).toIsAdicComplete
  CompletedTensorProduct.lift (annulusOverlapIdeal R I q)
    (le_of_eq (overlapIdeal_eq_map R I q).symm)
    (graphChartAlgY R I q hI).toAlgHom
    (IsScalarTower.toAlgHom R (annulusAlgebra R I q) (annulusOverlap R I q))

/-- The mixed graph lift `A ⊗̂_R A{1/y} →+* A[y⁻¹]^∧` (second factor localized). -/
def graphLiftYX (hI : I.FG) :
    CompletedTensorProduct R I (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)) →+*
      annulusOverlapY R I q :=
  haveI : IsAdicComplete (annulusOverlapIdealY R I q) (annulusOverlapY R I q) :=
    (annulusOverlapY_isAdicRing R I q hI).toIsAdicComplete
  CompletedTensorProduct.lift (annulusOverlapIdealY R I q)
    (le_of_eq (overlapIdealY_eq_map R I q).symm)
    (invLocXY R I q hI) (chartBridgeY R I q).toAlgHom

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
theorem graphLiftY_mem_pow (hI : I.FG) (m : ℕ)
    {x : CompletedTensorProduct R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
      (annulusAlgebra R I q)}
    (hx : x ∈ (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
      (annulusAlgebra R I q)) ^ m) :
    graphLiftY R I q hI x ∈ (annulusOverlapIdealY R I q) ^ m := by
  haveI : IsAdicComplete (annulusOverlapIdealY R I q) (annulusOverlapY R I q) :=
    (annulusOverlapY_isAdicRing R I q hI).toIsAdicComplete
  exact lift_mem_pow _ _ _ _ hI m hx

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
theorem graphLiftXY_mem_pow (hI : I.FG) (m : ℕ)
    {x : CompletedTensorProduct R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
      (annulusAlgebra R I q)}
    (hx : x ∈ (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
      (annulusAlgebra R I q)) ^ m) :
    graphLiftXY R I q hI x ∈ (annulusOverlapIdeal R I q) ^ m := by
  haveI : IsAdicComplete (annulusOverlapIdeal R I q) (annulusOverlap R I q) :=
    (annulusOverlap_isAdicRing R I q hI).toIsAdicComplete
  exact lift_mem_pow _ _ _ _ hI m hx

omit [TopologicalSpace R] [IsAdicRing I] [IsNoetherianRing R] in
theorem graphLiftYX_mem_pow (hI : I.FG) (m : ℕ)
    {x : CompletedTensorProduct R I (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))}
    (hx : x ∈ (idealOfDefinition R I (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))) ^ m) :
    graphLiftYX R I q hI x ∈ (annulusOverlapIdealY R I q) ^ m := by
  haveI : IsAdicComplete (annulusOverlapIdealY R I q) (annulusOverlapY R I q) :=
    (annulusOverlapY_isAdicRing R I q hI).toIsAdicComplete
  exact lift_mem_pow _ _ _ _ hI m hx

/-! ### The `(A)` and `(B)` identities of the three remaining lifts -/

set_option linter.unusedSectionVars false in
theorem graphLiftY_comp_map (hI : I.FG) :
    (graphLiftY R I q hI).comp
        (map hI
          (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))
          (AlgHom.id R (annulusAlgebra R I q))) =
      graphCodiagY R I q hI := by
  haveI : IsAdicComplete (annulusOverlapIdeal R I q) (annulusOverlap R I q) :=
    (annulusOverlap_isAdicRing R I q hI).toIsAdicComplete
  haveI : IsAdicComplete (annulusOverlapIdealY R I q) (annulusOverlapY R I q) :=
    (annulusOverlapY_isAdicRing R I q hI).toIsAdicComplete
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicComplete (I.map (algebraMap R (annulusAlgebra R I q))) (annulusAlgebra R I q) :=
    (annulus_isAdicRing_map R I q hI).toIsAdicComplete
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  refine hom_ext (annulusOverlapIdealY R I q) hI (fun m x hx => ?_) (fun m x hx => ?_)
    (fun a => ?_) (fun b => ?_)
  · exact graphLiftY_mem_pow R I q hI m (map_mem_pow hI _ _ m hx)
  · rw [graphCodiagY, RingHom.comp_apply, RingHom.comp_apply]
    have h1 : commHom (R := R) (I := I) (A := annulusAlgebra R I q)
        (B := annulusAlgebra R I q) hI x ∈
        (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) ^ m := by
      rw [commHom]
      exact lift_mem_pow _ _ _ _ hI m hx
    have h2 : graphCodiagX R I q hI (commHom (R := R) (I := I) (A := annulusAlgebra R I q)
        (B := annulusAlgebra R I q) hI x) ∈ (annulusOverlapIdeal R I q) ^ m := by
      rw [graphCodiagX, RingHom.comp_apply, localizedCodiagInvX]
      exact lift_mem_pow _ _ _ _ hI m (map_mem_pow hI _ _ m h1)
    have h3 : ((annulusOverlapIdeal R I q) ^ m).map
        (annulusOverlapInversion R I q hI : annulusOverlap R I q →+* annulusOverlapY R I q) =
        (annulusOverlapIdealY R I q) ^ m := by
      rw [Ideal.map_pow, map_annulusOverlapInversion_annulusOverlapIdeal]
    exact h3.le (Ideal.mem_map_of_mem _ h2)
  · rw [RingHom.comp_apply, map_inl, graphLiftY, lift_inl, IsScalarTower.coe_toAlgHom',
      AlgEquiv.coe_toAlgHom, chartBridgeY_algebraMap, graphCodiagY_inl]
    rfl
  · rw [RingHom.comp_apply, map_inr, AlgHom.id_apply, graphLiftY, lift_inr, invLocXY_apply,
      graphCodiagY_inr]
    rfl

set_option linter.unusedSectionVars false in
theorem graphLiftY_comp_map_transition (hI : I.FG) :
    haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
      annulus_isAdicRing_map R I q hI
    ((graphLiftY R I q hI).comp
        (map hI (annulusFibreChartTransitionInvAlg R I q hI).toAlgHom
          (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).toAlgHom)).comp
      (map hI
        (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))
        (AlgHom.id R (annulusAlgebra R I q))) =
      (invLocXY R I q hI).toRingHom.comp (codiagonal R I (annulusAlgebra R I q)) := by
  haveI : IsAdicComplete (annulusOverlapIdeal R I q) (annulusOverlap R I q) :=
    (annulusOverlap_isAdicRing R I q hI).toIsAdicComplete
  haveI : IsAdicComplete (annulusOverlapIdealY R I q) (annulusOverlapY R I q) :=
    (annulusOverlapY_isAdicRing R I q hI).toIsAdicComplete
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicComplete (I.map (algebraMap R (annulusAlgebra R I q))) (annulusAlgebra R I q) :=
    (annulus_isAdicRing_map R I q hI).toIsAdicComplete
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  have h0 : (invLocXY R I q hI).toRingHom =
      ((annulusOverlapInversion R I q hI : annulusOverlap R I q →+* annulusOverlapY R I q)).comp
        (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)) := rfl
  have h1 : (I.map (algebraMap R (annulusAlgebra R I q))).map
      (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)) = annulusOverlapIdeal R I q := by
    rw [Ideal.map_map,
      ← IsScalarTower.algebraMap_eq R (annulusAlgebra R I q) (annulusOverlap R I q),
      overlapIdeal_eq_map]
  have hid : (I.map (algebraMap R (annulusAlgebra R I q))).map
      (invLocXY R I q hI).toRingHom = annulusOverlapIdealY R I q := by
    rw [h0, ← Ideal.map_map, h1, map_annulusOverlapInversion_annulusOverlapIdeal]
  refine hom_ext (annulusOverlapIdealY R I q) hI (fun m x hx => ?_) (fun m x hx => ?_)
    (fun a => ?_) (fun b => ?_)
  · exact graphLiftY_mem_pow R I q hI m (map_mem_pow hI _ _ m (map_mem_pow hI _ _ m hx))
  · have h1 : codiagonal R I (annulusAlgebra R I q) x ∈
        (I.map (algebraMap R (annulusAlgebra R I q))) ^ m :=
      lift_mem_pow _ (le_refl _) (AlgHom.id R _) (AlgHom.id R _) hI m hx
    have h2 : ((I.map (algebraMap R (annulusAlgebra R I q))) ^ m).map
        (invLocXY R I q hI).toRingHom = (annulusOverlapIdealY R I q) ^ m := by
      rw [Ideal.map_pow, hid]
    exact h2.le (Ideal.mem_map_of_mem _ h1)
  · rw [RingHom.comp_apply, RingHom.comp_apply, map_inl, map_inl, graphLiftY, lift_inl]
    simp only [AlgEquiv.coe_toAlgHom, IsScalarTower.coe_toAlgHom']
    rw [chartBridgeY_transition_apply, graphChartAlgX_algebraMap, RingHom.comp_apply,
      codiagonal_inl]
    rfl
  · rw [RingHom.comp_apply, RingHom.comp_apply, map_inr, map_inr, AlgHom.id_apply, graphLiftY,
      lift_inr, RingHom.comp_apply, codiagonal_inr]
    rfl

set_option linter.unusedSectionVars false in
theorem graphLiftXY_comp_map (hI : I.FG) :
    (graphLiftXY R I q hI).comp
        (map hI
          (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))
          (AlgHom.id R (annulusAlgebra R I q))) =
      (graphCodiagX R I q hI).comp
        (commHom (R := R) (I := I) (A := annulusAlgebra R I q)
          (B := annulusAlgebra R I q) hI) := by
  haveI : IsAdicComplete (annulusOverlapIdeal R I q) (annulusOverlap R I q) :=
    (annulusOverlap_isAdicRing R I q hI).toIsAdicComplete
  haveI : IsAdicComplete (annulusOverlapIdealY R I q) (annulusOverlapY R I q) :=
    (annulusOverlapY_isAdicRing R I q hI).toIsAdicComplete
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicComplete (I.map (algebraMap R (annulusAlgebra R I q))) (annulusAlgebra R I q) :=
    (annulus_isAdicRing_map R I q hI).toIsAdicComplete
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  have hcod : ∀ (m : ℕ) (z : CompletedTensorProduct R I (annulusAlgebra R I q)
      (annulusAlgebra R I q)), z ∈ (idealOfDefinition R I (annulusAlgebra R I q)
        (annulusAlgebra R I q)) ^ m →
      graphCodiagX R I q hI z ∈ (annulusOverlapIdeal R I q) ^ m := by
    intro m z hz
    rw [graphCodiagX, RingHom.comp_apply, localizedCodiagInvX]
    exact lift_mem_pow _ _ _ _ hI m (map_mem_pow hI _ _ m hz)
  have hcomm : ∀ (m : ℕ) (z : CompletedTensorProduct R I (annulusAlgebra R I q)
      (annulusAlgebra R I q)), z ∈ (idealOfDefinition R I (annulusAlgebra R I q)
        (annulusAlgebra R I q)) ^ m →
      commHom (R := R) (I := I) (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) hI z ∈
        (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) ^ m := by
    intro m z hz
    rw [commHom]
    exact lift_mem_pow _ _ _ _ hI m hz
  refine hom_ext (annulusOverlapIdeal R I q) hI (fun m x hx => ?_) (fun m x hx => ?_)
    (fun a => ?_) (fun b => ?_)
  · exact graphLiftXY_mem_pow R I q hI m (map_mem_pow hI _ _ m hx)
  · rw [RingHom.comp_apply]
    exact hcod m _ (hcomm m x hx)
  · rw [RingHom.comp_apply, map_inl, graphLiftXY, lift_inl, IsScalarTower.coe_toAlgHom',
      AlgEquiv.coe_toAlgHom, graphChartAlgY_algebraMap, RingHom.comp_apply, commHom_inl,
      graphCodiagX_inr]
    rfl
  · rw [RingHom.comp_apply, map_inr, AlgHom.id_apply, graphLiftXY, lift_inr, RingHom.comp_apply,
      commHom_inr, graphCodiagX_inl]

set_option linter.unusedSectionVars false in
theorem graphLiftXY_comp_map_transition (hI : I.FG) :
    haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
      annulus_isAdicRing_map R I q hI
    ((graphLiftXY R I q hI).comp
        (map hI (annulusFibreChartTransitionInvAlg R I q hI).toAlgHom
          (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).toAlgHom)).comp
      (map hI
        (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))
        (AlgHom.id R (annulusAlgebra R I q))) =
      (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)).comp
        (codiagonal R I (annulusAlgebra R I q)) := by
  haveI : IsAdicComplete (annulusOverlapIdeal R I q) (annulusOverlap R I q) :=
    (annulusOverlap_isAdicRing R I q hI).toIsAdicComplete
  haveI : IsAdicComplete (annulusOverlapIdealY R I q) (annulusOverlapY R I q) :=
    (annulusOverlapY_isAdicRing R I q hI).toIsAdicComplete
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicComplete (I.map (algebraMap R (annulusAlgebra R I q))) (annulusAlgebra R I q) :=
    (annulus_isAdicRing_map R I q hI).toIsAdicComplete
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  have h1 : (I.map (algebraMap R (annulusAlgebra R I q))).map
      (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)) = annulusOverlapIdeal R I q := by
    rw [Ideal.map_map,
      ← IsScalarTower.algebraMap_eq R (annulusAlgebra R I q) (annulusOverlap R I q),
      overlapIdeal_eq_map]
  refine hom_ext (annulusOverlapIdeal R I q) hI (fun m x hx => ?_) (fun m x hx => ?_)
    (fun a => ?_) (fun b => ?_)
  · exact graphLiftXY_mem_pow R I q hI m (map_mem_pow hI _ _ m (map_mem_pow hI _ _ m hx))
  · have hc : codiagonal R I (annulusAlgebra R I q) x ∈
        (I.map (algebraMap R (annulusAlgebra R I q))) ^ m :=
      lift_mem_pow _ (le_refl _) (AlgHom.id R _) (AlgHom.id R _) hI m hx
    have h2 : ((I.map (algebraMap R (annulusAlgebra R I q))) ^ m).map
        (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)) =
        (annulusOverlapIdeal R I q) ^ m := by rw [Ideal.map_pow, h1]
    exact h2.le (Ideal.mem_map_of_mem _ hc)
  · rw [RingHom.comp_apply, RingHom.comp_apply, map_inl, map_inl, graphLiftXY, lift_inl]
    simp only [AlgEquiv.coe_toAlgHom, IsScalarTower.coe_toAlgHom']
    rw [graphChartAlgY_transition_apply, graphChartAlgX_algebraMap, RingHom.comp_apply,
      codiagonal_inl]
  · rw [RingHom.comp_apply, RingHom.comp_apply, map_inr, map_inr, AlgHom.id_apply, graphLiftXY,
      lift_inr, RingHom.comp_apply, codiagonal_inr]
    rfl

set_option linter.unusedSectionVars false in
theorem graphLiftYX_comp_map (hI : I.FG) :
    (graphLiftYX R I q hI).comp
        (map hI (AlgHom.id R (annulusAlgebra R I q))
          (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))) =
      (graphCodiagY R I q hI).comp
        (commHom (R := R) (I := I) (A := annulusAlgebra R I q)
          (B := annulusAlgebra R I q) hI) := by
  haveI : IsAdicComplete (annulusOverlapIdeal R I q) (annulusOverlap R I q) :=
    (annulusOverlap_isAdicRing R I q hI).toIsAdicComplete
  haveI : IsAdicComplete (annulusOverlapIdealY R I q) (annulusOverlapY R I q) :=
    (annulusOverlapY_isAdicRing R I q hI).toIsAdicComplete
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicComplete (I.map (algebraMap R (annulusAlgebra R I q))) (annulusAlgebra R I q) :=
    (annulus_isAdicRing_map R I q hI).toIsAdicComplete
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  have hcod : ∀ (m : ℕ) (z : CompletedTensorProduct R I (annulusAlgebra R I q)
      (annulusAlgebra R I q)), z ∈ (idealOfDefinition R I (annulusAlgebra R I q)
        (annulusAlgebra R I q)) ^ m →
      graphCodiagX R I q hI z ∈ (annulusOverlapIdeal R I q) ^ m := by
    intro m z hz
    rw [graphCodiagX, RingHom.comp_apply, localizedCodiagInvX]
    exact lift_mem_pow _ _ _ _ hI m (map_mem_pow hI _ _ m hz)
  have hcomm : ∀ (m : ℕ) (z : CompletedTensorProduct R I (annulusAlgebra R I q)
      (annulusAlgebra R I q)), z ∈ (idealOfDefinition R I (annulusAlgebra R I q)
        (annulusAlgebra R I q)) ^ m →
      commHom (R := R) (I := I) (A := annulusAlgebra R I q) (B := annulusAlgebra R I q) hI z ∈
        (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) ^ m := by
    intro m z hz
    rw [commHom]
    exact lift_mem_pow _ _ _ _ hI m hz
  have h3 : ∀ m : ℕ, ((annulusOverlapIdeal R I q) ^ m).map
      (annulusOverlapInversion R I q hI : annulusOverlap R I q →+* annulusOverlapY R I q) =
      (annulusOverlapIdealY R I q) ^ m := by
    intro m
    rw [Ideal.map_pow, map_annulusOverlapInversion_annulusOverlapIdeal]
  refine hom_ext (annulusOverlapIdealY R I q) hI (fun m x hx => ?_) (fun m x hx => ?_)
    (fun a => ?_) (fun b => ?_)
  · exact graphLiftYX_mem_pow R I q hI m (map_mem_pow hI _ _ m hx)
  · rw [RingHom.comp_apply, graphCodiagY, RingHom.comp_apply, RingHom.comp_apply]
    exact (h3 m).le (Ideal.mem_map_of_mem _ (hcod m _ (hcomm m _ (hcomm m x hx))))
  · rw [RingHom.comp_apply, map_inl, AlgHom.id_apply, graphLiftYX, lift_inl, invLocXY_apply,
      RingHom.comp_apply, commHom_inl, graphCodiagY_inr]
    rfl
  · rw [RingHom.comp_apply, map_inr, graphLiftYX, lift_inr, IsScalarTower.coe_toAlgHom',
      AlgEquiv.coe_toAlgHom, chartBridgeY_algebraMap, RingHom.comp_apply, commHom_inr,
      graphCodiagY_inl]
    rfl

set_option linter.unusedSectionVars false in
theorem graphLiftYX_comp_map_transition (hI : I.FG) :
    haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
      annulus_isAdicRing_map R I q hI
    ((graphLiftYX R I q hI).comp
        (map hI (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).toAlgHom
          (annulusFibreChartTransitionInvAlg R I q hI).toAlgHom)).comp
      (map hI (AlgHom.id R (annulusAlgebra R I q))
        (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))) =
      (invLocXY R I q hI).toRingHom.comp (codiagonal R I (annulusAlgebra R I q)) := by
  haveI : IsAdicComplete (annulusOverlapIdeal R I q) (annulusOverlap R I q) :=
    (annulusOverlap_isAdicRing R I q hI).toIsAdicComplete
  haveI : IsAdicComplete (annulusOverlapIdealY R I q) (annulusOverlapY R I q) :=
    (annulusOverlapY_isAdicRing R I q hI).toIsAdicComplete
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicComplete (I.map (algebraMap R (annulusAlgebra R I q))) (annulusAlgebra R I q) :=
    (annulus_isAdicRing_map R I q hI).toIsAdicComplete
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  have h0 : (invLocXY R I q hI).toRingHom =
      ((annulusOverlapInversion R I q hI : annulusOverlap R I q →+* annulusOverlapY R I q)).comp
        (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)) := rfl
  have h1 : (I.map (algebraMap R (annulusAlgebra R I q))).map
      (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)) = annulusOverlapIdeal R I q := by
    rw [Ideal.map_map,
      ← IsScalarTower.algebraMap_eq R (annulusAlgebra R I q) (annulusOverlap R I q),
      overlapIdeal_eq_map]
  have hid : (I.map (algebraMap R (annulusAlgebra R I q))).map
      (invLocXY R I q hI).toRingHom = annulusOverlapIdealY R I q := by
    rw [h0, ← Ideal.map_map, h1, map_annulusOverlapInversion_annulusOverlapIdeal]
  refine hom_ext (annulusOverlapIdealY R I q) hI (fun m x hx => ?_) (fun m x hx => ?_)
    (fun a => ?_) (fun b => ?_)
  · exact graphLiftYX_mem_pow R I q hI m (map_mem_pow hI _ _ m (map_mem_pow hI _ _ m hx))
  · have hc : codiagonal R I (annulusAlgebra R I q) x ∈
        (I.map (algebraMap R (annulusAlgebra R I q))) ^ m :=
      lift_mem_pow _ (le_refl _) (AlgHom.id R _) (AlgHom.id R _) hI m hx
    have h2 : ((I.map (algebraMap R (annulusAlgebra R I q))) ^ m).map
        (invLocXY R I q hI).toRingHom = (annulusOverlapIdealY R I q) ^ m := by
      rw [Ideal.map_pow, hid]
    exact h2.le (Ideal.mem_map_of_mem _ hc)
  · rw [RingHom.comp_apply, RingHom.comp_apply, map_inl, map_inl, AlgHom.id_apply, graphLiftYX,
      lift_inl, RingHom.comp_apply, codiagonal_inl]
    rfl
  · rw [RingHom.comp_apply, RingHom.comp_apply, map_inr, map_inr, graphLiftYX, lift_inr]
    simp only [AlgEquiv.coe_toAlgHom, IsScalarTower.coe_toAlgHom']
    rw [chartBridgeY_transition_apply, graphChartAlgX_algebraMap, RingHom.comp_apply,
      codiagonal_inr]
    rfl

end AlgebraicGeometry
