import FormalSchemes.TateGraphCodiagonalFactor

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

/-!
# The graph lifts through the `x`-localized overlap summands

Fix an adic base `(R, I)` with `I` finitely generated and a Tate parameter `q ∈ I`, write
`A = annulusAlgebra R I q`, `Ω_x = A[x⁻¹]^∧`, `Ω_y = A[y⁻¹]^∧` and
`A{1/x} = awayCompletion (I·A) (overlapX)`.

Each mixed chart `(b, ¬b)` of the four-chart Tate self-fibre product meets the two *diagonal*
charts `(b, b)` and `(¬b, ¬b)` along an overlap object which is a **coproduct of two summands**,
one localized at `x` and one at `y`, and *both* summands carry graph points. The `y`-localized
four are handled by `FormalSchemes.TateGraphCodiagonalFactor`; this file supplies the four
`x`-localized mirrors, i.e. the lifts through `A ⊗̂_R A{1/x}` and `A{1/x} ⊗̂_R A`.

Only the factorization identity (`(A)` in the notation of the companion file) is proved here — the
transition compatibility `(B)` is what the reverse inclusion needs and is not used by the `⊆` half.

## Main results

Four ring maps and their factorizations through the graph codiagonals of
`FormalSchemes.GraphCodiagonalClosedEmbedding`:

* `graphLiftAXtoY`, with `graphLiftAXtoY_comp_map : … = graphCodiagY`;
* `graphLiftXAtoX`, with `graphLiftXAtoX_comp_map : … = graphCodiagX`;
* `graphLiftXAtoY`, with `graphLiftXAtoY_comp_map : … = graphCodiagY ∘ commHom`;
* `graphLiftAXtoX`, with `graphLiftAXtoX_comp_map : … = graphCodiagX ∘ commHom`;

together with their `Spf`-level forms `spfGraphLift…` and the geometric factorizations
`spfGraphCodiagY_eq_ft_dAX`, `spfGraphCodiagX_eq_ft_dXA`, `spfGraphCodiagYComm_eq_tf_dXA`,
`spfGraphCodiagXComm_eq_tf_dAX`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
-/

noncomputable section

open Ideal AlgebraicGeometry CategoryTheory CategoryTheory.Limits FormalSpectrum
  CompletedTensorProduct CompletedTensorAwayInterchange

universe u

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-! ### The `x`-side inversion as an `R`-algebra equivalence -/

/-- The `x`-side 𝔾m-inversion `A[x⁻¹]^∧ ≃+* A[x⁻¹]^∧` upgraded to an `R`-algebra equivalence;
`R`-linearity is `annulusOverlapInvX_algebraMap`. -/
def annulusOverlapInvXAlg (hI : I.FG) : annulusOverlap R I q ≃ₐ[R] annulusOverlap R I q :=
  AlgEquiv.ofRingEquiv (f := annulusOverlapInvX R I q hI)
    (fun r => annulusOverlapInvX_algebraMap R I q hI r)

/-- The `R`-algebra map `A →ₐ[R] A[x⁻¹]^∧`, `a ↦ x⁻¹-inversion of locX (flip a)`: the second leg
of the `x`-side graph codiagonal (`graphCodiagX_inr`). -/
def invFlipLocX (hI : I.FG) : annulusAlgebra R I q →ₐ[R] annulusOverlap R I q :=
  (annulusOverlapInvXAlg R I q hI).toAlgHom.comp
    ((locX R I q).comp (annulusFlipHom R I q hI))

@[simp] theorem invFlipLocX_apply (hI : I.FG) (a : annulusAlgebra R I q) :
    invFlipLocX R I q hI a =
      annulusOverlapInvX R I q hI (locX R I q (annulusFlipHom R I q hI a)) := rfl

variable [TopologicalSpace R] [IsAdicRing I]

/-- **The twisted `x`-chart bridge** `ψˣʸ : A{1/x} ≃ₐ[R] A[y⁻¹]^∧`: the `x`-chart bridge
`graphChartAlgX` followed by the 𝔾m-inversion `A[x⁻¹]^∧ ≃ₐ[R] A[y⁻¹]^∧`. -/
def graphChartAlgXY (hI : I.FG) :
    awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q) ≃ₐ[R]
      annulusOverlapY R I q :=
  (graphChartAlgX R I q).trans (annulusOverlapInversionAlg R I q hI)

theorem graphChartAlgXY_algebraMap (hI : I.FG) (a : annulusAlgebra R I q) :
    graphChartAlgXY R I q hI
        (algebraMap (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)) a) =
      annulusOverlapInversion R I q hI (locX R I q a) := by
  rw [graphChartAlgXY, AlgEquiv.trans_apply, graphChartAlgX_algebraMap]
  rfl

variable [IsNoetherianRing R]

/-! ### The four `x`-localized graph lifts -/

section Lifts

variable (hI : I.FG)

/-- The graph lift `A ⊗̂_R A{1/x} →+* A[y⁻¹]^∧` (`(false, true)` chart, `dAX` summand). -/
def graphLiftAXtoY :
    CompletedTensorProduct R I (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)) →+*
      annulusOverlapY R I q :=
  haveI : IsAdicComplete (annulusOverlapIdealY R I q) (annulusOverlapY R I q) :=
    (annulusOverlapY_isAdicRing R I q hI).toIsAdicComplete
  CompletedTensorProduct.lift (annulusOverlapIdealY R I q)
    (le_of_eq (overlapIdealY_eq_map R I q).symm)
    (locY R I q) (graphChartAlgXY R I q hI).toAlgHom

/-- The graph lift `A{1/x} ⊗̂_R A →+* A[x⁻¹]^∧` (`(false, true)` chart, `dXA` summand). -/
def graphLiftXAtoX :
    CompletedTensorProduct R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
        (annulusAlgebra R I q) →+* annulusOverlap R I q :=
  haveI : IsAdicComplete (annulusOverlapIdeal R I q) (annulusOverlap R I q) :=
    (annulusOverlap_isAdicRing R I q hI).toIsAdicComplete
  CompletedTensorProduct.lift (annulusOverlapIdeal R I q)
    (le_of_eq (overlapIdeal_eq_map R I q).symm)
    (graphChartAlgX R I q).toAlgHom (invFlipLocX R I q hI)

/-- The graph lift `A{1/x} ⊗̂_R A →+* A[y⁻¹]^∧` (`(true, false)` chart, `dXA` summand). -/
def graphLiftXAtoY :
    CompletedTensorProduct R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
        (annulusAlgebra R I q) →+* annulusOverlapY R I q :=
  haveI : IsAdicComplete (annulusOverlapIdealY R I q) (annulusOverlapY R I q) :=
    (annulusOverlapY_isAdicRing R I q hI).toIsAdicComplete
  CompletedTensorProduct.lift (annulusOverlapIdealY R I q)
    (le_of_eq (overlapIdealY_eq_map R I q).symm)
    (graphChartAlgXY R I q hI).toAlgHom (locY R I q)

/-- The graph lift `A ⊗̂_R A{1/x} →+* A[x⁻¹]^∧` (`(true, false)` chart, `dAX` summand). -/
def graphLiftAXtoX :
    CompletedTensorProduct R I (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)) →+*
      annulusOverlap R I q :=
  haveI : IsAdicComplete (annulusOverlapIdeal R I q) (annulusOverlap R I q) :=
    (annulusOverlap_isAdicRing R I q hI).toIsAdicComplete
  CompletedTensorProduct.lift (annulusOverlapIdeal R I q)
    (le_of_eq (overlapIdeal_eq_map R I q).symm)
    (invFlipLocX R I q hI) (graphChartAlgX R I q).toAlgHom

/-! #### Legs -/

theorem graphLiftAXtoY_inl (a : annulusAlgebra R I q) :
    graphLiftAXtoY R I q hI (inl R I _ _ a) = locY R I q a := by
  haveI : IsAdicComplete (annulusOverlapIdealY R I q) (annulusOverlapY R I q) :=
    (annulusOverlapY_isAdicRing R I q hI).toIsAdicComplete
  rw [graphLiftAXtoY, lift_inl]

theorem graphLiftAXtoY_inr
    (z : awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)) :
    graphLiftAXtoY R I q hI (inr R I _ _ z) = graphChartAlgXY R I q hI z := by
  haveI : IsAdicComplete (annulusOverlapIdealY R I q) (annulusOverlapY R I q) :=
    (annulusOverlapY_isAdicRing R I q hI).toIsAdicComplete
  rw [graphLiftAXtoY, lift_inr]
  rfl

theorem graphLiftXAtoX_inl
    (z : awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)) :
    graphLiftXAtoX R I q hI (inl R I _ _ z) = graphChartAlgX R I q z := by
  haveI : IsAdicComplete (annulusOverlapIdeal R I q) (annulusOverlap R I q) :=
    (annulusOverlap_isAdicRing R I q hI).toIsAdicComplete
  rw [graphLiftXAtoX, lift_inl]
  rfl

theorem graphLiftXAtoX_inr (a : annulusAlgebra R I q) :
    graphLiftXAtoX R I q hI (inr R I _ _ a) = invFlipLocX R I q hI a := by
  haveI : IsAdicComplete (annulusOverlapIdeal R I q) (annulusOverlap R I q) :=
    (annulusOverlap_isAdicRing R I q hI).toIsAdicComplete
  rw [graphLiftXAtoX, lift_inr]

theorem graphLiftXAtoY_inl
    (z : awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)) :
    graphLiftXAtoY R I q hI (inl R I _ _ z) = graphChartAlgXY R I q hI z := by
  haveI : IsAdicComplete (annulusOverlapIdealY R I q) (annulusOverlapY R I q) :=
    (annulusOverlapY_isAdicRing R I q hI).toIsAdicComplete
  rw [graphLiftXAtoY, lift_inl]
  rfl

theorem graphLiftXAtoY_inr (a : annulusAlgebra R I q) :
    graphLiftXAtoY R I q hI (inr R I _ _ a) = locY R I q a := by
  haveI : IsAdicComplete (annulusOverlapIdealY R I q) (annulusOverlapY R I q) :=
    (annulusOverlapY_isAdicRing R I q hI).toIsAdicComplete
  rw [graphLiftXAtoY, lift_inr]

theorem graphLiftAXtoX_inl (a : annulusAlgebra R I q) :
    graphLiftAXtoX R I q hI (inl R I _ _ a) = invFlipLocX R I q hI a := by
  haveI : IsAdicComplete (annulusOverlapIdeal R I q) (annulusOverlap R I q) :=
    (annulusOverlap_isAdicRing R I q hI).toIsAdicComplete
  rw [graphLiftAXtoX, lift_inl]

theorem graphLiftAXtoX_inr
    (z : awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)) :
    graphLiftAXtoX R I q hI (inr R I _ _ z) = graphChartAlgX R I q z := by
  haveI : IsAdicComplete (annulusOverlapIdeal R I q) (annulusOverlap R I q) :=
    (annulusOverlap_isAdicRing R I q hI).toIsAdicComplete
  rw [graphLiftAXtoX, lift_inr]
  rfl

/-! #### Continuity -/

theorem graphLiftAXtoY_mem_pow (m : ℕ)
    {x : CompletedTensorProduct R I (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))}
    (hx : x ∈ (idealOfDefinition R I (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) ^ m) :
    graphLiftAXtoY R I q hI x ∈ (annulusOverlapIdealY R I q) ^ m := by
  haveI : IsAdicComplete (annulusOverlapIdealY R I q) (annulusOverlapY R I q) :=
    (annulusOverlapY_isAdicRing R I q hI).toIsAdicComplete
  exact lift_mem_pow _ _ _ _ hI m hx

theorem graphLiftXAtoX_mem_pow (m : ℕ)
    {x : CompletedTensorProduct R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
      (annulusAlgebra R I q)}
    (hx : x ∈ (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
      (annulusAlgebra R I q)) ^ m) :
    graphLiftXAtoX R I q hI x ∈ (annulusOverlapIdeal R I q) ^ m := by
  haveI : IsAdicComplete (annulusOverlapIdeal R I q) (annulusOverlap R I q) :=
    (annulusOverlap_isAdicRing R I q hI).toIsAdicComplete
  exact lift_mem_pow _ _ _ _ hI m hx

theorem graphLiftXAtoY_mem_pow (m : ℕ)
    {x : CompletedTensorProduct R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
      (annulusAlgebra R I q)}
    (hx : x ∈ (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
      (annulusAlgebra R I q)) ^ m) :
    graphLiftXAtoY R I q hI x ∈ (annulusOverlapIdealY R I q) ^ m := by
  haveI : IsAdicComplete (annulusOverlapIdealY R I q) (annulusOverlapY R I q) :=
    (annulusOverlapY_isAdicRing R I q hI).toIsAdicComplete
  exact lift_mem_pow _ _ _ _ hI m hx

theorem graphLiftAXtoX_mem_pow (m : ℕ)
    {x : CompletedTensorProduct R I (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))}
    (hx : x ∈ (idealOfDefinition R I (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) ^ m) :
    graphLiftAXtoX R I q hI x ∈ (annulusOverlapIdeal R I q) ^ m := by
  haveI : IsAdicComplete (annulusOverlapIdeal R I q) (annulusOverlap R I q) :=
    (annulusOverlap_isAdicRing R I q hI).toIsAdicComplete
  exact lift_mem_pow _ _ _ _ hI m hx

/-! #### Surjectivity -/

theorem graphLiftAXtoY_surjective : Function.Surjective (graphLiftAXtoY R I q hI) := fun e =>
  ⟨inr R I _ _ ((graphChartAlgXY R I q hI).symm e), by
    rw [graphLiftAXtoY_inr]; exact (graphChartAlgXY R I q hI).apply_symm_apply e⟩

theorem graphLiftXAtoX_surjective : Function.Surjective (graphLiftXAtoX R I q hI) := fun e =>
  ⟨inl R I _ _ ((graphChartAlgX R I q).symm e), by
    rw [graphLiftXAtoX_inl]; exact (graphChartAlgX R I q).apply_symm_apply e⟩

theorem graphLiftXAtoY_surjective : Function.Surjective (graphLiftXAtoY R I q hI) := fun e =>
  ⟨inl R I _ _ ((graphChartAlgXY R I q hI).symm e), by
    rw [graphLiftXAtoY_inl]; exact (graphChartAlgXY R I q hI).apply_symm_apply e⟩

theorem graphLiftAXtoX_surjective : Function.Surjective (graphLiftAXtoX R I q hI) := fun e =>
  ⟨inr R I _ _ ((graphChartAlgX R I q).symm e), by
    rw [graphLiftAXtoX_inr]; exact (graphChartAlgX R I q).apply_symm_apply e⟩

end Lifts

/-! ### The four factorization identities -/

section Factor

variable (hI : I.FG)

private theorem graphCodiagX_mem_pow (m : ℕ)
    {x : CompletedTensorProduct R I (annulusAlgebra R I q) (annulusAlgebra R I q)}
    (hx : x ∈ (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) ^ m) :
    graphCodiagX R I q hI x ∈ (annulusOverlapIdeal R I q) ^ m := by
  have h : ((idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) ^ m).map
      (graphCodiagX R I q hI) = (annulusOverlapIdeal R I q) ^ m := by
    rw [Ideal.map_pow, map_graphCodiagX_eq]
  exact h.le (Ideal.mem_map_of_mem _ hx)

private theorem graphCodiagY_mem_pow (m : ℕ)
    {x : CompletedTensorProduct R I (annulusAlgebra R I q) (annulusAlgebra R I q)}
    (hx : x ∈ (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) ^ m) :
    graphCodiagY R I q hI x ∈ (annulusOverlapIdealY R I q) ^ m := by
  have h : ((idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) ^ m).map
      (graphCodiagY R I q hI) = (annulusOverlapIdealY R I q) ^ m := by
    rw [Ideal.map_pow, map_graphCodiagY_eq]
  exact h.le (Ideal.mem_map_of_mem _ hx)

/-- **(A)** for the `(false, true)` chart's `dAX` summand: the `y`-side graph codiagonal factors
through the `x`-summand of the second-factor overlap chart. -/
theorem graphLiftAXtoY_comp_map :
    (graphLiftAXtoY R I q hI).comp
        (map hI (AlgHom.id R (annulusAlgebra R I q))
          (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))) =
      graphCodiagY R I q hI := by
  haveI : IsAdicComplete (annulusOverlapIdealY R I q) (annulusOverlapY R I q) :=
    (annulusOverlapY_isAdicRing R I q hI).toIsAdicComplete
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicComplete (I.map (algebraMap R (annulusAlgebra R I q))) (annulusAlgebra R I q) :=
    (annulus_isAdicRing_map R I q hI).toIsAdicComplete
  refine hom_ext (annulusOverlapIdealY R I q) hI (fun m x hx => ?_) (fun m x hx => ?_)
    (fun a => ?_) (fun b => ?_)
  · exact graphLiftAXtoY_mem_pow R I q hI m (map_mem_pow hI _ _ m hx)
  · exact graphCodiagY_mem_pow R I q hI m hx
  · rw [RingHom.comp_apply, map_inl, AlgHom.id_apply, graphLiftAXtoY_inl, graphCodiagY_inl]
  · rw [RingHom.comp_apply, map_inr, graphLiftAXtoY_inr, IsScalarTower.coe_toAlgHom',
      graphChartAlgXY_algebraMap, graphCodiagY_inr]

/-- **(A)** for the `(false, true)` chart's `dXA` summand: the `x`-side graph codiagonal factors
through the `x`-summand of the first-factor overlap chart. -/
theorem graphLiftXAtoX_comp_map :
    (graphLiftXAtoX R I q hI).comp
        (map hI
          (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))
          (AlgHom.id R (annulusAlgebra R I q))) =
      graphCodiagX R I q hI := by
  haveI : IsAdicComplete (annulusOverlapIdeal R I q) (annulusOverlap R I q) :=
    (annulusOverlap_isAdicRing R I q hI).toIsAdicComplete
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicComplete (I.map (algebraMap R (annulusAlgebra R I q))) (annulusAlgebra R I q) :=
    (annulus_isAdicRing_map R I q hI).toIsAdicComplete
  refine hom_ext (annulusOverlapIdeal R I q) hI (fun m x hx => ?_) (fun m x hx => ?_)
    (fun a => ?_) (fun b => ?_)
  · exact graphLiftXAtoX_mem_pow R I q hI m (map_mem_pow hI _ _ m hx)
  · exact graphCodiagX_mem_pow R I q hI m hx
  · rw [RingHom.comp_apply, map_inl, graphLiftXAtoX_inl, IsScalarTower.coe_toAlgHom',
      graphChartAlgX_algebraMap, graphCodiagX_inl]
    rfl
  · rw [RingHom.comp_apply, map_inr, AlgHom.id_apply, graphLiftXAtoX_inr, invFlipLocX_apply,
      graphCodiagX_inr]

/-- **(A)** for the `(true, false)` chart's `dXA` summand. -/
theorem graphLiftXAtoY_comp_map :
    (graphLiftXAtoY R I q hI).comp
        (map hI
          (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))
          (AlgHom.id R (annulusAlgebra R I q))) =
      (graphCodiagY R I q hI).comp
        (commHom (R := R) (I := I) (A := annulusAlgebra R I q)
          (B := annulusAlgebra R I q) hI) := by
  haveI : IsAdicComplete (annulusOverlapIdealY R I q) (annulusOverlapY R I q) :=
    (annulusOverlapY_isAdicRing R I q hI).toIsAdicComplete
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicComplete (I.map (algebraMap R (annulusAlgebra R I q))) (annulusAlgebra R I q) :=
    (annulus_isAdicRing_map R I q hI).toIsAdicComplete
  refine hom_ext (annulusOverlapIdealY R I q) hI (fun m x hx => ?_) (fun m x hx => ?_)
    (fun a => ?_) (fun b => ?_)
  · exact graphLiftXAtoY_mem_pow R I q hI m (map_mem_pow hI _ _ m hx)
  · exact graphCodiagY_mem_pow R I q hI m (commHom_mem_pow hI m hx)
  · rw [RingHom.comp_apply, map_inl, graphLiftXAtoY_inl, IsScalarTower.coe_toAlgHom',
      graphChartAlgXY_algebraMap, RingHom.comp_apply, commHom_inl, graphCodiagY_inr]
  · rw [RingHom.comp_apply, map_inr, AlgHom.id_apply, graphLiftXAtoY_inr, RingHom.comp_apply,
      commHom_inr, graphCodiagY_inl]

/-- **(A)** for the `(true, false)` chart's `dAX` summand. -/
theorem graphLiftAXtoX_comp_map :
    (graphLiftAXtoX R I q hI).comp
        (map hI (AlgHom.id R (annulusAlgebra R I q))
          (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))) =
      (graphCodiagX R I q hI).comp
        (commHom (R := R) (I := I) (A := annulusAlgebra R I q)
          (B := annulusAlgebra R I q) hI) := by
  haveI : IsAdicComplete (annulusOverlapIdeal R I q) (annulusOverlap R I q) :=
    (annulusOverlap_isAdicRing R I q hI).toIsAdicComplete
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicComplete (I.map (algebraMap R (annulusAlgebra R I q))) (annulusAlgebra R I q) :=
    (annulus_isAdicRing_map R I q hI).toIsAdicComplete
  refine hom_ext (annulusOverlapIdeal R I q) hI (fun m x hx => ?_) (fun m x hx => ?_)
    (fun a => ?_) (fun b => ?_)
  · exact graphLiftAXtoX_mem_pow R I q hI m (map_mem_pow hI _ _ m hx)
  · exact graphCodiagX_mem_pow R I q hI m (commHom_mem_pow hI m hx)
  · rw [RingHom.comp_apply, map_inl, AlgHom.id_apply, graphLiftAXtoX_inl, invFlipLocX_apply,
      RingHom.comp_apply, commHom_inl, graphCodiagX_inr]
  · rw [RingHom.comp_apply, map_inr, graphLiftAXtoX_inr, IsScalarTower.coe_toAlgHom',
      graphChartAlgX_algebraMap, RingHom.comp_apply, commHom_inr, graphCodiagX_inl]
    rfl

end Factor

/-! ### The `Spf`-level factorizations -/

section Geometric

/-- `Spf` of the graph lift `graphLiftAXtoY`. -/
def spfGraphLiftAXtoY (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I
        (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    locallyRingedSpaceObj (annulusOverlapIdealY R I q) ⟶
      locallyRingedSpaceObj (idealOfDefinition R I
        (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) :=
  haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I
      (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  locallyRingedSpaceMap _ _ (graphLiftAXtoY R I q hI) (by
    intro x hx
    rw [Ideal.mem_comap]
    have h := graphLiftAXtoY_mem_pow R I q hI 1 (by rwa [pow_one])
    rwa [pow_one] at h)

/-- `Spf` of the graph lift `graphLiftXAtoX`. -/
def spfGraphLiftXAtoX (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
        (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    locallyRingedSpaceObj (annulusOverlapIdeal R I q) ⟶
      locallyRingedSpaceObj (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
        (annulusAlgebra R I q)) :=
  haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
        (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  locallyRingedSpaceMap _ _ (graphLiftXAtoX R I q hI) (by
    intro x hx
    rw [Ideal.mem_comap]
    have h := graphLiftXAtoX_mem_pow R I q hI 1 (by rwa [pow_one])
    rwa [pow_one] at h)

/-- `Spf` of the graph lift `graphLiftXAtoY`. -/
def spfGraphLiftXAtoY (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
        (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    locallyRingedSpaceObj (annulusOverlapIdealY R I q) ⟶
      locallyRingedSpaceObj (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
        (annulusAlgebra R I q)) :=
  haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
        (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  locallyRingedSpaceMap _ _ (graphLiftXAtoY R I q hI) (by
    intro x hx
    rw [Ideal.mem_comap]
    have h := graphLiftXAtoY_mem_pow R I q hI 1 (by rwa [pow_one])
    rwa [pow_one] at h)

/-- `Spf` of the graph lift `graphLiftAXtoX`. -/
def spfGraphLiftAXtoX (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I
        (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    locallyRingedSpaceObj (annulusOverlapIdeal R I q) ⟶
      locallyRingedSpaceObj (idealOfDefinition R I
        (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) :=
  haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I
      (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  locallyRingedSpaceMap _ _ (graphLiftAXtoX R I q hI) (by
    intro x hx
    rw [Ideal.mem_comap]
    have h := graphLiftAXtoX_mem_pow R I q hI 1 (by rwa [pow_one])
    rwa [pow_one] at h)

/-- **(A)** at the `(false, true)` chart's `dAX` summand. -/
theorem spfGraphCodiagY_eq_ft_dAX (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    spfGraphCodiagY R I q hI =
      spfGraphLiftAXtoY R I q hI ≫
        rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapX R I q) hI := by
  haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  have hIK : idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≤
      (annulusOverlapIdealY R I q).comap ((graphLiftAXtoY R I q hI).comp
        (CompletedTensorProduct.map hI
          (AlgHom.id R (annulusAlgebra R I q))
          (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))))) := by
    rw [graphLiftAXtoY_comp_map R I q hI]
    exact graphCodiagY_le_comap hI
  rw [rightInterchangeOpenImmersion_eq_mapSpf, CompletedTensorProduct.mapSpf_eq,
    spfGraphLiftAXtoY, spfGraphCodiagY,
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIK)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _
    (graphLiftAXtoY_comp_map R I q hI).symm

/-- **(A)** at the `(false, true)` chart's `dXA` summand. -/
theorem spfGraphCodiagX_eq_ft_dXA (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
        (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    spfGraphCodiagX R I q hI =
      spfGraphLiftXAtoX R I q hI ≫
        interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapX R I q) hI := by
  haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
        (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  have hIK : idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≤
      (annulusOverlapIdeal R I q).comap ((graphLiftXAtoX R I q hI).comp
        (CompletedTensorProduct.map hI
          (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))
          (AlgHom.id R (annulusAlgebra R I q)))) := by
    rw [graphLiftXAtoX_comp_map R I q hI]
    exact graphCodiagX_le_comap hI
  rw [interchangeOpenImmersion_eq_mapSpf, CompletedTensorProduct.mapSpf_eq,
    spfGraphLiftXAtoX, spfGraphCodiagX,
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIK)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _
    (graphLiftXAtoX_comp_map R I q hI).symm

/-- **(A)** at the `(true, false)` chart's `dXA` summand. -/
theorem spfGraphCodiagYComm_eq_tf_dXA (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
        (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    spfGraphCodiagYComm R I q hI =
      spfGraphLiftXAtoY R I q hI ≫
        interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapX R I q) hI := by
  haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
        (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  have hIK : idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≤
      (annulusOverlapIdealY R I q).comap ((graphLiftXAtoY R I q hI).comp
        (CompletedTensorProduct.map hI
          (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))
          (AlgHom.id R (annulusAlgebra R I q)))) := by
    rw [graphLiftXAtoY_comp_map R I q hI]
    intro x hx
    rw [Ideal.mem_comap, RingHom.comp_apply]
    exact graphCodiagY_le_comap hI (commHom_le_comap_self R I q hI hx)
  rw [interchangeOpenImmersion_eq_mapSpf, CompletedTensorProduct.mapSpf_eq,
    spfGraphLiftXAtoY, spfGraphCodiagYComm,
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIK)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _
    (graphLiftXAtoY_comp_map R I q hI).symm

/-- **(A)** at the `(true, false)` chart's `dAX` summand. -/
theorem spfGraphCodiagXComm_eq_tf_dAX (hI : I.FG) :
    haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    spfGraphCodiagXComm R I q hI =
      spfGraphLiftAXtoX R I q hI ≫
        rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapX R I q) hI := by
  haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  have hIK : idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≤
      (annulusOverlapIdeal R I q).comap ((graphLiftAXtoX R I q hI).comp
        (CompletedTensorProduct.map hI
          (AlgHom.id R (annulusAlgebra R I q))
          (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))))) := by
    rw [graphLiftAXtoX_comp_map R I q hI]
    intro x hx
    rw [Ideal.mem_comap, RingHom.comp_apply]
    exact graphCodiagX_le_comap hI (commHom_le_comap_self R I q hI hx)
  rw [rightInterchangeOpenImmersion_eq_mapSpf, CompletedTensorProduct.mapSpf_eq,
    spfGraphLiftAXtoX, spfGraphCodiagXComm,
    ← FormalSpectrum.locallyRingedSpaceMap_comp (hIK := hIK)]
  exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _
    (graphLiftAXtoX_comp_map R I q hI).symm

end Geometric

end AlgebraicGeometry
