import FormalSchemes.DiagonalPreimageGraph
import FormalSchemes.TateGraphCodiagonalXLift

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

/-!
# The eight preimage bounds of the Tate diagonal in a mixed chart

Fix an adic base `(R, I)` with `I` finitely generated and a Tate parameter `q ∈ I`, write
`A = annulusAlgebra R I q`, `A{1/x}`, `A{1/y}` for the two basic-open chart domains and
`Ω_x = A[x⁻¹]^∧`, `Ω_y = A[y⁻¹]^∧`.

The `⊆` half of the mixed-chart description of the Tate diagonal (issue 503b/424-ii) needs, for
each **mixed** chart `(b, ¬b)` of the four-chart self fibre product, each of the two diagonal
charts `(c, c)` it meets, and each of the **two summands** of the corresponding overlap object, a
bound

```
Spf φ ⁻¹' (range Δ_aff) ⊆ range (Spf g)
```

where `Δ_aff` is the affine diagonal chart `diagChart` of `Spf A`, `φ` is the ring map underlying
the summand's transition composite `inᵢ ≫ t.hom ≫ overlapChart`, and `g` is that summand's graph
lift. That is `2 × 2 × 2 = 8` bounds.

There are only **four** distinct `φ`s: the transition composite does not depend on the chart
`(b, ¬b)`, only on which overlap (first- or second-factor) and which summand. Each `φ` is used with
two different graph lifts — one landing in `Ω_x` and one in `Ω_y` — because the two mixed charts
attach the two graph pieces to the summands in opposite ways.

## Main results

Two general packaging lemmas over `FormalSchemes.DiagonalPreimageGraph`:

* `CompletedTensorProduct.preimage_range_codiagonal_subset_of_inr_iso` — the right shape: the
  second tensor factor of the target carries the isomorphism leg of `g`;
* `CompletedTensorProduct.preimage_range_codiagonal_subset_of_inl_iso` — the mirror.

The four leg identities feeding them, the eight bounds
`preimage_range_diagChart_subset_*` (named by `(overlap, summand, target)`), the four
identifications `spf*Transition*_eq` of the transition composites `inᵢ ≫ t.hom ≫ overlapChart`
with `Spf` of the corresponding ring map, and the resulting geometric forms
`spfPreimage_range_diagChart_subset_*` — the shape the assembly (issue 557d) consumes.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
-/

noncomputable section

open Ideal AlgebraicGeometry CategoryTheory CategoryTheory.Limits FormalSpectrum
  CompletedTensorProduct CompletedTensorAwayInterchange

universe u

namespace CompletedTensorProduct

variable {R : Type u} [CommRing R] {I : Ideal R} [TopologicalSpace R] [IsAdicRing I]

section Generic

variable {A C E : Type u} [CommRing A] [CommRing C] [CommRing E]
variable [Algebra R A] [Algebra R C] [Algebra R E]
variable [TopologicalSpace A] [IsAdicRing (I.map (algebraMap R A))]
variable [TopologicalSpace E]
variable [TopologicalSpace (CompletedTensorProduct R I A A)]
  [IsAdicRing (idealOfDefinition R I A A)]

/-- **The preimage bound, right shape.** Let `φ : A ⊗̂_R A →+* A ⊗̂_R C` send `inl a ↦ inl a` and
`inr a ↦ inr (θ a)`, and let `g : A ⊗̂_R C →+* E` be adic with `g (inl a) = f₁ a` and
`g (inr c) = ψ c` for an `R`-algebra isomorphism `ψ : C ≃ₐ[R] E`. If `ψ ∘ θ = f₁` — the *graph
condition* — then the preimage under `Spf φ` of the affine diagonal locus of `Spf A` lies in the
range of `Spf g`.

`g` is automatically surjective (`inr ∘ ψ⁻¹` splits it), and that same map is the continuous
section required by `CompletedTensorProduct.mem_of_section`; the `inr` graph relation is then
identically zero and the `inl` one is `φ (inl a) - φ (inr a)`, which
`CompletedTensorProduct.map_inl_sub_map_inr_mem` discharges. -/
theorem preimage_range_codiagonal_subset_of_inr_iso
    [TopologicalSpace (CompletedTensorProduct R I A C)]
    [IsAdicRing (idealOfDefinition R I A C)]
    (hI : I.FG) (IA₀ : Ideal A) [IsAdicRing IA₀] (IE : Ideal E) [IsAdicRing IE]
    (hc : idealOfDefinition R I A A ≤ IA₀.comap (codiagonal R I A))
    (φ : CompletedTensorProduct R I A A →+* CompletedTensorProduct R I A C)
    (hφ : idealOfDefinition R I A A ≤ (idealOfDefinition R I A C).comap φ)
    (g : CompletedTensorProduct R I A C →+* E)
    (hg : idealOfDefinition R I A C ≤ IE.comap g)
    (hgpow : ∀ (m : ℕ) (x : CompletedTensorProduct R I A C),
      x ∈ (idealOfDefinition R I A C) ^ m → g x ∈ IE ^ m)
    (hIE : IE = I.map (algebraMap R E))
    (θ : A → C) (f₁ : A → E) (ψ : C ≃ₐ[R] E)
    (hφl : ∀ a : A, φ (inl R I A A a) = inl R I A C a)
    (hφr : ∀ a : A, φ (inr R I A A a) = inr R I A C (θ a))
    (hginl : ∀ a : A, g (inl R I A C a) = f₁ a)
    (hginr : ∀ c : C, g (inr R I A C c) = ψ c)
    (hleg : ∀ a : A, ψ (θ a) = f₁ a) :
    FormalSpectrum.map (idealOfDefinition R I A A) (idealOfDefinition R I A C) φ hφ ⁻¹'
        Set.range (FormalSpectrum.map (idealOfDefinition R I A A) IA₀ (codiagonal R I A) hc) ⊆
      Set.range (FormalSpectrum.map (idealOfDefinition R I A C) IE g hg) := by
  have hgs : Function.Surjective g := fun e =>
    ⟨inr R I A C (ψ.symm e), by rw [hginr]; exact ψ.apply_symm_apply e⟩
  set s : E →+* CompletedTensorProduct R I A C :=
    (inr R I A C).toRingHom.comp (ψ.symm : E →+* C) with hsdef
  have hsapp : ∀ e : E, s e = inr R I A C (ψ.symm e) := fun _ => rfl
  have hspow : ∀ (m : ℕ) (e : E), e ∈ IE ^ m → s e ∈ (idealOfDefinition R I A C) ^ m := by
    intro m e he
    rw [hsapp]
    refine inr_mem_pow m ?_
    have hmap : Ideal.map (ψ.symm : E →+* C) (I.map (algebraMap R E)) =
        I.map (algebraMap R C) := by
      rw [Ideal.map_map]
      congr 1
      exact RingHom.ext fun r => ψ.symm.commutes r
    have hz : (ψ.symm : E →+* C) e ∈
        Ideal.map (ψ.symm : E →+* C) ((I.map (algebraMap R E)) ^ m) :=
      Ideal.mem_map_of_mem _ (by rwa [← hIE])
    rw [Ideal.map_pow, hmap] at hz
    exact hz
  refine FormalSpectrum.preimage_range_subset_range_of_ker_le _ _ _ _ φ hφ g hg hgs
    (codiagonal R I A) hc codiagonal_surjective ?_
  refine FormalSpectrum.ker_quotientMap_le_map_of_mem_sup _ _ _ _ φ hφ g hg
    (codiagonal R I A) hc fun z hz => ?_
  refine mem_of_section hI IE g hgpow s hspow _ le_sup_right (fun a => ?_) (fun c => ?_) hz
  · have h1 : s (g (inl R I A C a)) = inr R I A C (θ a) := by
      rw [hginl, hsapp, ← hleg a, ψ.symm_apply_apply]
    rw [h1, ← hφl a, ← hφr a]
    exact Submodule.mem_sup_left (map_inl_sub_map_inr_mem φ a)
  · have h2 : s (g (inr R I A C c)) = inr R I A C c := by
      rw [hginr, hsapp, ψ.symm_apply_apply]
    rw [h2, sub_self]
    exact Submodule.zero_mem _

/-- **The preimage bound, left shape** — the mirror of
`CompletedTensorProduct.preimage_range_codiagonal_subset_of_inr_iso` with the isomorphism leg of
`g` on the *first* tensor factor. Here the `inl` graph relation vanishes and the `inr` one is
`φ (inr a) - φ (inl a)`, the negative of a diagonal generator's image. -/
theorem preimage_range_codiagonal_subset_of_inl_iso
    [TopologicalSpace (CompletedTensorProduct R I C A)]
    [IsAdicRing (idealOfDefinition R I C A)]
    (hI : I.FG) (IA₀ : Ideal A) [IsAdicRing IA₀] (IE : Ideal E) [IsAdicRing IE]
    (hc : idealOfDefinition R I A A ≤ IA₀.comap (codiagonal R I A))
    (φ : CompletedTensorProduct R I A A →+* CompletedTensorProduct R I C A)
    (hφ : idealOfDefinition R I A A ≤ (idealOfDefinition R I C A).comap φ)
    (g : CompletedTensorProduct R I C A →+* E)
    (hg : idealOfDefinition R I C A ≤ IE.comap g)
    (hgpow : ∀ (m : ℕ) (x : CompletedTensorProduct R I C A),
      x ∈ (idealOfDefinition R I C A) ^ m → g x ∈ IE ^ m)
    (hIE : IE = I.map (algebraMap R E))
    (θ : A → C) (f₁ : A → E) (ψ : C ≃ₐ[R] E)
    (hφl : ∀ a : A, φ (inl R I A A a) = inl R I C A (θ a))
    (hφr : ∀ a : A, φ (inr R I A A a) = inr R I C A a)
    (hginl : ∀ c : C, g (inl R I C A c) = ψ c)
    (hginr : ∀ a : A, g (inr R I C A a) = f₁ a)
    (hleg : ∀ a : A, ψ (θ a) = f₁ a) :
    FormalSpectrum.map (idealOfDefinition R I A A) (idealOfDefinition R I C A) φ hφ ⁻¹'
        Set.range (FormalSpectrum.map (idealOfDefinition R I A A) IA₀ (codiagonal R I A) hc) ⊆
      Set.range (FormalSpectrum.map (idealOfDefinition R I C A) IE g hg) := by
  have hgs : Function.Surjective g := fun e =>
    ⟨inl R I C A (ψ.symm e), by rw [hginl]; exact ψ.apply_symm_apply e⟩
  set s : E →+* CompletedTensorProduct R I C A :=
    (inl R I C A).toRingHom.comp (ψ.symm : E →+* C) with hsdef
  have hsapp : ∀ e : E, s e = inl R I C A (ψ.symm e) := fun _ => rfl
  have hspow : ∀ (m : ℕ) (e : E), e ∈ IE ^ m → s e ∈ (idealOfDefinition R I C A) ^ m := by
    intro m e he
    rw [hsapp]
    refine inl_mem_pow m ?_
    have hmap : Ideal.map (ψ.symm : E →+* C) (I.map (algebraMap R E)) =
        I.map (algebraMap R C) := by
      rw [Ideal.map_map]
      congr 1
      exact RingHom.ext fun r => ψ.symm.commutes r
    have hz : (ψ.symm : E →+* C) e ∈
        Ideal.map (ψ.symm : E →+* C) ((I.map (algebraMap R E)) ^ m) :=
      Ideal.mem_map_of_mem _ (by rwa [← hIE])
    rw [Ideal.map_pow, hmap] at hz
    exact hz
  refine FormalSpectrum.preimage_range_subset_range_of_ker_le _ _ _ _ φ hφ g hg hgs
    (codiagonal R I A) hc codiagonal_surjective ?_
  refine FormalSpectrum.ker_quotientMap_le_map_of_mem_sup _ _ _ _ φ hφ g hg
    (codiagonal R I A) hc fun z hz => ?_
  refine mem_of_section hI IE g hgpow s hspow _ le_sup_right (fun c => ?_) (fun a => ?_) hz
  · have h1 : s (g (inl R I C A c)) = inl R I C A c := by
      rw [hginl, hsapp, ψ.symm_apply_apply]
    rw [h1, sub_self]
    exact Submodule.zero_mem _
  · have h2 : s (g (inr R I C A a)) = inl R I C A (θ a) := by
      rw [hginr, hsapp, ← hleg a, ψ.symm_apply_apply]
    rw [h2, ← hφl a, ← hφr a, ← neg_sub]
    exact Submodule.neg_mem _ (Submodule.mem_sup_left (map_inl_sub_map_inr_mem φ a))

/-- Adicity of a composite of two functorial maps. -/
theorem map_comp_map_le_comap {A B A' B' A'' B'' : Type u}
    [CommRing A] [CommRing B] [CommRing A'] [CommRing B'] [CommRing A''] [CommRing B'']
    [Algebra R A] [Algebra R B] [Algebra R A'] [Algebra R B'] [Algebra R A''] [Algebra R B'']
    [TopologicalSpace (CompletedTensorProduct R I A B)] [IsAdicRing (idealOfDefinition R I A B)]
    [TopologicalSpace (CompletedTensorProduct R I A' B')]
    [IsAdicRing (idealOfDefinition R I A' B')]
    [TopologicalSpace (CompletedTensorProduct R I A'' B'')]
    [IsAdicRing (idealOfDefinition R I A'' B'')]
    (hI : I.FG) (f : A →ₐ[R] A') (g : B →ₐ[R] B') (f' : A' →ₐ[R] A'') (g' : B' →ₐ[R] B'') :
    idealOfDefinition R I A B ≤
      (idealOfDefinition R I A'' B'').comap ((map hI f' g').comp (map hI f g)) := by
  intro x hx
  rw [Ideal.mem_comap, RingHom.comp_apply]
  have h := map_mem_pow hI f' g' 1
    (map_mem_pow hI f g 1 (by rw [pow_one]; exact hx))
  rwa [pow_one] at h

end Generic

end CompletedTensorProduct

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R) [IsNoetherianRing R]
variable [TopologicalSpace R] [IsAdicRing I]

/-! ### The affine diagonal chart as `Spf` of the codiagonal -/

/-- The codiagonal `∇ : A ⊗̂_R A →+* A` is adic for the annulus ideal convention
`annulusIdealOfDefinition` — the continuity witness built into `diagChart`, exposed by name. -/
theorem annulusCodiagonal_le_comap (hI : I.FG) :
    haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
      annulus_isAdicRing_map R I q hI
    haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≤
      (annulusIdealOfDefinition R I q).comap
        (CompletedTensorProduct.codiagonal R I (annulusAlgebra R I q)) := by
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  refine Ideal.map_le_iff_le_comap.mp ?_
  rw [CompletedTensorProduct.map_codiagonal_eq (R := R) (I := I) (A := annulusAlgebra R I q)]
  exact (annulus_map_eq R I q).le

/-- The base map of the affine diagonal chart is `FormalSpectrum.map` of the codiagonal. -/
theorem diagChart_base_eq (hI : I.FG) :
    haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
      annulus_isAdicRing_map R I q hI
    haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    ⇑(diagChart R I q hI).base =
      FormalSpectrum.map
        (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))
        (annulusIdealOfDefinition R I q)
        (CompletedTensorProduct.codiagonal R I (annulusAlgebra R I q))
        (annulusCodiagonal_le_comap R I q hI) :=
  rfl

/-! ### The four leg identities -/

/-- `ψʸ ∘ τ ∘ (A → A{1/x})` is the structural map `A → A[x⁻¹]^∧`. -/
theorem graphChartAlgY_transition_locX (hI : I.FG) (a : annulusAlgebra R I q) :
    graphChartAlgY R I q hI
        (annulusFibreChartTransitionInvAlg R I q hI
          (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)) a)) =
      algebraMap (annulusAlgebra R I q) (annulusOverlap R I q) a := by
  rw [graphChartAlgY_transition_apply, IsScalarTower.coe_toAlgHom', graphChartAlgX_algebraMap]

/-- `ψʸ_plain ∘ τ ∘ (A → A{1/x})` is `invLocXY`. -/
theorem chartBridgeY_transition_locX (hI : I.FG) (a : annulusAlgebra R I q) :
    chartBridgeY R I q
        (annulusFibreChartTransitionInvAlg R I q hI
          (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)) a)) =
      invLocXY R I q hI a := by
  rw [chartBridgeY_transition_apply, IsScalarTower.coe_toAlgHom', graphChartAlgX_algebraMap,
    invLocXY_apply]

/-- `ψˣ ∘ τ⁻¹ ∘ (A → A{1/y})` is `invFlipLocX`. -/
theorem graphChartAlgX_transitionSymm_locY (hI : I.FG) (a : annulusAlgebra R I q) :
    graphChartAlgX R I q
        ((annulusFibreChartTransitionInvAlg R I q hI).symm
          (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)) a)) =
      invFlipLocX R I q hI a := by
  have h := graphChartAlgY_transition_apply R I q hI
    ((annulusFibreChartTransitionInvAlg R I q hI).symm
      (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)) a))
  rw [AlgEquiv.apply_symm_apply] at h
  rw [← h, IsScalarTower.coe_toAlgHom', graphChartAlgY_algebraMap, invFlipLocX_apply,
    IsScalarTower.coe_toAlgHom']

/-- `ψˣʸ ∘ τ⁻¹ ∘ (A → A{1/y})` is the structural map `A → A[y⁻¹]^∧`. -/
theorem graphChartAlgXY_transitionSymm_locY (hI : I.FG) (a : annulusAlgebra R I q) :
    graphChartAlgXY R I q hI
        ((annulusFibreChartTransitionInvAlg R I q hI).symm
          (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
            (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)) a)) =
      algebraMap (annulusAlgebra R I q) (annulusOverlapY R I q) a := by
  rw [graphChartAlgXY, AlgEquiv.trans_apply, graphChartAlgX_transitionSymm_locY,
    invFlipLocX_apply]
  change annulusOverlapInversion R I q hI
    (annulusOverlapInvX R I q hI
      (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)
        (annulusFlipHom R I q hI a))) = _
  rw [annulusOverlapInversion_annulusOverlapInvX, annulusOverlapTransition_algebraMap_annulus,
    annulusFlip_apply, ← AlgHom.comp_apply, annulusFlipHom_annulusFlipHom, AlgHom.id_apply]

/-! ### The legs of the three `#236` lifts that were not exposed -/

theorem graphLiftY_inl (hI : I.FG)
    (z : awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)) :
    graphLiftY R I q hI (inl R I _ _ z) = chartBridgeY R I q z := by
  haveI : IsAdicComplete (annulusOverlapIdealY R I q) (annulusOverlapY R I q) :=
    (annulusOverlapY_isAdicRing R I q hI).toIsAdicComplete
  rw [graphLiftY, lift_inl]
  rfl

theorem graphLiftY_inr (hI : I.FG) (a : annulusAlgebra R I q) :
    graphLiftY R I q hI (inr R I _ _ a) = invLocXY R I q hI a := by
  haveI : IsAdicComplete (annulusOverlapIdealY R I q) (annulusOverlapY R I q) :=
    (annulusOverlapY_isAdicRing R I q hI).toIsAdicComplete
  rw [graphLiftY, lift_inr]

theorem graphLiftXY_inl (hI : I.FG)
    (z : awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)) :
    graphLiftXY R I q hI (inl R I _ _ z) = graphChartAlgY R I q hI z := by
  haveI : IsAdicComplete (annulusOverlapIdeal R I q) (annulusOverlap R I q) :=
    (annulusOverlap_isAdicRing R I q hI).toIsAdicComplete
  rw [graphLiftXY, lift_inl]
  rfl

theorem graphLiftXY_inr (hI : I.FG) (a : annulusAlgebra R I q) :
    graphLiftXY R I q hI (inr R I _ _ a) =
      algebraMap (annulusAlgebra R I q) (annulusOverlap R I q) a := by
  haveI : IsAdicComplete (annulusOverlapIdeal R I q) (annulusOverlap R I q) :=
    (annulusOverlap_isAdicRing R I q hI).toIsAdicComplete
  rw [graphLiftXY, lift_inr]
  rfl

theorem graphLiftYX_inl (hI : I.FG) (a : annulusAlgebra R I q) :
    graphLiftYX R I q hI (inl R I _ _ a) = invLocXY R I q hI a := by
  haveI : IsAdicComplete (annulusOverlapIdealY R I q) (annulusOverlapY R I q) :=
    (annulusOverlapY_isAdicRing R I q hI).toIsAdicComplete
  rw [graphLiftYX, lift_inl]

theorem graphLiftYX_inr (hI : I.FG)
    (z : awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)) :
    graphLiftYX R I q hI (inr R I _ _ z) = chartBridgeY R I q z := by
  haveI : IsAdicComplete (annulusOverlapIdealY R I q) (annulusOverlapY R I q) :=
    (annulusOverlapY_isAdicRing R I q hI).toIsAdicComplete
  rw [graphLiftYX, lift_inr]
  rfl

/-! ### The eight preimage bounds -/

/-- **Mixed chart `(false, true)`, `c = false`, `dAY` summand.** The preimage of the affine
diagonal locus under the transition composite of the `y`-localized summand of the second-factor
overlap lies in the range of the `x`-side graph lift. -/
theorem preimage_range_diagChart_subset_second_dAY_x (hI : I.FG) :
    haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
      annulus_isAdicRing_map R I q hI
    haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
    haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    FormalSpectrum.map
        (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))
        (idealOfDefinition R I (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))
        ((map hI (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).toAlgHom
            (annulusFibreChartTransitionInvAlg R I q hI).toAlgHom).comp
          (map hI (AlgHom.id R (annulusAlgebra R I q))
            (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
              (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))))
        (CompletedTensorProduct.map_comp_map_le_comap hI _ _ _ _) ⁻¹'
        Set.range ⇑(diagChart R I q hI).base ⊆
      Set.range ⇑(spfGraphLiftX R I q hI).base := by
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) := annulus_isAdicRing R I q hI
  haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  rw [diagChart_base_eq]
  exact CompletedTensorProduct.preimage_range_codiagonal_subset_of_inr_iso hI
    (annulusIdealOfDefinition R I q) (annulusOverlapIdeal R I q)
    (annulusCodiagonal_le_comap R I q hI) _ _ (graphLiftX R I q hI) _
    (fun m x hx => graphLiftX_mem_pow R I q hI m hx) (overlapIdeal_eq_map R I q)
    (fun a => annulusFibreChartTransitionInvAlg R I q hI
      (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)) a))
    (fun a => algebraMap (annulusAlgebra R I q) (annulusOverlap R I q) a)
    (graphChartAlgY R I q hI)
    (fun a => by rw [RingHom.comp_apply, map_inl, map_inl]; rfl)
    (fun a => by rw [RingHom.comp_apply, map_inr, map_inr]; rfl)
    (fun a => graphLiftX_inl R I q hI a) (fun z => graphLiftX_inr R I q hI z)
    (fun a => graphChartAlgY_transition_locX R I q hI a)

/-- **Mixed chart `(true, false)`, `c = true`, `dAY` summand.** -/
theorem preimage_range_diagChart_subset_second_dAY_y (hI : I.FG) :
    haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
      annulus_isAdicRing_map R I q hI
    haveI : IsAdicRing (annulusIdealOfDefinition R I q) :=
      annulus_isAdicRing R I q hI
    haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
      (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapY R I q))) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q))) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    FormalSpectrum.map
        (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))
        (idealOfDefinition R I
          (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
            (overlapY R I q)))
        ((map hI (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).toAlgHom
            (annulusFibreChartTransitionInvAlg R I q hI).toAlgHom).comp
          (map hI (AlgHom.id R (annulusAlgebra R I q))
            (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
              (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
                (overlapX R I q)))))
        (CompletedTensorProduct.map_comp_map_le_comap hI _ _ _ _) ⁻¹'
        Set.range ⇑(diagChart R I q hI).base ⊆
      Set.range ⇑(spfGraphLiftYX R I q hI).base := by
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) :=
    annulus_isAdicRing R I q hI
  haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
    (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapY R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapX R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  rw [diagChart_base_eq]
  exact CompletedTensorProduct.preimage_range_codiagonal_subset_of_inr_iso hI
    (annulusIdealOfDefinition R I q) (annulusOverlapIdealY R I q)
    (annulusCodiagonal_le_comap R I q hI) _ _ (graphLiftYX R I q hI) _
    (fun m x hx => graphLiftYX_mem_pow R I q hI m hx) (overlapIdealY_eq_map R I q)
    (fun a =>
      (annulusFibreChartTransitionInvAlg R I q hI)
        (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
            (overlapX R I q)) a))
    (fun a => invLocXY R I q hI a)
    (chartBridgeY R I q)
    (fun a => by rw [RingHom.comp_apply, map_inl, map_inl]; rfl)
    (fun a => by rw [RingHom.comp_apply, map_inr, map_inr]; rfl)
    (fun a => graphLiftYX_inl R I q hI a) (fun z => graphLiftYX_inr R I q hI z)
    (fun a => chartBridgeY_transition_locX R I q hI a)

/-- **Mixed chart `(false, true)`, `c = false`, `dAX` summand.** -/
theorem preimage_range_diagChart_subset_second_dAX_y (hI : I.FG) :
    haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
      annulus_isAdicRing_map R I q hI
    haveI : IsAdicRing (annulusIdealOfDefinition R I q) :=
      annulus_isAdicRing R I q hI
    haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
      (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q))) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapY R I q))) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    FormalSpectrum.map
        (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))
        (idealOfDefinition R I
          (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
            (overlapX R I q)))
        ((map hI (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).toAlgHom
            (annulusFibreChartTransitionInvAlg R I q hI).symm.toAlgHom).comp
          (map hI (AlgHom.id R (annulusAlgebra R I q))
            (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
              (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
                (overlapY R I q)))))
        (CompletedTensorProduct.map_comp_map_le_comap hI _ _ _ _) ⁻¹'
        Set.range ⇑(diagChart R I q hI).base ⊆
      Set.range ⇑(spfGraphLiftAXtoY R I q hI).base := by
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) :=
    annulus_isAdicRing R I q hI
  haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
    (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapX R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapY R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  rw [diagChart_base_eq]
  exact CompletedTensorProduct.preimage_range_codiagonal_subset_of_inr_iso hI
    (annulusIdealOfDefinition R I q) (annulusOverlapIdealY R I q)
    (annulusCodiagonal_le_comap R I q hI) _ _ (graphLiftAXtoY R I q hI) _
    (fun m x hx => graphLiftAXtoY_mem_pow R I q hI m hx) (overlapIdealY_eq_map R I q)
    (fun a =>
      (annulusFibreChartTransitionInvAlg R I q hI).symm
        (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
            (overlapY R I q)) a))
    (fun a => algebraMap (annulusAlgebra R I q) (annulusOverlapY R I q) a)
    (graphChartAlgXY R I q hI)
    (fun a => by rw [RingHom.comp_apply, map_inl, map_inl]; rfl)
    (fun a => by rw [RingHom.comp_apply, map_inr, map_inr]; rfl)
    (fun a => graphLiftAXtoY_inl R I q hI a) (fun z => graphLiftAXtoY_inr R I q hI z)
    (fun a => graphChartAlgXY_transitionSymm_locY R I q hI a)

/-- **Mixed chart `(true, false)`, `c = true`, `dAX` summand.** -/
theorem preimage_range_diagChart_subset_second_dAX_x (hI : I.FG) :
    haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
      annulus_isAdicRing_map R I q hI
    haveI : IsAdicRing (annulusIdealOfDefinition R I q) :=
      annulus_isAdicRing R I q hI
    haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
      (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q))) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapY R I q))) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    FormalSpectrum.map
        (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))
        (idealOfDefinition R I
          (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
            (overlapX R I q)))
        ((map hI (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).toAlgHom
            (annulusFibreChartTransitionInvAlg R I q hI).symm.toAlgHom).comp
          (map hI (AlgHom.id R (annulusAlgebra R I q))
            (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
              (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
                (overlapY R I q)))))
        (CompletedTensorProduct.map_comp_map_le_comap hI _ _ _ _) ⁻¹'
        Set.range ⇑(diagChart R I q hI).base ⊆
      Set.range ⇑(spfGraphLiftAXtoX R I q hI).base := by
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) :=
    annulus_isAdicRing R I q hI
  haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
    (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapX R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapY R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  rw [diagChart_base_eq]
  exact CompletedTensorProduct.preimage_range_codiagonal_subset_of_inr_iso hI
    (annulusIdealOfDefinition R I q) (annulusOverlapIdeal R I q)
    (annulusCodiagonal_le_comap R I q hI) _ _ (graphLiftAXtoX R I q hI) _
    (fun m x hx => graphLiftAXtoX_mem_pow R I q hI m hx) (overlapIdeal_eq_map R I q)
    (fun a =>
      (annulusFibreChartTransitionInvAlg R I q hI).symm
        (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
            (overlapY R I q)) a))
    (fun a => invFlipLocX R I q hI a)
    (graphChartAlgX R I q)
    (fun a => by rw [RingHom.comp_apply, map_inl, map_inl]; rfl)
    (fun a => by rw [RingHom.comp_apply, map_inr, map_inr]; rfl)
    (fun a => graphLiftAXtoX_inl R I q hI a) (fun z => graphLiftAXtoX_inr R I q hI z)
    (fun a => graphChartAlgX_transitionSymm_locY R I q hI a)

/-- **Mixed chart `(false, true)`, `c = true`, `dYA` summand.** -/
theorem preimage_range_diagChart_subset_first_dYA_y (hI : I.FG) :
    haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
      annulus_isAdicRing_map R I q hI
    haveI : IsAdicRing (annulusIdealOfDefinition R I q) :=
      annulus_isAdicRing R I q hI
    haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
      (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapY R I q))
        (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q))
        (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    FormalSpectrum.map
        (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))
        (idealOfDefinition R I
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
            (overlapY R I q))
          (annulusAlgebra R I q))
        ((map hI (annulusFibreChartTransitionInvAlg R I q hI).toAlgHom
            (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).toAlgHom).comp
          (map hI (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
              (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
                (overlapX R I q)))
            (AlgHom.id R (annulusAlgebra R I q))))
        (CompletedTensorProduct.map_comp_map_le_comap hI _ _ _ _) ⁻¹'
        Set.range ⇑(diagChart R I q hI).base ⊆
      Set.range ⇑(spfGraphLiftY R I q hI).base := by
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) :=
    annulus_isAdicRing R I q hI
  haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
    (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapY R I q))
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapX R I q))
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  rw [diagChart_base_eq]
  exact CompletedTensorProduct.preimage_range_codiagonal_subset_of_inl_iso hI
    (annulusIdealOfDefinition R I q) (annulusOverlapIdealY R I q)
    (annulusCodiagonal_le_comap R I q hI) _ _ (graphLiftY R I q hI) _
    (fun m x hx => graphLiftY_mem_pow R I q hI m hx) (overlapIdealY_eq_map R I q)
    (fun a =>
      (annulusFibreChartTransitionInvAlg R I q hI)
        (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
            (overlapX R I q)) a))
    (fun a => invLocXY R I q hI a)
    (chartBridgeY R I q)
    (fun a => by rw [RingHom.comp_apply, map_inl, map_inl]; rfl)
    (fun a => by rw [RingHom.comp_apply, map_inr, map_inr]; rfl)
    (fun z => graphLiftY_inl R I q hI z) (fun a => graphLiftY_inr R I q hI a)
    (fun a => chartBridgeY_transition_locX R I q hI a)

/-- **Mixed chart `(true, false)`, `c = false`, `dYA` summand.** -/
theorem preimage_range_diagChart_subset_first_dYA_x (hI : I.FG) :
    haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
      annulus_isAdicRing_map R I q hI
    haveI : IsAdicRing (annulusIdealOfDefinition R I q) :=
      annulus_isAdicRing R I q hI
    haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
      (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapY R I q))
        (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q))
        (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    FormalSpectrum.map
        (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))
        (idealOfDefinition R I
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
            (overlapY R I q))
          (annulusAlgebra R I q))
        ((map hI (annulusFibreChartTransitionInvAlg R I q hI).toAlgHom
            (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).toAlgHom).comp
          (map hI (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
              (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
                (overlapX R I q)))
            (AlgHom.id R (annulusAlgebra R I q))))
        (CompletedTensorProduct.map_comp_map_le_comap hI _ _ _ _) ⁻¹'
        Set.range ⇑(diagChart R I q hI).base ⊆
      Set.range ⇑(spfGraphLiftXY R I q hI).base := by
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) :=
    annulus_isAdicRing R I q hI
  haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
    (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapY R I q))
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapX R I q))
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  rw [diagChart_base_eq]
  exact CompletedTensorProduct.preimage_range_codiagonal_subset_of_inl_iso hI
    (annulusIdealOfDefinition R I q) (annulusOverlapIdeal R I q)
    (annulusCodiagonal_le_comap R I q hI) _ _ (graphLiftXY R I q hI) _
    (fun m x hx => graphLiftXY_mem_pow R I q hI m hx) (overlapIdeal_eq_map R I q)
    (fun a =>
      (annulusFibreChartTransitionInvAlg R I q hI)
        (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
            (overlapX R I q)) a))
    (fun a => algebraMap (annulusAlgebra R I q) (annulusOverlap R I q) a)
    (graphChartAlgY R I q hI)
    (fun a => by rw [RingHom.comp_apply, map_inl, map_inl]; rfl)
    (fun a => by rw [RingHom.comp_apply, map_inr, map_inr]; rfl)
    (fun z => graphLiftXY_inl R I q hI z) (fun a => graphLiftXY_inr R I q hI a)
    (fun a => graphChartAlgY_transition_locX R I q hI a)

/-- **Mixed chart `(false, true)`, `c = true`, `dXA` summand.** -/
theorem preimage_range_diagChart_subset_first_dXA_x (hI : I.FG) :
    haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
      annulus_isAdicRing_map R I q hI
    haveI : IsAdicRing (annulusIdealOfDefinition R I q) :=
      annulus_isAdicRing R I q hI
    haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
      (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q))
        (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapY R I q))
        (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    FormalSpectrum.map
        (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))
        (idealOfDefinition R I
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
            (overlapX R I q))
          (annulusAlgebra R I q))
        ((map hI (annulusFibreChartTransitionInvAlg R I q hI).symm.toAlgHom
            (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).toAlgHom).comp
          (map hI (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
              (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
                (overlapY R I q)))
            (AlgHom.id R (annulusAlgebra R I q))))
        (CompletedTensorProduct.map_comp_map_le_comap hI _ _ _ _) ⁻¹'
        Set.range ⇑(diagChart R I q hI).base ⊆
      Set.range ⇑(spfGraphLiftXAtoX R I q hI).base := by
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) :=
    annulus_isAdicRing R I q hI
  haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
    (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapX R I q))
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapY R I q))
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  rw [diagChart_base_eq]
  exact CompletedTensorProduct.preimage_range_codiagonal_subset_of_inl_iso hI
    (annulusIdealOfDefinition R I q) (annulusOverlapIdeal R I q)
    (annulusCodiagonal_le_comap R I q hI) _ _ (graphLiftXAtoX R I q hI) _
    (fun m x hx => graphLiftXAtoX_mem_pow R I q hI m hx) (overlapIdeal_eq_map R I q)
    (fun a =>
      (annulusFibreChartTransitionInvAlg R I q hI).symm
        (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
            (overlapY R I q)) a))
    (fun a => invFlipLocX R I q hI a)
    (graphChartAlgX R I q)
    (fun a => by rw [RingHom.comp_apply, map_inl, map_inl]; rfl)
    (fun a => by rw [RingHom.comp_apply, map_inr, map_inr]; rfl)
    (fun z => graphLiftXAtoX_inl R I q hI z) (fun a => graphLiftXAtoX_inr R I q hI a)
    (fun a => graphChartAlgX_transitionSymm_locY R I q hI a)

/-- **Mixed chart `(true, false)`, `c = false`, `dXA` summand.** -/
theorem preimage_range_diagChart_subset_first_dXA_y (hI : I.FG) :
    haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
      annulus_isAdicRing_map R I q hI
    haveI : IsAdicRing (annulusIdealOfDefinition R I q) :=
      annulus_isAdicRing R I q hI
    haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
      (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q))
        (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapY R I q))
        (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    FormalSpectrum.map
        (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))
        (idealOfDefinition R I
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
            (overlapX R I q))
          (annulusAlgebra R I q))
        ((map hI (annulusFibreChartTransitionInvAlg R I q hI).symm.toAlgHom
            (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).toAlgHom).comp
          (map hI (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
              (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
                (overlapY R I q)))
            (AlgHom.id R (annulusAlgebra R I q))))
        (CompletedTensorProduct.map_comp_map_le_comap hI _ _ _ _) ⁻¹'
        Set.range ⇑(diagChart R I q hI).base ⊆
      Set.range ⇑(spfGraphLiftXAtoY R I q hI).base := by
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) :=
    annulus_isAdicRing R I q hI
  haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
    (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapX R I q))
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapY R I q))
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  rw [diagChart_base_eq]
  exact CompletedTensorProduct.preimage_range_codiagonal_subset_of_inl_iso hI
    (annulusIdealOfDefinition R I q) (annulusOverlapIdealY R I q)
    (annulusCodiagonal_le_comap R I q hI) _ _ (graphLiftXAtoY R I q hI) _
    (fun m x hx => graphLiftXAtoY_mem_pow R I q hI m hx) (overlapIdealY_eq_map R I q)
    (fun a =>
      (annulusFibreChartTransitionInvAlg R I q hI).symm
        (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
            (overlapY R I q)) a))
    (fun a => algebraMap (annulusAlgebra R I q) (annulusOverlapY R I q) a)
    (graphChartAlgXY R I q hI)
    (fun a => by rw [RingHom.comp_apply, map_inl, map_inl]; rfl)
    (fun a => by rw [RingHom.comp_apply, map_inr, map_inr]; rfl)
    (fun z => graphLiftXAtoY_inl R I q hI z) (fun a => graphLiftXAtoY_inr R I q hI a)
    (fun a => graphChartAlgXY_transitionSymm_locY R I q hI a)


/-! ### The four transition composites as `Spf` of the corresponding ring map -/

/-- The `dAY`-summand transition composite of the second-factor overlap, as `Spf` of `φ`. -/
theorem spfSecondTransitionDAY_eq (hI : I.FG) :
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    (rightSummandInv R I q hI).inv ≫
        rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapX R I q) hI =
      FormalSpectrum.locallyRingedSpaceMap
        (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))
        (idealOfDefinition R I (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))
        ((map hI (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).toAlgHom
            (annulusFibreChartTransitionInvAlg R I q hI).toAlgHom).comp
          (map hI (AlgHom.id R (annulusAlgebra R I q))
            (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
              (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))))
        (CompletedTensorProduct.map_comp_map_le_comap hI _ _ _ _) := by
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  rw [rightInterchangeOpenImmersion_eq_mapSpf, CompletedTensorProduct.mapSpf_eq,
    rightSummandInv, CompletedTensorProduct.mapSpfIso_inv, CompletedTensorProduct.mapSpf_eq,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (hIK := CompletedTensorProduct.map_comp_map_le_comap hI _ _ _ _)]

/-- The `dAX`-summand transition composite of the second-factor overlap, as `Spf` of `φ`. -/
theorem spfSecondTransitionDAX_eq (hI : I.FG) :
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    (rightSummandInv R I q hI).hom ≫
        rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapY R I q) hI =
      FormalSpectrum.locallyRingedSpaceMap
        (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))
        (idealOfDefinition R I (annulusAlgebra R I q)
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))
        ((map hI (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).toAlgHom
            (annulusFibreChartTransitionInvAlg R I q hI).symm.toAlgHom).comp
          (map hI (AlgHom.id R (annulusAlgebra R I q))
            (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
              (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))))
        (CompletedTensorProduct.map_comp_map_le_comap hI _ _ _ _) := by
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  rw [rightInterchangeOpenImmersion_eq_mapSpf, CompletedTensorProduct.mapSpf_eq,
    rightSummandInv, CompletedTensorProduct.mapSpfIso_hom, AlgEquiv.refl_symm,
    CompletedTensorProduct.mapSpf_eq,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (hIK := CompletedTensorProduct.map_comp_map_le_comap hI _ _ _ _)]

/-- The `dYA`-summand transition composite of the first-factor overlap, as `Spf` of `φ`. -/
theorem spfFirstTransitionDYA_eq (hI : I.FG) :
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
        (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
        (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    (firstSummandInv R I q hI).inv ≫
        interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapX R I q) hI =
      FormalSpectrum.locallyRingedSpaceMap
        (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))
        (idealOfDefinition R I
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
          (annulusAlgebra R I q))
        ((map hI (annulusFibreChartTransitionInvAlg R I q hI).toAlgHom
            (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).toAlgHom).comp
          (map hI (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
              (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q)))
            (AlgHom.id R (annulusAlgebra R I q))))
        (CompletedTensorProduct.map_comp_map_le_comap hI _ _ _ _) := by
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  rw [interchangeOpenImmersion_eq_mapSpf, CompletedTensorProduct.mapSpf_eq,
    firstSummandInv, twoPatchFibreProductInvTransition,
    CompletedTensorProduct.mapSpfIso_inv, CompletedTensorProduct.mapSpf_eq,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (hIK := CompletedTensorProduct.map_comp_map_le_comap hI _ _ _ _)]

/-- The `dXA`-summand transition composite of the first-factor overlap, as `Spf` of `φ`. -/
theorem spfFirstTransitionDXA_eq (hI : I.FG) :
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
        (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
        (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    (firstSummandInv R I q hI).hom ≫
        interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapY R I q) hI =
      FormalSpectrum.locallyRingedSpaceMap
        (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))
        (idealOfDefinition R I
          (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
          (annulusAlgebra R I q))
        ((map hI (annulusFibreChartTransitionInvAlg R I q hI).symm.toAlgHom
            (AlgEquiv.refl (R := R) (A₁ := annulusAlgebra R I q)).toAlgHom).comp
          (map hI (IsScalarTower.toAlgHom R (annulusAlgebra R I q)
              (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q)))
            (AlgHom.id R (annulusAlgebra R I q))))
        (CompletedTensorProduct.map_comp_map_le_comap hI _ _ _ _) := by
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapY R I q))
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q))) (overlapX R I q))
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  rw [interchangeOpenImmersion_eq_mapSpf, CompletedTensorProduct.mapSpf_eq,
    firstSummandInv, twoPatchFibreProductInvTransition,
    CompletedTensorProduct.mapSpfIso_hom, AlgEquiv.refl_symm,
    CompletedTensorProduct.mapSpf_eq,
    ← FormalSpectrum.locallyRingedSpaceMap_comp
      (hIK := CompletedTensorProduct.map_comp_map_le_comap hI _ _ _ _)]

/-! ### Geometric forms of the eight bounds -/

/-- **Geometric form** for the mixed
chart `(false, true)`, `c = false`, `dAY` summand: the preimage of the
affine diagonal locus under that summand's transition composite lies in the range of its graph
lift. -/
theorem spfPreimage_range_diagChart_subset_second_dAY_x (hI : I.FG) :
    haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
      annulus_isAdicRing_map R I q hI
    haveI : IsAdicRing (annulusIdealOfDefinition R I q) :=
      annulus_isAdicRing R I q hI
    haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
      (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapY R I q))) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q))) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    ⇑((rightSummandInv R I q hI).inv ≫
        rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapX R I q) hI).base ⁻¹'
        Set.range ⇑(diagChart R I q hI).base ⊆
      Set.range ⇑(spfGraphLiftX R I q hI).base := by
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) :=
    annulus_isAdicRing R I q hI
  haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
    (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapY R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapX R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  rw [spfSecondTransitionDAY_eq]
  exact preimage_range_diagChart_subset_second_dAY_x R I q hI

/-- **Geometric form** for the mixed
chart `(true, false)`, `c = true`, `dAY` summand: the preimage of the
affine diagonal locus under that summand's transition composite lies in the range of its graph
lift. -/
theorem spfPreimage_range_diagChart_subset_second_dAY_y (hI : I.FG) :
    haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
      annulus_isAdicRing_map R I q hI
    haveI : IsAdicRing (annulusIdealOfDefinition R I q) :=
      annulus_isAdicRing R I q hI
    haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
      (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapY R I q))) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q))) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    ⇑((rightSummandInv R I q hI).inv ≫
        rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapX R I q) hI).base ⁻¹'
        Set.range ⇑(diagChart R I q hI).base ⊆
      Set.range ⇑(spfGraphLiftYX R I q hI).base := by
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) :=
    annulus_isAdicRing R I q hI
  haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
    (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapY R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapX R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  rw [spfSecondTransitionDAY_eq]
  exact preimage_range_diagChart_subset_second_dAY_y R I q hI

/-- **Geometric form** for the mixed
chart `(false, true)`, `c = false`, `dAX` summand: the preimage of the
affine diagonal locus under that summand's transition composite lies in the range of its graph
lift. -/
theorem spfPreimage_range_diagChart_subset_second_dAX_y (hI : I.FG) :
    haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
      annulus_isAdicRing_map R I q hI
    haveI : IsAdicRing (annulusIdealOfDefinition R I q) :=
      annulus_isAdicRing R I q hI
    haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
      (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q))) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapY R I q))) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    ⇑((rightSummandInv R I q hI).hom ≫
        rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapY R I q) hI).base ⁻¹'
        Set.range ⇑(diagChart R I q hI).base ⊆
      Set.range ⇑(spfGraphLiftAXtoY R I q hI).base := by
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) :=
    annulus_isAdicRing R I q hI
  haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
    (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapX R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapY R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  rw [spfSecondTransitionDAX_eq]
  exact preimage_range_diagChart_subset_second_dAX_y R I q hI

/-- **Geometric form** for the mixed
chart `(true, false)`, `c = true`, `dAX` summand: the preimage of the
affine diagonal locus under that summand's transition composite lies in the range of its graph
lift. -/
theorem spfPreimage_range_diagChart_subset_second_dAX_x (hI : I.FG) :
    haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
      annulus_isAdicRing_map R I q hI
    haveI : IsAdicRing (annulusIdealOfDefinition R I q) :=
      annulus_isAdicRing R I q hI
    haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
      (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q))) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (annulusAlgebra R I q)
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapY R I q))) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    ⇑((rightSummandInv R I q hI).hom ≫
        rightInterchangeOpenImmersion (A := annulusAlgebra R I q) I (overlapY R I q) hI).base ⁻¹'
        Set.range ⇑(diagChart R I q hI).base ⊆
      Set.range ⇑(spfGraphLiftAXtoX R I q hI).base := by
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) :=
    annulus_isAdicRing R I q hI
  haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
    (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapX R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (annulusAlgebra R I q)
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapY R I q))) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  rw [spfSecondTransitionDAX_eq]
  exact preimage_range_diagChart_subset_second_dAX_x R I q hI

/-- **Geometric form** for the mixed
chart `(false, true)`, `c = true`, `dYA` summand: the preimage of the
affine diagonal locus under that summand's transition composite lies in the range of its graph
lift. -/
theorem spfPreimage_range_diagChart_subset_first_dYA_y (hI : I.FG) :
    haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
      annulus_isAdicRing_map R I q hI
    haveI : IsAdicRing (annulusIdealOfDefinition R I q) :=
      annulus_isAdicRing R I q hI
    haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
      (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapY R I q))
        (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q))
        (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    ⇑((firstSummandInv R I q hI).inv ≫
        interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapX R I q) hI).base ⁻¹'
        Set.range ⇑(diagChart R I q hI).base ⊆
      Set.range ⇑(spfGraphLiftY R I q hI).base := by
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) :=
    annulus_isAdicRing R I q hI
  haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
    (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapY R I q))
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapX R I q))
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  rw [spfFirstTransitionDYA_eq]
  exact preimage_range_diagChart_subset_first_dYA_y R I q hI

/-- **Geometric form** for the mixed
chart `(true, false)`, `c = false`, `dYA` summand: the preimage of the
affine diagonal locus under that summand's transition composite lies in the range of its graph
lift. -/
theorem spfPreimage_range_diagChart_subset_first_dYA_x (hI : I.FG) :
    haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
      annulus_isAdicRing_map R I q hI
    haveI : IsAdicRing (annulusIdealOfDefinition R I q) :=
      annulus_isAdicRing R I q hI
    haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
      (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapY R I q))
        (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q))
        (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    ⇑((firstSummandInv R I q hI).inv ≫
        interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapX R I q) hI).base ⁻¹'
        Set.range ⇑(diagChart R I q hI).base ⊆
      Set.range ⇑(spfGraphLiftXY R I q hI).base := by
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) :=
    annulus_isAdicRing R I q hI
  haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
    (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapY R I q))
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapX R I q))
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  rw [spfFirstTransitionDYA_eq]
  exact preimage_range_diagChart_subset_first_dYA_x R I q hI

/-- **Geometric form** for the mixed
chart `(false, true)`, `c = true`, `dXA` summand: the preimage of the
affine diagonal locus under that summand's transition composite lies in the range of its graph
lift. -/
theorem spfPreimage_range_diagChart_subset_first_dXA_x (hI : I.FG) :
    haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
      annulus_isAdicRing_map R I q hI
    haveI : IsAdicRing (annulusIdealOfDefinition R I q) :=
      annulus_isAdicRing R I q hI
    haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
      (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q))
        (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapY R I q))
        (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    ⇑((firstSummandInv R I q hI).hom ≫
        interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapY R I q) hI).base ⁻¹'
        Set.range ⇑(diagChart R I q hI).base ⊆
      Set.range ⇑(spfGraphLiftXAtoX R I q hI).base := by
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) :=
    annulus_isAdicRing R I q hI
  haveI : IsAdicRing (annulusOverlapIdeal R I q) := annulusOverlap_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
    (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapX R I q))
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapY R I q))
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  rw [spfFirstTransitionDXA_eq]
  exact preimage_range_diagChart_subset_first_dXA_x R I q hI

/-- **Geometric form** for the mixed
chart `(true, false)`, `c = false`, `dXA` summand: the preimage of the
affine diagonal locus under that summand's transition composite lies in the range of its graph
lift. -/
theorem spfPreimage_range_diagChart_subset_first_dXA_y (hI : I.FG) :
    haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
      annulus_isAdicRing_map R I q hI
    haveI : IsAdicRing (annulusIdealOfDefinition R I q) :=
      annulus_isAdicRing R I q hI
    haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
    haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
      (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapX R I q))
        (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    haveI : IsAdicRing (idealOfDefinition R I
        (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
          (overlapY R I q))
        (annulusAlgebra R I q)) :=
      CompletedTensorProduct.isAdicRing R I _ _ hI
    ⇑((firstSummandInv R I q hI).hom ≫
        interchangeOpenImmersion (B := annulusAlgebra R I q) I (overlapY R I q) hI).base ⁻¹'
        Set.range ⇑(diagChart R I q hI).base ⊆
      Set.range ⇑(spfGraphLiftXAtoY R I q hI).base := by
  haveI : IsAdicRing (I.map (algebraMap R (annulusAlgebra R I q))) :=
    annulus_isAdicRing_map R I q hI
  haveI : IsAdicRing (annulusIdealOfDefinition R I q) :=
    annulus_isAdicRing R I q hI
  haveI : IsAdicRing (annulusOverlapIdealY R I q) := annulusOverlapY_isAdicRing R I q hI
  haveI : IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q)
    (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapX R I q))
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  haveI : IsAdicRing (idealOfDefinition R I
      (awayCompletion (I.map (algebraMap R (annulusAlgebra R I q)))
        (overlapY R I q))
      (annulusAlgebra R I q)) :=
    CompletedTensorProduct.isAdicRing R I _ _ hI
  rw [spfFirstTransitionDXA_eq]
  exact preimage_range_diagChart_subset_first_dXA_y R I q hI


end AlgebraicGeometry
