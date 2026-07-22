import FormalSchemes.BasicOpenChartComponent

set_option linter.style.header false

/-!
# Towards the open immersion property of the affine basic-open chart

For an adic ring `(R, I)` with `I.FG` and `f : R`, the affine basic-open chart
`Spf R{1/f} ⟶ Spf R` (`FormalSchemes/BasicOpenChart.lean`) is expected to be a
`LocallyRingedSpace.IsOpenImmersion`. The underlying map is an open topological embedding with
range `D(f)` (`FormalSpectrum.isOpenEmbedding_basicOpenChartBase`,
`FormalSpectrum.range_basicOpenChartBase`); the remaining ingredient is the `c_iso` field, i.e.
the sheaf component of the chart is an isomorphism on the basis of basic opens `D(g) ⊆ D(f)`.

This file provides the level-`n` matching lemma that identifies the chart's sheaf component on a
basic open `D(g) ⊆ D(f)`, read through the sections identifications
`FormalSpectrum.sectionsBasicOpenEquiv`, with the already-merged algebraic isomorphism
`FormalSpectrum.awayCompletionChartEquiv` (`R{1/g} ≃+* R{1/f}{1/ḡ}`,
`FormalSchemes/AwayCompletionInterchange.lean`).

## Main results

* `AdicCompletion.evalₐ_mapCompletion`: the general functoriality rule `evalₐ ∘ mapCompletion =
  quotientMap ∘ evalₐ`; the level-`n` component of a completed ring map is the induced map of
  quotients.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace AdicCompletion

variable {R S : Type u} [CommRing R] [CommRing S] {I : Ideal R} {J : Ideal S}

/-- The level-`n` component `evalₐ` of the completed ring map `mapCompletion f` is the induced
map of quotients `Ideal.quotientMap`: completion is functorial and compatible with the
truncations `R ⧸ I ^ n`. Both `I` and `J` are finitely generated so that the completions are
complete and the level maps determine the completed map. -/
theorem evalₐ_mapCompletion (f : R →+* S) (hf : I.map f ≤ J) (hJ : J.FG) (hI : I.FG) (n : ℕ)
    (hc : I ^ n ≤ (J ^ n).comap f) (x : AdicCompletion I R) :
    evalₐ J n (mapCompletion f hf hJ x) =
      Ideal.quotientMap (J ^ n) f hc (evalₐ I n x) := by
  -- represent the level-`n` component of `x` by an element `b : R`
  obtain ⟨b, hb⟩ := Submodule.mkQ_surjective (I ^ n • ⊤ : Submodule R R) (eval I R n x)
  have heval0 : eval I R n (x - AdicCompletion.of I R b) = 0 := by
    rw [map_sub, eval_of, hb, sub_self]
  have hker : x - AdicCompletion.of I R b ∈ (I ^ n • ⊤ : Submodule R (AdicCompletion I R)) := by
    rw [pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker]
    exact heval0
  -- hence `evalₐ I n x = mk b`
  have hevalₐ : evalₐ I n x = Ideal.Quotient.mk (I ^ n) b := by
    have h0 : evalₐ I n (x - AdicCompletion.of I R b) = 0 := by
      rw [← factor_eval_eq_evalₐ I (x - AdicCompletion.of I R b)
        (by simp : (I ^ n • ⊤ : Ideal R) ≤ I ^ n), heval0]
      exact _root_.map_zero _
    rw [map_sub, evalₐ_of, sub_eq_zero] at h0
    exact h0
  -- the target level component of the tail vanishes
  have htail : evalₐ J n (mapCompletion f hf hJ (x - AdicCompletion.of I R b)) = 0 := by
    have hmem : mapCompletion f hf hJ (x - AdicCompletion.of I R b) ∈ (idealOfDefinition J) ^ n :=
      mapCompletion_mem_pow f hf hJ hI n hker
    rw [mem_idealOfDefinition_pow_iff, pow_smul_top_eq_ker_eval hJ, LinearMap.mem_ker] at hmem
    rw [← factor_eval_eq_evalₐ J _ (by simp : (J ^ n • ⊤ : Ideal S) ≤ J ^ n), hmem]
    exact _root_.map_zero _
  -- assemble
  have hsplit : evalₐ J n (mapCompletion f hf hJ x) =
      evalₐ J n (mapCompletion f hf hJ (AdicCompletion.of I R b)) := by
    have := htail
    rw [map_sub, map_sub, sub_eq_zero] at this
    exact this
  rw [hsplit, mapCompletion_of, AdicCompletion.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, evalₐ_of, hevalₐ, Ideal.quotientMap_mk]

end AdicCompletion
