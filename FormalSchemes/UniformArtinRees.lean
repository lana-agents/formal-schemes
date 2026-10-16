/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.RestrictedPowerSeriesNoetherian
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Filtration

/-!
# A uniform Artin–Rees lemma for inverse systems of submodules

Let `R` be Noetherian, `J ⊆ R` an ideal, `V` a finite `R`-module, and let `Sₙ ⊆ V / Jⁿ V` be
submodules compatible under the reduction maps, with `S_{n'} → Sₙ` surjective for `n ≤ n'`.
Then there is `c` such that for all `c ≤ m ≤ m'`,
`S_{m'} ∩ Jᵐ (V / J^{m'} V) ⊆ J^{m-c} S_{m'}` (`uniform_artinRees`).

This is the Artin–Rees lemma for the submodule `Ŝ = lim Sₙ` of the completion `V̂`, a finite module
over the Noetherian ring `R̂` (`AdicCompletion.isNoetherianRing`, Atiyah–Macdonald 10.26), pushed
down to the finite levels using `ker (V̂ → V / Jⁿ V) = Jⁿ V̂` (Stacks, Lemma 10.96.3, Tag 05GG). It
is the input to the abelianness of the category of coherent formal modules (Stacks, Lemma 30.23.2,
Tag 087X), i.e. to kernels of morphisms of adic systems.
-/

universe u

open Submodule

namespace FormalSchemes.UniformArtinRees

variable {R : Type u} [CommRing R] (J : Ideal R) {V : Type u} [AddCommGroup V] [Module R V]

/-- A compatible system of submodules of the reductions of `V`, with surjective transitions. -/
structure System where
  /-- the submodule at level `n` -/
  S : ∀ n : ℕ, Submodule R (V ⧸ (J ^ n • ⊤ : Submodule R V))
  map_eq : ∀ {n n' : ℕ} (h : n ≤ n'), (S n').map (factorPow J V h) = S n

variable {J}

/-- The limit `Ŝ = lim Sₙ`, a submodule of the completion over `R̂`. -/
def System.lim (S : System J (V := V)) : Submodule (AdicCompletion J R) (AdicCompletion J V) where
  carrier := {v | ∀ n, v.val n ∈ S.S n}
  add_mem' hv hw n := add_mem (hv n) (hw n)
  zero_mem' n := zero_mem _
  smul_mem' r v hv n := by
    change r.val n • v.val n ∈ S.S n
    obtain ⟨r', hr'⟩ := Submodule.Quotient.mk_surjective _ (r.val n)
    rw [← hr']
    exact (S.S n).smul_mem r' (hv n)

lemma mk_mem_of_le (S : System J (V := V)) {n n' : ℕ} (h : n ≤ n') {v : V}
    (hv : (Submodule.Quotient.mk v : V ⧸ (J ^ n' • ⊤ : Submodule R V)) ∈ S.S n') :
    (Submodule.Quotient.mk v : V ⧸ (J ^ n • ⊤ : Submodule R V)) ∈ S.S n := by
  rw [← S.map_eq h]
  exact ⟨_, hv, rfl⟩

lemma exists_lift_step (S : System J (V := V)) (k : ℕ) (w : V)
    (hw : (Submodule.Quotient.mk w : V ⧸ (J ^ k • ⊤ : Submodule R V)) ∈ S.S k) :
    ∃ v : V, (Submodule.Quotient.mk v : V ⧸ (J ^ (k + 1) • ⊤ : Submodule R V)) ∈ S.S (k + 1) ∧
      v - w ∈ (J ^ k • ⊤ : Submodule R V) := by
  rw [← S.map_eq (Nat.le_succ k)] at hw
  obtain ⟨s, hs, hsw⟩ := hw
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ s
  refine ⟨v, hs, ?_⟩
  rw [← Submodule.Quotient.eq]
  exact hsw

/-- **Lifting to the limit**: every element of `S_{m'}` comes from `Ŝ`. -/
lemma exists_lim_lift (S : System J (V := V)) (m' : ℕ) (x : V ⧸ (J ^ m' • ⊤ : Submodule R V))
    (hx : x ∈ S.S m') : ∃ v ∈ S.lim, v.val m' = x := by
  classical
  obtain ⟨x0, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  -- lifts at the levels `m' + j`
  let step : ∀ j : ℕ, {v : V // (Submodule.Quotient.mk v :
      V ⧸ (J ^ (m' + j) • ⊤ : Submodule R V)) ∈ S.S (m' + j)} →
      {v : V // (Submodule.Quotient.mk v :
        V ⧸ (J ^ (m' + (j + 1)) • ⊤ : Submodule R V)) ∈ S.S (m' + (j + 1))} :=
    fun j w ↦ ⟨(exists_lift_step S (m' + j) w.1 w.2).choose,
      (exists_lift_step S (m' + j) w.1 w.2).choose_spec.1⟩
  let u : ∀ j : ℕ, {v : V // (Submodule.Quotient.mk v :
      V ⧸ (J ^ (m' + j) • ⊤ : Submodule R V)) ∈ S.S (m' + j)} :=
    fun j ↦ Nat.rec ⟨x0, hx⟩ (fun j w ↦ step j w) j
  have hu : ∀ j, ((u (j + 1)).1 - (u j).1) ∈ (J ^ (m' + j) • ⊤ : Submodule R V) := fun j ↦
    (exists_lift_step S (m' + j) (u j).1 (u j).2).choose_spec.2
  have hu' : ∀ j j', j ≤ j' → ((u j').1 - (u j).1) ∈ (J ^ (m' + j) • ⊤ : Submodule R V) := by
    intro j j' hjj'
    induction j', hjj' using Nat.le_induction with
    | base => simp
    | succ j' hj' ih =>
      have := Submodule.smul_mono_left (Ideal.pow_le_pow_right (show m' + j ≤ m' + j' by omega))
        (hu j')
      rw [show (u (j' + 1)).1 - (u j).1 = ((u (j' + 1)).1 - (u j').1) + ((u j').1 - (u j).1) by
        abel]
      exact add_mem this ih
  let seq : ℕ → V := fun n ↦ (u (n - m')).1
  have hseq : AdicCompletion.IsAdicCauchy J V seq := by
    intro n n' hnn'
    rw [SModEq.sub_mem, ← neg_sub]
    refine neg_mem (Submodule.smul_mono_left (Ideal.pow_le_pow_right ?_)
      (hu' (n - m') (n' - m') (by omega)))
    omega
  refine ⟨AdicCompletion.mk J V ⟨seq, hseq⟩, fun n ↦ ?_, ?_⟩
  · change (Submodule.Quotient.mk (seq n) : V ⧸ (J ^ n • ⊤ : Submodule R V)) ∈ S.S n
    rcases le_or_gt m' n with h | h
    · obtain ⟨j, rfl⟩ : ∃ j, n = m' + j := ⟨n - m', by omega⟩
      change (Submodule.Quotient.mk (u (m' + j - m')).1 :
        V ⧸ (J ^ (m' + j) • ⊤ : Submodule R V)) ∈ S.S (m' + j)
      have key : ∀ k a, k = m' + a → (Submodule.Quotient.mk (u a).1 :
          V ⧸ (J ^ k • ⊤ : Submodule R V)) ∈ S.S k := by
        rintro k a rfl
        exact (u a).2
      exact key _ _ (by omega)
    · have : seq n = x0 := by
        change (u (n - m')).1 = x0
        rw [show n - m' = 0 by omega]
        rfl
      rw [this]
      exact mk_mem_of_le S h.le hx
  · change (Submodule.Quotient.mk (u (m' - m')).1 : V ⧸ (J ^ m' • ⊤ : Submodule R V)) = _
    rw [Nat.sub_self]
    rfl

/-- **Uniform Artin–Rees for an inverse system of submodules.** -/
theorem uniform_artinRees [IsNoetherianRing R] [Module.Finite R V] (S : System J (V := V)) :
    ∃ c : ℕ, ∀ m m', c ≤ m → m ≤ m' → ∀ x ∈ S.S m',
      x ∈ (J ^ m • ⊤ : Submodule R (V ⧸ (J ^ m' • ⊤ : Submodule R V))) →
      x ∈ J ^ (m - c) • S.S m' := by
  have hJ : J.FG := (IsNoetherian.noetherian J)
  haveI : IsNoetherianRing (AdicCompletion J R) := AdicCompletion.isNoetherianRing J hJ
  haveI : Module.Finite (AdicCompletion J R) (AdicCompletion J V) :=
    Module.Finite.of_surjective (AdicCompletion.ofTensorProduct J V)
      (AdicCompletion.ofTensorProduct_surjective_of_finite J V)
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul
    (J.map (algebraMap R (AdicCompletion J R))) S.lim
  refine ⟨c, fun m m' hm hmm' x hxS hx ↦ ?_⟩
  obtain ⟨v, hvS, hvx⟩ := exists_lim_lift S m' x hxS
  have hv1 : v ∈ (J ^ m • ⊤ : Submodule R (AdicCompletion J V)) := by
    have hmap : (J ^ m • ⊤ : Submodule R (AdicCompletion J V)).map (AdicCompletion.eval J V m') =
        J ^ m • ⊤ := by
      rw [Submodule.map_smul'', Submodule.map_top, AdicCompletion.range_eval]
    rw [← hmap] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have hker : v - y ∈ (J ^ m' • ⊤ : Submodule R (AdicCompletion J V)) := by
      rw [AdicCompletion.pow_smul_top_eq_ker_eval hJ, LinearMap.mem_ker, map_sub, hyx]
      change v.val m' - x = 0
      rw [hvx, sub_self]
    have := add_mem (Submodule.smul_mono_left (Ideal.pow_le_pow_right hmm') hker) hy
    rwa [sub_add_cancel] at this
  have hv2 : v ∈ (J.map (algebraMap R (AdicCompletion J R))) ^ m •
      (⊤ : Submodule (AdicCompletion J R) (AdicCompletion J V)) := by
    rw [← Submodule.restrictScalars_mem R, ← Ideal.map_pow, Ideal.smul_restrictScalars,
      Submodule.restrictScalars_top]
    exact hv1
  have hv3 : v ∈ (J.map (algebraMap R (AdicCompletion J R))) ^ (m - c) • S.lim := by
    have h := hc m hm ▸ (show v ∈ _ ⊓ S.lim from ⟨hv2, hvS⟩)
    exact Submodule.smul_mono le_rfl inf_le_right h
  rw [← Submodule.restrictScalars_mem R, ← Ideal.map_pow, Ideal.smul_restrictScalars] at hv3
  have h4 := Submodule.mem_map_of_mem (f := AdicCompletion.eval J V m') hv3
  rw [Submodule.map_smul''] at h4
  have h5 : (S.lim.restrictScalars R).map (AdicCompletion.eval J V m') ≤ S.S m' := by
    rintro _ ⟨w, hw, rfl⟩
    exact hw m'
  rw [← hvx]
  exact Submodule.smul_mono le_rfl h5 h4

end FormalSchemes.UniformArtinRees
