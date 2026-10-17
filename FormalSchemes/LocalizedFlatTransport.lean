/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.RingTheory.Flat.Localization

/-!
# Flatness at a prime, across a principal localization

Two facts used to glue flatness over the two charts of `ℙ¹_A`:

* `LocalFlatness.flat_localizedModule_of_le`: flatness at a prime passes to its generizations
  (if `M` is flat at `q` and `p ⊆ q`, then `M` is flat at `p`).
* `LocalFlatness.flat_localizedModule_iff`: let `L = R[1/r]`, `W` an `L`-module and `N → W` a
  localization at `r` of `R`-modules (`N_r = W`). For a prime `P` of `L` with preimage `p` in `R`,
  `N` localized at `p` is flat over `R` iff `W` localized at `P` is flat over `L`. This makes
  flatness at a point of an overlap `Spec L` independent of the chart `Spec R` through which it
  is computed.
-/

universe u

namespace LocalFlatness

/-- **Flatness at a prime passes to generizations.** -/
theorem flat_localizedModule_of_le {R M : Type u} [CommRing R] [AddCommGroup M] [Module R M]
    (p q : Ideal R) [p.IsPrime] [q.IsPrime] (h : p ≤ q)
    (hq : Module.Flat R (LocalizedModule q.primeCompl M)) :
    Module.Flat R (LocalizedModule p.primeCompl M) := by
  have hle : q.primeCompl ≤ p.primeCompl := fun x hx hxp ↦ hx (h hxp)
  have : Module.Flat (Localization.AtPrime p) (LocalizedModule p.primeCompl M) :=
    Module.Flat.of_isLocalizedModule (Localization.AtPrime p) p.primeCompl
      (IsLocalizedModule.liftOfLE q.primeCompl p.primeCompl hle
        (LocalizedModule.mkLinearMap q.primeCompl M) (LocalizedModule.mkLinearMap p.primeCompl M))
  have : Module.Flat R (Localization.AtPrime p) := IsLocalization.flat _ p.primeCompl
  exact Module.Flat.trans R (Localization.AtPrime p) _

section Transport

variable {R L : Type u} [CommRing R] [CommRing L] [Algebra R L] (r : R)
  [IsLocalization.Away r L] {N W : Type u} [AddCommGroup N] [Module R N] [AddCommGroup W]
  [Module L W] [Module R W] [IsScalarTower R L W] (g : N →ₗ[R] W) [IsLocalizedModule.Away r g]
  (P : Ideal L) [hP : P.IsPrime]

include r in
lemma algebraMap_pow_notMem (k : ℕ) : algebraMap R L (r ^ k) ∉ P := fun h ↦
  hP.ne_top (Ideal.eq_top_of_isUnit_mem _ h
    (IsLocalization.map_units L (⟨r ^ k, k, rfl⟩ : Submonoid.powers r)))

include r in
/-- `N → W → W[P⁻¹]` is a localization of `R`-modules at the preimage of `P` (with the
`R`-module structure of the target through `L`). -/
lemma isLocalizedModule_comp :
    IsLocalizedModule (P.comap (algebraMap R L)).primeCompl
      (((LocalizedModule.mkLinearMap P.primeCompl W).restrictScalars R) ∘ₗ g) := by
  have hsm : ∀ (x : R) (m : LocalizedModule P.primeCompl W), x • m = algebraMap R L x • m :=
    fun x m ↦ (algebraMap_smul L x m).symm
  constructor
  · rintro ⟨s, hs⟩
    rw [Module.End.isUnit_iff]
    have := (Module.End.isUnit_iff _).1 (IsLocalizedModule.map_units
      (LocalizedModule.mkLinearMap P.primeCompl W) (⟨algebraMap R L s, hs⟩ : P.primeCompl))
    convert this using 1
    funext m
    exact hsm s m
  · intro y
    induction y using LocalizedModule.induction_on with
    | h w σ =>
      obtain ⟨⟨n, ⟨_, k, rfl⟩⟩, hn⟩ := IsLocalizedModule.surj (Submonoid.powers r) g w
      obtain ⟨⟨a, ⟨_, j, rfl⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers r) (σ : L)
      simp only at hn ha
      have haP : algebraMap R L a ∉ P := by
        rw [← ha]
        exact fun hm ↦ (hP.mem_or_mem hm).elim σ.2 (algebraMap_pow_notMem r P j)
      refine ⟨⟨r ^ j • n, ⟨r ^ k * a, ?_⟩⟩, ?_⟩
      · change algebraMap R L (r ^ k * a) ∉ P
        rw [map_mul]
        exact fun hm ↦ (hP.mem_or_mem hm).elim (algebraMap_pow_notMem r P k) haP
      · change (r ^ k * a) • LocalizedModule.mk w σ = LocalizedModule.mk (g (r ^ j • n)) 1
        rw [hsm, LocalizedModule.smul'_mk, LocalizedModule.mk_eq]
        refine ⟨1, ?_⟩
        have hn' : (r ^ k : R) • w = g n := hn
        rw [map_smul, ← hn', one_smul, one_smul, Submonoid.smul_def, Submonoid.smul_def,
          OneMemClass.coe_one, one_smul, ← algebraMap_smul L (r ^ j), ← algebraMap_smul L (r ^ k),
          smul_smul, smul_smul, ha, map_mul, mul_comm]
  · intro x₁ x₂ hx
    change LocalizedModule.mk (g x₁) 1 = LocalizedModule.mk (g x₂) 1 at hx
    obtain ⟨u, hu⟩ := LocalizedModule.mk_eq.1 hx
    simp only [one_smul] at hu
    obtain ⟨⟨a, ⟨_, j, rfl⟩⟩, ha⟩ := IsLocalization.surj (Submonoid.powers r) (u : L)
    simp only at ha
    have haP : algebraMap R L a ∉ P := by
      rw [← ha]
      exact fun hm ↦ (hP.mem_or_mem hm).elim u.2 (algebraMap_pow_notMem r P j)
    have key : ∀ x, g (a • x) = algebraMap R L (r ^ j) • ((u : L) • g x) := fun x ↦ by
      rw [map_smul, ← algebraMap_smul L a, ← ha, mul_comm, mul_smul]
    have hga : g (a • x₁) = g (a • x₂) := by
      rw [key, key]
      exact congrArg _ hu
    obtain ⟨⟨_, k, rfl⟩, hc⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers r) hga
    refine ⟨⟨r ^ k * a, ?_⟩, ?_⟩
    · change algebraMap R L (r ^ k * a) ∉ P
      rw [map_mul]
      exact fun hm ↦ (hP.mem_or_mem hm).elim (algebraMap_pow_notMem r P k) haP
    · simpa only [Submonoid.smul_def, mul_smul] using hc

include r g in
/-- **Flatness at a point of a principal open is independent of the chart.** For `L = R[1/r]`,
an `L`-module `W` with `N_r = W` (via `g`) and a prime `P` of `L` over `p ⊂ R`: `N` localized at
`p` is flat over `R` iff `W` localized at `P` is flat over `L`. -/
theorem flat_localizedModule_iff :
    Module.Flat R (LocalizedModule (P.comap (algebraMap R L)).primeCompl N) ↔
      Module.Flat L (LocalizedModule P.primeCompl W) := by
  haveI := isLocalizedModule_comp r g P
  have : IsScalarTower R L (LocalizedModule P.primeCompl W) := inferInstance
  let e := IsLocalizedModule.iso (P.comap (algebraMap R L)).primeCompl
    (((LocalizedModule.mkLinearMap P.primeCompl W).restrictScalars R) ∘ₗ g)
  rw [Module.flat_iff_of_isLocalization L (Submonoid.powers r)]
  exact ⟨fun _ ↦ Module.Flat.of_linearEquiv e.symm, fun _ ↦ Module.Flat.of_linearEquiv e⟩

end Transport

end LocalFlatness
