/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartModuleFormal

/-!
# The connecting map of a surjection of chart modules, and its reductions

For a morphism `φ : F → M` of chart modules which is surjective on the charts `Spec A[X]` and
`Spec A[Y]`, the short exact sequence `0 → ker φ → F → M → 0` has a connecting map
`Hom.delta φ : H⁰(M) → H¹(ker φ)` (`FormalSchemes.TwoCech`), computed by lifting a section of `M`
to `F` and taking the difference of the lifts on the overlap (`Hom.delta_eq`). Reducing modulo an
ideal `J` gives `Hom.reduce φ J : F / J F → M / J M`, still surjective, with kernel
`(ker φ + J F) / J F`; this file records the maps comparing the two connecting maps
(`Hom.toReduceKer`, `Hom.delta_reduce`) and the transition maps between reductions
(`Hom.reduceKerMap`, `Hom.delta_quotMap`).
-/

universe u

open Polynomial LaurentPolynomial

namespace ProjectiveLine

namespace ChartModule

variable {A : Type u} [CommRing A] {F M N : ChartModule A}

/-- The inclusion of the kernel. -/
noncomputable def Hom.kerι (φ : Hom F M) : Hom φ.ker F where
  f0 := (LinearMap.ker φ.f0).subtype
  f1 := (LinearMap.ker φ.f1).subtype
  f01 := (LinearMap.ker φ.f01).subtype
  comm_x0 _ := rfl
  comm_x1 _ := rfl
  comm_t _ := rfl
  comm_r0 _ := rfl
  comm_r1 _ := rfl

section Delta

variable (φ : Hom F M) (h0 : Function.Surjective φ.f0) (h1 : Function.Surjective φ.f1)

/-- The connecting map `H⁰(M) → H¹(ker φ)`. -/
noncomputable def Hom.delta : M.H0 →ₗ[A] φ.ker.H1 :=
  TwoCech.δ (f' := φ.ker.r0) (g' := φ.ker.r1)
    (LinearMap.ker φ.f0).subtype (LinearMap.ker φ.f1).subtype (LinearMap.ker φ.f01).subtype
    φ.f0 φ.f1 φ.f01 (LinearMap.ext fun _ ↦ rfl) (LinearMap.ext fun _ ↦ rfl)
    φ.comm_r0' φ.comm_r1' φ.f0.exact_subtype_ker_map φ.f1.exact_subtype_ker_map
    φ.f01.exact_subtype_ker_map h0 h1 (Submodule.injective_subtype (LinearMap.ker φ.f01))

/-- Computing the connecting map: lift, take the Čech differential, and observe it lies in the
kernel. -/
lemma Hom.delta_eq (x : M.H0) (y : F.M0 × F.M1) (hy : (φ.f0 y.1, φ.f1 y.2) = (x : M.M0 × M.M1))
    (z : LinearMap.ker φ.f01) (hz : (z : F.M01) = F.r0 y.1 - F.r1 y.2) :
    φ.delta h0 h1 x = Submodule.Quotient.mk z :=
  TwoCech.δ_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x y hy z (by rw [TwoCech.d_apply]; exact hz)

lemma Hom.exact_mapH0_delta : Function.Exact φ.mapH0 (φ.delta h0 h1) :=
  TwoCech.exact_mapH0_δ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

lemma Hom.exact_delta_mapH1 : Function.Exact (φ.delta h0 h1) φ.kerι.mapH1 :=
  TwoCech.exact_δ_mapH1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

lemma Hom.delta_injective (hF : F.H0 = ⊥) : Function.Injective (φ.delta h0 h1) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (φ.exact_mapH0_delta h0 h1 x).1 hx
  have hy : y = 0 := by
    obtain ⟨y, hy⟩ := y
    have : y ∈ (⊥ : Submodule A (F.M0 × F.M1)) := hF ▸ hy
    exact Subtype.ext ((Submodule.mem_bot _).1 this)
  rw [hy, map_zero]

end Delta

/-! ### Reductions -/

section Reduce

variable (φ : Hom F M) (J : Ideal A)

/-- The reduction `F / J F → M / J M` of a morphism. -/
noncomputable def Hom.reduce : Hom (F.quot J) (M.quot J) where
  f0 := Submodule.mapQ _ _ φ.f0 (smul_top_le_comap J φ.f0)
  f1 := Submodule.mapQ _ _ φ.f1 (smul_top_le_comap J φ.f1)
  f01 := Submodule.mapQ _ _ φ.f01 (smul_top_le_comap J φ.f01)
  comm_x0 m := by
    induction m using Submodule.Quotient.induction_on with
    | H m => exact congrArg Submodule.Quotient.mk (φ.comm_x0 m)
  comm_x1 m := by
    induction m using Submodule.Quotient.induction_on with
    | H m => exact congrArg Submodule.Quotient.mk (φ.comm_x1 m)
  comm_t z := by
    induction z using Submodule.Quotient.induction_on with
    | H z => exact congrArg Submodule.Quotient.mk (φ.comm_t z)
  comm_r0 m := by
    induction m using Submodule.Quotient.induction_on with
    | H m => exact congrArg Submodule.Quotient.mk (φ.comm_r0 m)
  comm_r1 m := by
    induction m using Submodule.Quotient.induction_on with
    | H m => exact congrArg Submodule.Quotient.mk (φ.comm_r1 m)

variable {φ} in
lemma Hom.reduce_surjective {P Q : Type u} [AddCommGroup P] [Module A P] [AddCommGroup Q]
    [Module A Q] {f : P →ₗ[A] Q} (hf : Function.Surjective f) :
    Function.Surjective (Submodule.mapQ (J • (⊤ : Submodule A P)) (J • (⊤ : Submodule A Q)) f
      (smul_top_le_comap J f)) := by
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H q =>
    obtain ⟨p, rfl⟩ := hf q
    exact ⟨Submodule.Quotient.mk p, rfl⟩

/-- `ker φ → ker (φ mod J)`. -/
noncomputable def Hom.toReduceKer : Hom φ.ker (φ.reduce J).ker where
  f0 := LinearMap.codRestrict (LinearMap.ker (φ.reduce J).f0)
    ((J • (⊤ : Submodule A F.M0)).mkQ ∘ₗ (LinearMap.ker φ.f0).subtype) fun k ↦ by
      change Submodule.Quotient.mk (φ.f0 k.1) = 0
      rw [show φ.f0 k.1 = 0 from k.2, Submodule.Quotient.mk_zero]
  f1 := LinearMap.codRestrict (LinearMap.ker (φ.reduce J).f1)
    ((J • (⊤ : Submodule A F.M1)).mkQ ∘ₗ (LinearMap.ker φ.f1).subtype) fun k ↦ by
      change Submodule.Quotient.mk (φ.f1 k.1) = 0
      rw [show φ.f1 k.1 = 0 from k.2, Submodule.Quotient.mk_zero]
  f01 := LinearMap.codRestrict (LinearMap.ker (φ.reduce J).f01)
    ((J • (⊤ : Submodule A F.M01)).mkQ ∘ₗ (LinearMap.ker φ.f01).subtype) fun k ↦ by
      change Submodule.Quotient.mk (φ.f01 k.1) = 0
      rw [show φ.f01 k.1 = 0 from k.2, Submodule.Quotient.mk_zero]
  comm_x0 _ := rfl
  comm_x1 _ := rfl
  comm_t _ := rfl
  comm_r0 _ := rfl
  comm_r1 _ := rfl

variable {J} {J' : Ideal A} (h : J ≤ J')

omit [CommRing A] in
lemma mapQ_factor_comm {R : Type u} [CommRing R] {P Q : Type u} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] (f : P →ₗ[R] Q) {J J' : Ideal R} (h : J ≤ J')
    (x : P ⧸ J • (⊤ : Submodule R P)) :
    Submodule.mapQ _ _ f (smul_top_le_comap J' f) (Submodule.factor (smul_top_mono h) x) =
      Submodule.factor (smul_top_mono h) (Submodule.mapQ _ _ f (smul_top_le_comap J f) x) := by
  induction x using Submodule.Quotient.induction_on with | H p => rfl

lemma factor_mem_ker {P Q : Type u} [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
    (f : P →ₗ[A] Q) (x : LinearMap.ker (Submodule.mapQ (J • (⊤ : Submodule A P))
      (J • (⊤ : Submodule A Q)) f (smul_top_le_comap J f))) :
    Submodule.factor (smul_top_mono h) x.1 ∈
      LinearMap.ker (Submodule.mapQ (J' • (⊤ : Submodule A P))
        (J' • (⊤ : Submodule A Q)) f (smul_top_le_comap J' f)) := by
  rw [LinearMap.mem_ker, mapQ_factor_comm f h, show Submodule.mapQ _ _ f _ x.1 = 0 from x.2,
    map_zero]

/-- The transition map `ker (φ mod J) → ker (φ mod J')` for `J ≤ J'`. -/
noncomputable def Hom.reduceKerMap : Hom (φ.reduce J).ker (φ.reduce J').ker where
  f0 := LinearMap.codRestrict (LinearMap.ker (φ.reduce J').f0)
    ((F.quotMap h).f0 ∘ₗ (LinearMap.ker (φ.reduce J).f0).subtype) (factor_mem_ker h φ.f0)
  f1 := LinearMap.codRestrict (LinearMap.ker (φ.reduce J').f1)
    ((F.quotMap h).f1 ∘ₗ (LinearMap.ker (φ.reduce J).f1).subtype) (factor_mem_ker h φ.f1)
  f01 := LinearMap.codRestrict (LinearMap.ker (φ.reduce J').f01)
    ((F.quotMap h).f01 ∘ₗ (LinearMap.ker (φ.reduce J).f01).subtype) (factor_mem_ker h φ.f01)
  comm_x0 k := Subtype.ext ((F.quotMap h).comm_x0 k.1)
  comm_x1 k := Subtype.ext ((F.quotMap h).comm_x1 k.1)
  comm_t z := Subtype.ext ((F.quotMap h).comm_t z.1)
  comm_r0 k := Subtype.ext ((F.quotMap h).comm_r0 k.1)
  comm_r1 k := Subtype.ext ((F.quotMap h).comm_r1 k.1)

lemma Hom.reduceKerMap_toReduceKer (w : φ.ker.H1) :
    (φ.reduceKerMap h).mapH1 ((φ.toReduceKer J).mapH1 w) = (φ.toReduceKer J').mapH1 w := by
  induction w using Submodule.Quotient.induction_on with | H z => rfl

lemma Hom.reduce_surjective0 (h0 : Function.Surjective φ.f0) (J : Ideal A) :
    Function.Surjective (φ.reduce J).f0 :=
  Hom.reduce_surjective J h0

lemma Hom.reduce_surjective1 (h1 : Function.Surjective φ.f1) (J : Ideal A) :
    Function.Surjective (φ.reduce J).f1 :=
  Hom.reduce_surjective J h1

variable (h0 : Function.Surjective φ.f0) (h1 : Function.Surjective φ.f1)

lemma Hom.sub_mem_ker (x : M.H0) {s : F.M0} {m : F.M1} (hs : φ.f0 s = x.1.1)
    (hm : φ.f1 m = x.1.2) : F.r0 s - F.r1 m ∈ LinearMap.ker φ.f01 := by
  rw [LinearMap.mem_ker, map_sub, φ.comm_r0, φ.comm_r1, hs, hm]
  exact sub_eq_zero.2 (TwoCech.mem_H0.1 x.2)

/-- **Naturality of the connecting map under reduction.** -/
lemma Hom.delta_reduce (J : Ideal A) (x : M.H0) :
    (φ.reduce J).delta (φ.reduce_surjective0 h0 J) (φ.reduce_surjective1 h1 J)
      ((M.quotHom J).mapH0 x) = (φ.toReduceKer J).mapH1 (φ.delta h0 h1 x) := by
  obtain ⟨s, hs⟩ := h0 x.1.1
  obtain ⟨m, hm⟩ := h1 x.1.2
  have hz := φ.sub_mem_ker x hs hm
  rw [φ.delta_eq h0 h1 x (s, m) (by rw [hs, hm]) ⟨_, hz⟩ rfl]
  rw [(φ.reduce J).delta_eq _ _ _ (Submodule.Quotient.mk s, Submodule.Quotient.mk m) ?_
    ((φ.toReduceKer J).f01 ⟨_, hz⟩) ?_]
  · rfl
  · change (Submodule.Quotient.mk (φ.f0 s), Submodule.Quotient.mk (φ.f1 m)) =
      (Submodule.Quotient.mk x.1.1, Submodule.Quotient.mk x.1.2)
    rw [hs, hm]
  · change Submodule.Quotient.mk (F.r0 s - F.r1 m) =
      Submodule.Quotient.mk (F.r0 s) - Submodule.Quotient.mk (F.r1 m)
    rw [Submodule.Quotient.mk_sub]

/-- **Naturality of the connecting map under the transition maps.** -/
lemma Hom.delta_quotMap (y : (M.quot J).H0) :
    (φ.reduce J').delta (φ.reduce_surjective0 h0 J') (φ.reduce_surjective1 h1 J')
      ((M.quotMap h).mapH0 y) =
      (φ.reduceKerMap h).mapH1 ((φ.reduce J).delta (φ.reduce_surjective0 h0 J)
        (φ.reduce_surjective1 h1 J) y) := by
  obtain ⟨s, hs⟩ := φ.reduce_surjective0 h0 J y.1.1
  obtain ⟨m, hm⟩ := φ.reduce_surjective1 h1 J y.1.2
  have hz := (φ.reduce J).sub_mem_ker y hs hm
  rw [(φ.reduce J).delta_eq _ _ y (s, m) (by rw [hs, hm]) ⟨_, hz⟩ rfl]
  rw [(φ.reduce J').delta_eq _ _ _ ((F.quotMap h).f0 s, (F.quotMap h).f1 m) ?_
    ((φ.reduceKerMap h).f01 ⟨_, hz⟩) ?_]
  · rfl
  · change ((φ.reduce J').f0 ((F.quotMap h).f0 s), (φ.reduce J').f1 ((F.quotMap h).f1 m)) =
      ((M.quotMap h).f0 y.1.1, (M.quotMap h).f1 y.1.2)
    rw [← hs, ← hm]
    exact Prod.ext (mapQ_factor_comm φ.f0 h s) (mapQ_factor_comm φ.f1 h m)
  · change (F.quotMap h).f01 ((F.quot J).r0 s - (F.quot J).r1 m) =
      (F.quot J').r0 ((F.quotMap h).f0 s) - (F.quot J').r1 ((F.quotMap h).f1 m)
    rw [map_sub, (F.quotMap h).comm_r0, (F.quotMap h).comm_r1]

omit [CommRing A] in
lemma exists_ker_lift {R : Type u} [CommRing R] {P Q : Type u} [AddCommGroup P] [Module R P]
    [AddCommGroup Q] [Module R Q] (f : P →ₗ[R] Q) (hf : Function.Surjective f) (J : Ideal R)
    (x : P) (hx : f x ∈ J • (⊤ : Submodule R Q)) :
    ∃ k ∈ LinearMap.ker f, x - k ∈ J • (⊤ : Submodule R P) := by
  have : J • (⊤ : Submodule R Q) = (J • (⊤ : Submodule R P)).map f := by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.2 hf]
  rw [this] at hx
  obtain ⟨g, hg, hgx⟩ := hx
  exact ⟨x - g, by rw [LinearMap.mem_ker, map_sub, hgx, sub_self], by rwa [sub_sub_cancel]⟩

omit [CommRing A] in
lemma surjective_toReduceKer_aux {R : Type u} [CommRing R] {P Q : Type u} [AddCommGroup P]
    [Module R P] [AddCommGroup Q] [Module R Q] (f : P →ₗ[R] Q) (hf : Function.Surjective f)
    (J : Ideal R) :
    Function.Surjective (LinearMap.codRestrict (LinearMap.ker (Submodule.mapQ
      (J • (⊤ : Submodule R P)) (J • (⊤ : Submodule R Q)) f (smul_top_le_comap J f)))
      ((J • (⊤ : Submodule R P)).mkQ ∘ₗ (LinearMap.ker f).subtype) fun k ↦ by
        change Submodule.Quotient.mk (f k.1) = 0
        rw [show f k.1 = 0 from k.2, Submodule.Quotient.mk_zero]) := by
  rintro ⟨x, hx⟩
  induction x using Submodule.Quotient.induction_on with | H x => ?_
  have hx' : f x ∈ J • (⊤ : Submodule R Q) := (Submodule.Quotient.mk_eq_zero _).1 hx
  obtain ⟨k, hk, hxk⟩ := exists_ker_lift f hf J x hx'
  refine ⟨⟨k, hk⟩, Subtype.ext ?_⟩
  change Submodule.Quotient.mk k = Submodule.Quotient.mk x
  exact ((Submodule.Quotient.eq _).2 hxk).symm

include h0 in
lemma Hom.toReduceKer_surjective0 (J : Ideal A) : Function.Surjective (φ.toReduceKer J).f0 :=
  surjective_toReduceKer_aux φ.f0 h0 J

include h1 in
lemma Hom.toReduceKer_surjective1 (J : Ideal A) : Function.Surjective (φ.toReduceKer J).f1 :=
  surjective_toReduceKer_aux φ.f1 h1 J

include h0 in
include h0 in
lemma Hom.toReduceKer_surjective01 (J : Ideal A) : Function.Surjective (φ.toReduceKer J).f01 :=
  surjective_toReduceKer_aux φ.f01 (φ.surjective_f01 h0) J

include h0 in
lemma Hom.toReduceKer_mapH1_surjective (J : Ideal A) :
    Function.Surjective (φ.toReduceKer J).mapH1 :=
  TwoCech.mapH1_surjective _ _ _ _ _ (φ.toReduceKer_surjective01 h0 J)

lemma Hom.smul_top_le_ker_toReduceKer_mapH1 (J : Ideal A) :
    J • (⊤ : Submodule A φ.ker.H1) ≤ LinearMap.ker (φ.toReduceKer J).mapH1 := by
  rw [Submodule.smul_le]
  intro a ha w _
  rw [LinearMap.mem_ker, map_smul]
  induction ((φ.toReduceKer J).mapH1 w) using Submodule.Quotient.induction_on with
  | H z =>
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    obtain ⟨z, hz⟩ := z
    induction z using Submodule.Quotient.induction_on with | H z => ?_
    have : a • (⟨Submodule.Quotient.mk z, hz⟩ : LinearMap.ker (φ.reduce J).f01) = 0 := by
      apply Subtype.ext
      change Submodule.Quotient.mk (a • z) = 0
      exact (Submodule.Quotient.mk_eq_zero _).2 (Submodule.smul_mem_smul ha Submodule.mem_top)
    rw [this]
    exact zero_mem _

include h0 h1 in
/-- With an Artin–Rees constant `c` on the overlap, the kernel of `H¹(ker φ) → H¹(ker (φ mod Iⁿ))`
lies in `Iⁿ⁻ᶜ H¹(ker φ)`. -/
lemma Hom.ker_toReduceKer_mapH1_le (I : Ideal A) (c n : ℕ)
    (hc : ∀ z ∈ LinearMap.ker φ.f01, z ∈ I ^ n • (⊤ : Submodule A F.M01) →
      z ∈ I ^ (n - c) • LinearMap.ker φ.f01) :
    LinearMap.ker (φ.toReduceKer (I ^ n)).mapH1 ≤ I ^ (n - c) • (⊤ : Submodule A φ.ker.H1) := by
  intro w hw
  induction w using Submodule.Quotient.induction_on with | H z => ?_
  rw [LinearMap.mem_ker] at hw
  change Submodule.Quotient.mk ((φ.toReduceKer (I ^ n)).f01 z) = 0 at hw
  rw [Submodule.Quotient.mk_eq_zero] at hw
  obtain ⟨⟨k0', k1'⟩, hk⟩ := hw
  obtain ⟨k0, rfl⟩ := φ.toReduceKer_surjective0 h0 (I ^ n) k0'
  obtain ⟨k1, rfl⟩ := φ.toReduceKer_surjective1 h1 (I ^ n) k1'
  set e := z - TwoCech.d φ.ker.r0 φ.ker.r1 (k0, k1) with he
  have he0 : (φ.toReduceKer (I ^ n)).f01 e = 0 := by
    rw [he, map_sub, ← hk, TwoCech.d_apply, TwoCech.d_apply, map_sub,
      (φ.toReduceKer (I ^ n)).comm_r0, (φ.toReduceKer (I ^ n)).comm_r1]
    exact sub_self _
  have he1 : (e : F.M01) ∈ I ^ n • (⊤ : Submodule A F.M01) :=
    (Submodule.Quotient.mk_eq_zero _).1 (congrArg Subtype.val he0)
  have he2 := hc e e.2 he1
  rw [← Submodule.mem_smul_top_iff] at he2
  have hmk : Submodule.Quotient.mk (p := LinearMap.range (TwoCech.d φ.ker.r0 φ.ker.r1)) z =
      (LinearMap.range (TwoCech.d φ.ker.r0 φ.ker.r1)).mkQ e := by
    rw [he, map_sub, sub_eq_self.2 ((Submodule.Quotient.mk_eq_zero _).2
      (LinearMap.mem_range_self _ (k0, k1)))]
    rfl
  rw [hmk]
  have := Submodule.mem_map_of_mem (f := (LinearMap.range (TwoCech.d φ.ker.r0 φ.ker.r1)).mkQ) he2
  rwa [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at this

end Reduce

end ChartModule

end ProjectiveLine
