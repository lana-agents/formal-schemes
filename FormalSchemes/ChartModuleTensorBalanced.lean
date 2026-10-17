/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import FormalSchemes.ChartModuleFF
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Tensor products over `A[X]` of modules with an endomorphism

For `A`-modules `P`, `Q` with endomorphisms `f`, `g`, `ProjectiveLine.BTensor f g` is the tensor
product over `A[X]` of `P` and `Q`, `X` acting by `f` and `g` (`Module.AEval'`). This is the
tensor product of the sections of two quasi-coherent modules over a chart of `ℙ¹_A`.

* `BTensor.tm p q`: the pure tensor of `p : P` and `q : Q`; `tm (f p) q = tm p (g q)`;
* `BTensor.xmul`: the action of `X`, as an `A`-linear endomorphism;
* `BTensor.blift`: the `A`-linear map out of `BTensor f g` given by an `A`-bilinear map `β`
  with `β (f p) q = h (β p q) = β p (g q)`; it intertwines `xmul` and `h`;
* `BTensor.bmap`: functoriality along maps commuting with the endomorphisms (`A[X]`-linear);
* `BTensor.exists_and_ker`: **tensor products commute with localization**: if `r : P → R`,
  `s : Q → S` are localizations at `X` (`X` acting by automorphisms `τ`, `σ` on `R`, `S`), so
  is `r ⊗ s : P ⊗ Q → R ⊗ S` (via `IsLocalizedModule.rTensor`).
-/

universe u

open Polynomial TensorProduct

namespace ProjectiveLine

variable {A : Type u} [CommRing A]
variable {P Q R S T : Type u} [AddCommGroup P] [Module A P] [AddCommGroup Q] [Module A Q]
  [AddCommGroup R] [Module A R] [AddCommGroup S] [Module A S] [AddCommGroup T] [Module A T]

/-- The tensor product over `A[X]` of `P` and `Q`, `X` acting by `f` and `g`. -/
abbrev BTensor (f : P →ₗ[A] P) (g : Q →ₗ[A] Q) : Type u :=
  Module.AEval' f ⊗[A[X]] Module.AEval' g

namespace BTensor

variable {f : P →ₗ[A] P} {g : Q →ₗ[A] Q}

/-- The pure tensor `p ⊗ q`. -/
noncomputable def tm (f : P →ₗ[A] P) (g : Q →ₗ[A] Q) (p : P) (q : Q) : BTensor f g :=
  Module.AEval'.of f p ⊗ₜ[A[X]] Module.AEval'.of g q

lemma tm_add_left (p p' : P) (q : Q) : tm f g (p + p') q = tm f g p q + tm f g p' q := by
  simp [tm, add_tmul]

lemma tm_add_right (p : P) (q q' : Q) : tm f g p (q + q') = tm f g p q + tm f g p q' := by
  simp [tm, tmul_add]

lemma tm_smul_left (a : A) (p : P) (q : Q) : tm f g (a • p) q = a • tm f g p q := by
  simp only [tm, map_smul]
  rw [← algebraMap_smul (A := A[X]) a, ← algebraMap_smul (A := A[X]) a, smul_tmul']

lemma tm_smul_right (a : A) (p : P) (q : Q) : tm f g p (a • q) = a • tm f g p q := by
  simp only [tm, map_smul]
  rw [← algebraMap_smul (A := A[X]) a, ← algebraMap_smul (A := A[X]) a, tmul_smul]

lemma X_pow_smul_tm (k : ℕ) (p : P) (q : Q) :
    ((X : A[X]) ^ k) • tm f g p q = tm f g ((f ^ k) p) q := by
  rw [tm, smul_tmul', Module.AEval'.X_pow_smul_of]
  rfl

lemma X_pow_smul_tm' (k : ℕ) (p : P) (q : Q) :
    ((X : A[X]) ^ k) • tm f g p q = tm f g p ((g ^ k) q) := by
  rw [tm, ← tmul_smul, Module.AEval'.X_pow_smul_of]
  rfl

lemma tm_f (p : P) (q : Q) : tm f g (f p) q = tm f g p (g q) := by
  have h1 := X_pow_smul_tm (f := f) (g := g) 1 p q
  have h2 := X_pow_smul_tm' (f := f) (g := g) 1 p q
  simp only [pow_one] at h1 h2
  rw [← h1, h2]

lemma tm_pow (k : ℕ) (p : P) (q : Q) : tm f g ((f ^ k) p) q = tm f g p ((g ^ k) q) := by
  rw [← X_pow_smul_tm, X_pow_smul_tm']

variable (f g) in
/-- The pure tensor as an `A`-bilinear map. -/
noncomputable def tmBil : P →ₗ[A] Q →ₗ[A] BTensor f g :=
  LinearMap.mk₂ A (tm f g) tm_add_left tm_smul_left tm_add_right tm_smul_right

@[simp] lemma tmBil_apply (p : P) (q : Q) : tmBil f g p q = tm f g p q := rfl

@[simp] lemma tm_zero_left (q : Q) : tm f g 0 q = 0 := by
  rw [← tmBil_apply, map_zero, LinearMap.zero_apply]

@[simp] lemma tm_zero_right (p : P) : tm f g p 0 = 0 := by
  rw [← tmBil_apply, map_zero]

@[elab_as_elim]
lemma induction_on {C : BTensor f g → Prop} (w : BTensor f g) (h0 : C 0)
    (htm : ∀ p q, C (tm f g p q)) (hadd : ∀ x y, C x → C y → C (x + y)) : C w := by
  induction w using TensorProduct.induction_on with
  | zero => exact h0
  | tmul m n =>
    have := htm ((Module.AEval'.of f).symm m) ((Module.AEval'.of g).symm n)
    simpa [tm] using this
  | add x y hx hy => exact hadd x y hx hy

lemma ext {φ ψ : BTensor f g →ₗ[A] T} (h : ∀ p q, φ (tm f g p q) = ψ (tm f g p q)) : φ = ψ := by
  refine LinearMap.ext fun w ↦ ?_
  induction w using induction_on with
  | h0 => simp
  | htm p q => exact h p q
  | hadd x y hx hy => rw [map_add, map_add, hx, hy]

variable (f g) in
/-- The action of `X`. -/
noncomputable def xmul : BTensor f g →ₗ[A] BTensor f g :=
  (LinearMap.lsmul A[X] (BTensor f g) X).restrictScalars A

lemma xmul_apply (w : BTensor f g) : xmul f g w = (X : A[X]) • w := rfl

lemma xmul_pow_apply (k : ℕ) (w : BTensor f g) : (xmul f g ^ k) w = ((X : A[X]) ^ k) • w := by
  induction k generalizing w with
  | zero => simp
  | succ k ih => rw [pow_succ, Module.End.mul_apply, ih, xmul_apply, pow_succ, mul_smul]

lemma xmul_tm (p : P) (q : Q) : xmul f g (tm f g p q) = tm f g (f p) q := by
  rw [xmul_apply]
  simpa using X_pow_smul_tm (f := f) (g := g) 1 p q

lemma xmul_tm' (p : P) (q : Q) : xmul f g (tm f g p q) = tm f g p (g q) := by
  rw [xmul_tm, tm_f]

/-! ### Maps out of `BTensor` -/

section Lift

variable (h : T →ₗ[A] T) (β : P →ₗ[A] Q →ₗ[A] T) (hl : ∀ p q, β (f p) q = h (β p q))
  (hr : ∀ p q, β p (g q) = h (β p q))

/-- The underlying `A[X]`-bilinear map of `blift`. -/
noncomputable def bliftBil : Module.AEval' f →ₗ[A[X]] Module.AEval' g →ₗ[A[X]] Module.AEval' h :=
  LinearMap.mk₂ A[X]
    (fun m n ↦ Module.AEval'.of h (β ((Module.AEval'.of f).symm m) ((Module.AEval'.of g).symm n)))
    (fun m m' n ↦ by simp)
    (fun c m n ↦ by
      let L : P →ₗ[A] Module.AEval' h :=
        (Module.AEval'.of h).toLinearMap ∘ₗ β.flip ((Module.AEval'.of g).symm n)
      have hL : ∀ p, L (f • p) = (X : A[X]) • L p := fun p ↦ by
        simp only [L, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
          LinearMap.flip_apply, Module.End.smul_def, hl, Module.AEval'.X_smul_of]
      exact (LinearMap.ofAEval f L hL).map_smul c m)
    (fun m n n' ↦ by simp)
    (fun c m n ↦ by
      let L : Q →ₗ[A] Module.AEval' h :=
        (Module.AEval'.of h).toLinearMap ∘ₗ β ((Module.AEval'.of f).symm m)
      have hL : ∀ q, L (g • q) = (X : A[X]) • L q := fun q ↦ by
        simp only [L, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
          Module.End.smul_def, hr, Module.AEval'.X_smul_of]
      exact (LinearMap.ofAEval g L hL).map_smul c n)

/-- **The map out of `BTensor f g`** given by a balanced bilinear map. -/
noncomputable def blift : BTensor f g →ₗ[A] T :=
  (Module.AEval'.of h).symm.toLinearMap ∘ₗ
    (TensorProduct.lift (bliftBil h β hl hr)).restrictScalars A

@[simp] lemma blift_tm (p : P) (q : Q) : blift h β hl hr (tm f g p q) = β p q := by
  simp [blift, tm, bliftBil]

lemma blift_xmul (w : BTensor f g) : blift h β hl hr (xmul f g w) = h (blift h β hl hr w) := by
  induction w using induction_on with
  | h0 => simp
  | htm p q => rw [xmul_tm, blift_tm, blift_tm, hl]
  | hadd x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

end Lift

section Map

variable {P' Q' : Type u} [AddCommGroup P'] [Module A P'] [AddCommGroup Q'] [Module A Q']
  {f' : P' →ₗ[A] P'} {g' : Q' →ₗ[A] Q'}

/-- An `A`-linear map commuting with the endomorphisms, as an `A[X]`-linear map. -/
noncomputable def aevalMap (u : P →ₗ[A] P') (hu : ∀ p, u (f p) = f' (u p)) :
    Module.AEval' f →ₗ[A[X]] Module.AEval' f' :=
  LinearMap.ofAEval f ((Module.AEval'.of f').toLinearMap ∘ₗ u) fun p ↦ by
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, Module.End.smul_def,
      hu, Module.AEval'.X_smul_of]

lemma aevalMap_of (u : P →ₗ[A] P') (hu : ∀ p, u (f p) = f' (u p)) (p : P) :
    aevalMap u hu (Module.AEval'.of f p) = Module.AEval'.of f' (u p) := by
  simp [aevalMap, LinearMap.ofAEval]

/-- **Functoriality**: `u ⊗ v` for maps commuting with the endomorphisms. -/
noncomputable def bmapX (u : P →ₗ[A] P') (v : Q →ₗ[A] Q') (hu : ∀ p, u (f p) = f' (u p))
    (hv : ∀ q, v (g q) = g' (v q)) : BTensor f g →ₗ[A[X]] BTensor f' g' :=
  TensorProduct.map (aevalMap u hu) (aevalMap v hv)

/-- `u ⊗ v` as an `A`-linear map. -/
noncomputable def bmap (u : P →ₗ[A] P') (v : Q →ₗ[A] Q') (hu : ∀ p, u (f p) = f' (u p))
    (hv : ∀ q, v (g q) = g' (v q)) : BTensor f g →ₗ[A] BTensor f' g' :=
  (bmapX u v hu hv).restrictScalars A

variable (u : P →ₗ[A] P') (v : Q →ₗ[A] Q') (hu : ∀ p, u (f p) = f' (u p))
  (hv : ∀ q, v (g q) = g' (v q))

@[simp] lemma bmap_tm (p : P) (q : Q) : bmap u v hu hv (tm f g p q) = tm f' g' (u p) (v q) := by
  simp [bmap, bmapX, tm, aevalMap_of]

lemma bmap_X_pow_smul (k : ℕ) (w : BTensor f g) :
    bmap u v hu hv (((X : A[X]) ^ k) • w) = ((X : A[X]) ^ k) • bmap u v hu hv w :=
  (bmapX u v hu hv).map_smul _ w

lemma bmap_xmul (w : BTensor f g) : bmap u v hu hv (xmul f g w) = xmul f' g' (bmap u v hu hv w) :=
  (bmapX u v hu hv).map_smul _ w

lemma bmap_xmul_pow (k : ℕ) (w : BTensor f g) :
    bmap u v hu hv ((xmul f g ^ k) w) = (xmul f' g' ^ k) (bmap u v hu hv w) := by
  rw [xmul_pow_apply, xmul_pow_apply, bmap_X_pow_smul]

lemma bmap_id : bmap (f := f) (g := g) LinearMap.id LinearMap.id (fun _ ↦ rfl) (fun _ ↦ rfl) =
    LinearMap.id :=
  ext fun p q ↦ by simp

lemma bmap_comp {P'' Q'' : Type u} [AddCommGroup P''] [Module A P''] [AddCommGroup Q'']
    [Module A Q''] {f'' : P'' →ₗ[A] P''} {g'' : Q'' →ₗ[A] Q''} (u' : P' →ₗ[A] P'')
    (v' : Q' →ₗ[A] Q'') (hu' : ∀ p, u' (f' p) = f'' (u' p)) (hv' : ∀ q, v' (g' q) = g'' (v' q)) :
    bmap u' v' hu' hv' ∘ₗ bmap u v hu hv =
      bmap (u' ∘ₗ u) (v' ∘ₗ v) (fun p ↦ by simp [hu, hu']) (fun q ↦ by simp [hv, hv']) :=
  ext fun p q ↦ by simp

end Map

/-! ### Localization -/

section Localization

variable {τ : R ≃ₗ[A] R} {σ : S ≃ₗ[A] S}

lemma pow_apply_eq (k : ℕ) (z : R) : ((τ : R →ₗ[A] R) ^ k) z = (τ ^ k) z := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ', pow_succ', Module.End.mul_apply, LinearEquiv.mul_apply, ih]; rfl

/-- `X` acts bijectively on a tensor product whose left factor carries an automorphism. -/
lemma X_smul_injective {M : Type u} [AddCommGroup M] [Module A[X] M] :
    Function.Injective (fun w : Module.AEval' (τ : R →ₗ[A] R) ⊗[A[X]] M ↦ (X : A[X]) • w) := by
  let inv : Module.AEval' (τ : R →ₗ[A] R) →ₗ[A[X]] Module.AEval' (τ : R →ₗ[A] R) :=
    aevalMap (f := (τ : R →ₗ[A] R)) (f' := (τ : R →ₗ[A] R)) τ.symm.toLinearMap
      (fun p ↦ by simp)
  have key : ∀ w : Module.AEval' (τ : R →ₗ[A] R) ⊗[A[X]] M,
      TensorProduct.map inv (LinearMap.id : M →ₗ[A[X]] M) ((X : A[X]) • w) = w := fun w ↦ by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul m n =>
      obtain ⟨p, rfl⟩ := (Module.AEval'.of (τ : R →ₗ[A] R)).surjective m
      rw [smul_tmul', map_tmul, Module.AEval'.X_smul_of, aevalMap_of]
      simp
    | add x y hx hy => rw [smul_add, map_add, hx, hy]
  exact fun w w' h ↦ by rw [← key w, ← key w']; exact congrArg _ h

lemma X_pow_smul_injective {M : Type u} [AddCommGroup M] [Module A[X] M] (k : ℕ) :
    Function.Injective
      (fun w : Module.AEval' (τ : R →ₗ[A] R) ⊗[A[X]] M ↦ ((X : A[X]) ^ k) • w) := by
  induction k with
  | zero => exact fun _ _ h ↦ by simpa using h
  | succ k ih =>
    intro w w' h
    simp only [pow_succ, mul_smul] at h
    exact X_smul_injective (ih h)

variable {r : P →ₗ[A] R} (hr : ∀ p, r (f p) = τ (r p))
  (hex : ∀ z, ∃ (p : P) (k : ℕ), (τ ^ k) z = r p) (hker : ∀ p, r p = 0 → ∃ k : ℕ, (f ^ k) p = 0)

include hex hker in
/-- A localization at `X` in the sense of chart modules is an `IsLocalizedModule`. -/
lemma isLocalizedModule_aevalMap :
    IsLocalizedModule.Away (X : A[X]) (aevalMap (f' := (τ : R →ₗ[A] R)) r hr) := by
  refine IsLocalizedModule.Away.mk_of_addCommGroup ?_ ?_ ?_
  · rw [Module.End.isUnit_iff]
    have hb : Function.Bijective (fun z : Module.AEval' (τ : R →ₗ[A] R) ↦ (X : A[X]) • z) := by
      have : (fun z : Module.AEval' (τ : R →ₗ[A] R) ↦ (X : A[X]) • z) =
          Module.AEval'.of (τ : R →ₗ[A] R) ∘ τ ∘ (Module.AEval'.of (τ : R →ₗ[A] R)).symm := by
        funext z
        obtain ⟨z, rfl⟩ := (Module.AEval'.of (τ : R →ₗ[A] R)).surjective z
        simp [Module.AEval'.X_smul_of]
      rw [this]
      exact (Module.AEval'.of _).bijective.comp
        (τ.bijective.comp (Module.AEval'.of _).symm.bijective)
    exact hb
  · intro z
    obtain ⟨p, k, hk⟩ := hex ((Module.AEval'.of (τ : R →ₗ[A] R)).symm z)
    refine ⟨k, Module.AEval'.of f p, ?_⟩
    obtain ⟨z, rfl⟩ := (Module.AEval'.of (τ : R →ₗ[A] R)).surjective z
    rw [Module.AEval'.X_pow_smul_of, aevalMap_of, ← hk]
    simp only [LinearEquiv.symm_apply_apply]
    congr 1
    rw [Module.End.smul_def]
    exact pow_apply_eq k z
  · intro m hm
    obtain ⟨p, rfl⟩ := (Module.AEval'.of f).surjective m
    rw [aevalMap_of, LinearEquiv.map_eq_zero_iff] at hm
    obtain ⟨k, hk⟩ := hker p hm
    exact ⟨k, by rw [Module.AEval'.X_pow_smul_of]; simp [Module.End.smul_def, hk]⟩

variable {s : Q →ₗ[A] S} (hs : ∀ q, s (g q) = σ (s q))
  (hex' : ∀ z, ∃ (q : Q) (k : ℕ), (σ ^ k) z = s q) (hker' : ∀ q, s q = 0 → ∃ k : ℕ, (g ^ k) q = 0)


include hex hex' in
/-- Every element of `R ⊗ S` becomes, after multiplication by a power of `X`, the image of an
element of `P ⊗ Q`. -/
lemma exists_bmap (z : BTensor (τ : R →ₗ[A] R) (σ : S →ₗ[A] S)) :
    ∃ (w : BTensor f g) (k : ℕ), (xmul _ _ ^ k) z = bmap r s hr hs w := by
  induction z using induction_on with
  | h0 => exact ⟨0, 0, by simp⟩
  | htm a b =>
    obtain ⟨p, k, hk⟩ := hex a
    obtain ⟨q, l, hl⟩ := hex' b
    refine ⟨tm f g p q, k + l, ?_⟩
    rw [xmul_pow_apply, pow_add, mul_smul, X_pow_smul_tm', X_pow_smul_tm,
      pow_apply_eq (τ := τ) k a, hk, pow_apply_eq (τ := σ) l b, hl, bmap_tm]
  | hadd x y hx hy =>
    obtain ⟨w, k, hk⟩ := hx
    obtain ⟨w', k', hk'⟩ := hy
    refine ⟨((X : A[X]) ^ k') • w + ((X : A[X]) ^ k) • w', k + k', ?_⟩
    rw [map_add, map_add, bmap_X_pow_smul, bmap_X_pow_smul, ← xmul_pow_apply, ← xmul_pow_apply,
      ← hk, ← hk', ← Module.End.mul_apply, ← Module.End.mul_apply, ← pow_add, ← pow_add,
      add_comm k' k]

include hex hker hex' hker' in
/-- **Tensor products commute with localization**: an element of `P ⊗ Q` mapping to `0` in
`R ⊗ S` is killed by a power of `X`. -/
lemma exists_xmul_pow_eq_zero (w : BTensor f g) (hw : bmap r s hr hs w = 0) :
    ∃ k : ℕ, (xmul f g ^ k) w = 0 := by
  have hr' := isLocalizedModule_aevalMap hr hex hker
  have hs' := isLocalizedModule_aevalMap hs hex' hker'
  let r' := aevalMap (f' := (τ : R →ₗ[A] R)) r hr
  let s' := aevalMap (f' := (σ : S →ₗ[A] S)) s hs
  -- `r ⊗ s = (1 ⊗ s) ∘ (r ⊗ 1)`
  have hfac : bmapX r s hr hs = (TensorProduct.map LinearMap.id s') ∘ₗ
      (TensorProduct.AlgebraTensorModule.rTensor A[X] (Module.AEval' g) r') := by
    apply TensorProduct.ext'
    intro m n
    simp [bmapX, r', s']
  -- `1 ⊗ s` is injective
  have hinj : Function.Injective (TensorProduct.map (LinearMap.id :
      Module.AEval' (τ : R →ₗ[A] R) →ₗ[A[X]] _) s') := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro u hu
    rw [LinearMap.mem_ker] at hu
    have hc : TensorProduct.AlgebraTensorModule.rTensor A[X] (Module.AEval' (τ : R →ₗ[A] R)) s'
        (TensorProduct.comm A[X] _ _ u) = 0 := by
      have : TensorProduct.AlgebraTensorModule.rTensor A[X] (Module.AEval' (τ : R →ₗ[A] R)) s'
          ∘ₗ (TensorProduct.comm A[X] _ _).toLinearMap =
          (TensorProduct.comm A[X] _ _).toLinearMap ∘ₗ TensorProduct.map LinearMap.id s' := by
        apply TensorProduct.ext'
        intro m n
        simp
      have h2 := LinearMap.congr_fun this u
      simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply] at h2
      rw [h2, hu, map_zero]
    have hloc := IsLocalizedModule.rTensor (R := A[X]) (A := A[X]) (Submonoid.powers X)
      (N := Module.AEval' (τ : R →ₗ[A] R)) s'
    obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers (X : A[X]))
      (f := TensorProduct.AlgebraTensorModule.rTensor A[X] (Module.AEval' (τ : R →ₗ[A] R)) s')
      (x₁ := TensorProduct.comm A[X] _ _ u) (x₂ := 0) (by rw [hc, map_zero])
    simp only [Submonoid.smul_def, smul_zero] at hk
    rw [← LinearEquiv.map_smul, LinearEquiv.map_eq_zero_iff] at hk
    refine (Submodule.mem_bot A[X]).2 (X_pow_smul_injective (τ := τ) k ?_)
    simpa using hk
  have h1 : TensorProduct.AlgebraTensorModule.rTensor A[X] (Module.AEval' g) r' w = 0 := by
    apply hinj
    rw [map_zero, ← LinearMap.comp_apply, ← hfac]
    exact hw
  have hloc := IsLocalizedModule.rTensor (R := A[X]) (A := A[X]) (Submonoid.powers X)
    (N := Module.AEval' g) r'
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers (X : A[X]))
    (f := TensorProduct.AlgebraTensorModule.rTensor A[X] (Module.AEval' g) r')
    (x₁ := w) (x₂ := 0) (by rw [h1, map_zero])
  refine ⟨k, ?_⟩
  rw [xmul_pow_apply]
  simpa [Submonoid.smul_def] using hk

end Localization

end BTensor

end ProjectiveLine
