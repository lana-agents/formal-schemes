/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Compatible systems of modules over the thickenings of an adic ring

Fix a commutative ring `A` and an ideal `I`. An `AdicSystem I` is an inverse system `(Mₙ)ₙ` of
finite `A`-modules such that `Mₙ` is killed by `I^(n+1)` and the transition map `Mₙ₊₁ → Mₙ` is
surjective with kernel `I^(n+1) Mₙ₊₁`, i.e. `Mₙ₊₁ ⧸ I^(n+1) Mₙ₊₁ ≅ Mₙ`. This is the
module-theoretic incarnation of the category `Coh(Spec A, I)` of coherent formal modules of
Stacks, Section 30.23 (Tag 0EHN), with the index shifted by one.

The main results of this file are the algebraic content of Stacks, Lemma 30.23.1 (Tag 087W) and
Lemma 10.98.2 (Tag 09B8): when `A` is `I`-adically precomplete, the limit `M = lim Mₙ`
(`AdicSystem.limit`) is a finite `A`-module (`AdicSystem.limit_finite`), each projection
`M → Mₙ` is surjective with kernel `I^(n+1) M` (`AdicSystem.proj_surjective`,
`AdicSystem.ker_proj`), and hence `M ⧸ I^(n+1) M ≃ Mₙ` (`AdicSystem.quotEquiv`).

The proof follows Stacks 087W: lift generators of `M₀` to the limit, observe by a nilpotent
Nakayama argument that they generate every `Mₙ`, and solve `∑ aᵢ xᵢ = m` by successive
approximation of the coefficients, which converge because `A` is precomplete
(`AdicSystem.exists_coeff`). The Mittag-Leffler argument of Stacks is replaced by the
observation that the kernels of `(A ⧸ I^(n+1))^t → Mₙ` already map onto each other.

## Main definitions and results

* `AdicSystem`, `AdicSystem.limit`, `AdicSystem.proj`
* `AdicSystem.exists_section_of_surjective`: an element of one level of a tower of surjections
  extends to a compatible section.
* `AdicSystem.exists_coeff`: successive approximation of coefficients.
* `AdicSystem.limit_finite`, `AdicSystem.ker_proj`, `AdicSystem.quotEquiv`
-/

universe u v w

open CategoryTheory

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- A compatible system of finite modules over the thickenings `A ⧸ I^(n+1)`: the module-theoretic
form of an object of `Coh(Spec A, I)` (Stacks, Tag 0EHN). -/
structure AdicSystem where
  /-- The module at level `n`, a module over `A ⧸ I^(n+1)`. -/
  obj : ℕ → ModuleCat.{v} A
  /-- The transition map from level `n + 1` to level `n`. -/
  map : ∀ n, obj (n + 1) ⟶ obj n
  map_surjective : ∀ n, Function.Surjective (map n).hom
  ker_map : ∀ n, LinearMap.ker (map n).hom = I ^ (n + 1) • ⊤
  pow_smul_top : ∀ n, I ^ (n + 1) • (⊤ : Submodule A (obj n)) = ⊥
  finite : ∀ n, Module.Finite A (obj n)

namespace AdicSystem

/-- An element of one level of a tower of surjections extends to a compatible section of the
tower. -/
theorem exists_section_of_surjective (n : ℕ) :
    ∀ {X : ℕ → Type w} (f : ∀ k, X (k + 1) → X k), (∀ k, Function.Surjective (f k)) →
      ∀ x : X n, ∃ s : ∀ k, X k, (∀ k, f k (s (k + 1)) = s k) ∧ s n = x := by
  induction n with
  | zero =>
    intro X f hf x
    refine ⟨fun k ↦ Nat.rec (motive := X) x (fun k y ↦ (hf k y).choose) k, fun k ↦ ?_, rfl⟩
    exact (hf k _).choose_spec
  | succ n ih =>
    intro X f hf x
    obtain ⟨t, ht, htn⟩ := ih (X := fun k ↦ X (k + 1)) (fun k ↦ f (k + 1)) (fun k ↦ hf (k + 1)) x
    refine ⟨fun k ↦ Nat.casesOn (motive := X) k (f 0 (t 0)) t, fun k ↦ ?_, htn⟩
    cases k with
    | zero => rfl
    | succ k => exact ht k

variable {I} (S : AdicSystem.{u, v} I)

/-- The limit `lim Mₙ`, as a submodule of the product. -/
def limit : Submodule A (∀ n, S.obj n) where
  carrier := {x | ∀ n, (S.map n).hom (x (n + 1)) = x n}
  add_mem' {x y} hx hy n := by simp [hx n, hy n]
  zero_mem' n := by simp
  smul_mem' c x hx n := by simp [hx n]

/-- The projection `lim Mₙ → Mₙ`. -/
def proj (n : ℕ) : S.limit →ₗ[A] S.obj n :=
  (LinearMap.proj n).comp S.limit.subtype

theorem proj_apply (n : ℕ) (x : S.limit) : S.proj n x = x.1 n := rfl

@[simp]
theorem map_proj (n : ℕ) (x : S.limit) : (S.map n).hom (S.proj (n + 1) x) = S.proj n x :=
  x.2 n

theorem map_comp_proj (n : ℕ) : (S.map n).hom ∘ₗ S.proj (n + 1) = S.proj n :=
  LinearMap.ext (S.map_proj n)

theorem smul_eq_zero {n : ℕ} {c : A} (hc : c ∈ I ^ (n + 1)) (z : S.obj n) : c • z = 0 := by
  have : c • z ∈ I ^ (n + 1) • (⊤ : Submodule A (S.obj n)) :=
    Submodule.smul_mem_smul hc Submodule.mem_top
  rwa [S.pow_smul_top, Submodule.mem_bot] at this

theorem smul_eq_zero_of_le {n m : ℕ} (h : n + 1 ≤ m) {c : A} (hc : c ∈ I ^ m)
    (z : S.obj n) : c • z = 0 :=
  S.smul_eq_zero (Ideal.pow_le_pow_right h hc) z

/-- Every projection of the limit is surjective. -/
theorem proj_surjective (n : ℕ) : Function.Surjective (S.proj n) := by
  intro x
  obtain ⟨s, hs, hsn⟩ := exists_section_of_surjective n (X := fun k ↦ S.obj k)
    (fun k ↦ (S.map k).hom) S.map_surjective x
  exact ⟨⟨s, hs⟩, hsn⟩

/-- An element of the limit vanishing at every level `≥ n` is zero. -/
theorem eq_zero_of_proj_eq_zero (n : ℕ) {y : S.limit} (hy : ∀ j, S.proj (n + j) y = 0) :
    y = 0 := by
  have key : ∀ d k, n ≤ k + d → S.proj k y = 0 := by
    intro d
    induction d with
    | zero =>
      intro k hk
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
      exact hy j
    | succ d ih =>
      intro k hk
      rw [← S.map_proj, ih (k + 1) (by omega), map_zero]
  exact Subtype.ext (funext fun k ↦ key n k (by omega))

/-- The images in `Mₙ₊₁` of a family of elements of the limit generate `Mₙ₊₁` as soon as their
images generate `Mₙ` (nilpotent Nakayama). -/
theorem span_succ_eq_top {ι : Type*} (x : ι → S.limit) (n : ℕ)
    (h : Submodule.span A (Set.range fun i ↦ S.proj n (x i)) = ⊤) :
    Submodule.span A (Set.range fun i ↦ S.proj (n + 1) (x i)) = ⊤ := by
  set N := Submodule.span A (Set.range fun i ↦ S.proj (n + 1) (x i))
  have hmap : N.map (S.map n).hom = ⊤ := by
    rw [Submodule.map_span, ← Set.range_comp, ← h]
    congr 2
    exact funext fun i ↦ S.map_proj n (x i)
  have hsup : N ⊔ I ^ (n + 1) • ⊤ = ⊤ := by
    rw [← S.ker_map, ← Submodule.comap_map_eq, hmap, Submodule.comap_top]
  have hJ : I ^ (n + 1) • (⊤ : Submodule A (S.obj (n + 1))) ≤ N := by
    calc I ^ (n + 1) • (⊤ : Submodule A (S.obj (n + 1)))
        = I ^ (n + 1) • (N ⊔ I ^ (n + 1) • ⊤) := by rw [hsup]
      _ = I ^ (n + 1) • N ⊔ (I ^ (n + 1) * I ^ (n + 1)) • ⊤ := by
          rw [Submodule.smul_sup, Submodule.mul_smul]
      _ ≤ N ⊔ I ^ (n + 1 + 1) • ⊤ := by
          refine sup_le_sup Submodule.smul_le_right ?_
          rw [← pow_add]
          exact Submodule.smul_mono_left (Ideal.pow_le_pow_right (by omega))
      _ = N := by rw [S.pow_smul_top, sup_bot_eq]
  rw [← hsup]
  exact le_antisymm le_sup_left (sup_le le_rfl hJ)

/-- If the images of a family of elements of the limit generate `M₀`, they generate every `Mₙ`. -/
theorem span_eq_top {ι : Type*} (x : ι → S.limit)
    (h : Submodule.span A (Set.range fun i ↦ S.proj 0 (x i)) = ⊤) (n : ℕ) :
    Submodule.span A (Set.range fun i ↦ S.proj n (x i)) = ⊤ := by
  induction n with
  | zero => exact h
  | succ n ih => exact S.span_succ_eq_top x n ih

theorem smodEq_pow_iff {n : ℕ} {a b : A} :
    a ≡ b [SMOD (I ^ n • ⊤ : Submodule A A)] ↔ a - b ∈ I ^ n := by
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]

section Approximation

variable {ι : Type*} [Fintype ι] (x : ι → S.limit)
  (hx : ∀ k, Submodule.span A (Set.range fun i ↦ S.proj k (x i)) = ⊤)
include hx

/-- One step of the successive approximation: coefficients expressing `m` at level `k` can be
corrected by elements of `I^(k+1)` to coefficients expressing `m` at level `k + 1`. -/
theorem exists_coeff_succ (m : S.limit) (k : ℕ) (b : ι → A)
    (hb : ∑ i, b i • S.proj k (x i) = S.proj k m) :
    ∃ b' : ι → A, (∀ i, b' i - b i ∈ I ^ (k + 1)) ∧
      ∑ i, b' i • S.proj (k + 1) (x i) = S.proj (k + 1) m := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun A).1
    ((hx (k + 1)).symm ▸ Submodule.mem_top : S.proj (k + 1) m ∈ _)
  have h1 : ∑ i, c i • S.proj k (x i) = S.proj k m := by
    rw [← S.map_proj, ← hc, map_sum]
    simp only [map_smul, map_proj]
  have hker : ∑ i, (c i - b i) • S.proj (k + 1) (x i) ∈ LinearMap.ker (S.map k).hom := by
    rw [LinearMap.mem_ker, map_sum]
    simp only [sub_smul, map_sub, map_smul, map_proj, Finset.sum_sub_distrib, h1, hb, sub_self]
  rw [S.ker_map, ← hx (k + 1), Submodule.mem_ideal_smul_span_iff_exists_sum] at hker
  obtain ⟨e, he, hsum⟩ := hker
  refine ⟨b + ⇑e, fun i ↦ by simpa using he i, ?_⟩
  rw [Finsupp.sum_fintype _ _ (by simp)] at hsum
  simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, hsum, sub_smul,
    Finset.sum_sub_distrib, hc]
  abel

variable [IsPrecomplete I A]

/-- **Successive approximation** (Stacks, Tag 087W). If finitely many elements `xᵢ` of the limit
generate every level, and coefficients `a⁰` express `m` at level `n`, then there are coefficients
`a ≡ a⁰ mod I^(n+1)` with `∑ aᵢ xᵢ = m` in the limit. -/
theorem exists_coeff (m : S.limit) (n : ℕ) (a₀ : ι → A)
    (ha₀ : ∑ i, a₀ i • S.proj n (x i) = S.proj n m) :
    ∃ a : ι → A, (∀ i, a i - a₀ i ∈ I ^ (n + 1)) ∧ ∑ i, a i • x i = m := by
  choose g hg₁ hg₂ using S.exists_coeff_succ x hx m
  let seq : (j : ℕ) → {b : ι → A // ∑ i, b i • S.proj (n + j) (x i) = S.proj (n + j) m} :=
    fun j ↦ Nat.rec ⟨a₀, ha₀⟩ (fun j b ↦ ⟨g (n + j) b.1 b.2, hg₂ _ _ b.2⟩) j
  have hstep : ∀ j i, (seq (j + 1)).1 i - (seq j).1 i ∈ I ^ (n + j + 1) :=
    fun j i ↦ hg₁ (n + j) _ (seq j).2 i
  have hmono : ∀ j d i, (seq (j + d)).1 i - (seq j).1 i ∈ I ^ (n + j + 1) := by
    intro j d i
    induction d with
    | zero => simp
    | succ d ih =>
      have := Ideal.pow_le_pow_right (I := I) (show n + j + 1 ≤ n + (j + d) + 1 by omega)
        (hstep (j + d) i)
      have h := add_mem this ih
      rw [sub_add_sub_cancel] at h
      exact h
  have hcauchy : ∀ i {p q : ℕ}, p ≤ q →
      (seq p).1 i ≡ (seq q).1 i [SMOD (I ^ p • ⊤ : Submodule A A)] := by
    intro i p q hpq
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hpq
    rw [smodEq_pow_iff, ← neg_mem_iff, neg_sub]
    exact Ideal.pow_le_pow_right (by omega) (hmono p d i)
  choose L hL using fun i ↦ IsPrecomplete.prec inferInstance (hcauchy i)
  have hclose : ∀ j i, L i - (seq j).1 i ∈ I ^ (n + j + 1) := by
    intro j i
    have h1 := (smodEq_pow_iff (I := I)).1 (hL i (n + j + 1))
    have h2 := hmono j (n + 1) i
    rw [show j + (n + 1) = n + j + 1 by omega] at h2
    rw [show L i - (seq j).1 i = -((seq (n + j + 1)).1 i - L i) +
      ((seq (n + j + 1)).1 i - (seq j).1 i) by abel]
    exact add_mem (neg_mem h1) h2
  refine ⟨L, fun i ↦ by simpa [seq] using hclose 0 i, ?_⟩
  rw [← sub_eq_zero]
  refine S.eq_zero_of_proj_eq_zero n fun j ↦ ?_
  have hzero : ∑ i, (L i - (seq j).1 i) • S.proj (n + j) (x i) = 0 :=
    Finset.sum_eq_zero fun i _ ↦ S.smul_eq_zero (hclose j i) _
  simp only [sub_smul, Finset.sum_sub_distrib, (seq j).2, sub_eq_zero] at hzero
  simp [map_sum, map_smul, hzero]

end Approximation

/-- Lifts to the limit of finitely many generators of `M₀` generate every level. -/
theorem exists_generators : ∃ (t : ℕ) (x : Fin t → S.limit),
    ∀ k, Submodule.span A (Set.range fun i ↦ S.proj k (x i)) = ⊤ := by
  have := S.finite 0
  obtain ⟨t, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := S.obj 0)
  choose x hx using fun i ↦ S.proj_surjective 0 (s i)
  refine ⟨t, x, S.span_eq_top x ?_⟩
  simpa [hx] using hs

section Limit

variable [IsPrecomplete I A]

theorem mem_span_of_span_eq_top {t : ℕ} (x : Fin t → S.limit)
    (hx : ∀ k, Submodule.span A (Set.range fun i ↦ S.proj k (x i)) = ⊤) (m : S.limit) :
    m ∈ Submodule.span A (Set.range x) := by
  obtain ⟨a₀, ha₀⟩ := (Submodule.mem_span_range_iff_exists_fun A).1
    ((hx 0).symm ▸ Submodule.mem_top : S.proj 0 m ∈ _)
  obtain ⟨a, -, ha⟩ := S.exists_coeff x hx m 0 a₀ ha₀
  exact (Submodule.mem_span_range_iff_exists_fun A).2 ⟨a, ha⟩

/-- **The limit of an adic system is a finite module** (Stacks, Tag 087W). -/
instance limit_finite : Module.Finite A S.limit := by
  obtain ⟨t, x, hx⟩ := S.exists_generators
  refine ⟨Submodule.fg_def.2 ⟨Set.range x, Set.finite_range x, ?_⟩⟩
  rw [eq_top_iff]
  exact fun m _ ↦ S.mem_span_of_span_eq_top x hx m

/-- The kernel of the projection `lim Mₖ → Mₙ` is `I^(n+1)` times the limit
(Stacks, Tag 09B8). -/
theorem ker_proj (n : ℕ) : LinearMap.ker (S.proj n) = I ^ (n + 1) • ⊤ := by
  apply le_antisymm
  · intro m hm
    obtain ⟨t, x, hx⟩ := S.exists_generators
    obtain ⟨a, ha, rfl⟩ := S.exists_coeff x hx m n 0 (by simp [LinearMap.mem_ker.1 hm])
    exact Submodule.sum_mem _ fun i _ ↦
      Submodule.smul_mem_smul (by simpa using ha i) Submodule.mem_top
  · rw [Submodule.smul_le]
    intro c hc y _
    rw [LinearMap.mem_ker, map_smul, S.smul_eq_zero hc]

/-- **`lim Mₖ ⧸ I^(n+1) ≃ Mₙ`** (Stacks, Tag 09B8). -/
noncomputable def quotEquiv (n : ℕ) :
    (S.limit ⧸ (I ^ (n + 1) • ⊤ : Submodule A S.limit)) ≃ₗ[A] S.obj n :=
  (Submodule.quotEquivOfEq _ _ (S.ker_proj n).symm).trans
    ((S.proj n).quotKerEquivOfSurjective (S.proj_surjective n))

@[simp]
theorem quotEquiv_mk (n : ℕ) (m : S.limit) :
    S.quotEquiv n (Submodule.Quotient.mk m) = S.proj n m := by
  simp [quotEquiv]

end Limit

end AdicSystem
