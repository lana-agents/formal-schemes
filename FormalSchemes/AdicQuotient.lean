import FormalSchemes.RestrictedPowerSeries
import Mathlib.RingTheory.AdicCompletion.Noetherian

set_option linter.style.header false

/-!
# Completeness of quotients of adic rings

If `B` is a `K`-adically complete ring and `A` is a `B`-algebra whose structure map is
surjective (e.g. a quotient of `B`), then `A` is precomplete for the induced filtration: Cauchy
sequences lift to Cauchy sequences of `B` (choosing, term by term, lifts of the differences
inside the powers of `K`), converge there, and push back down. Hausdorff separation, by
contrast, is *not* automatic: it holds precisely when the kernel of the structure map is closed
for the `K`-adic topology, i.e. when `⋂ n (ker + K ^ n) = ker` — in the noetherian setting this
is the Artin–Rees lemma; here we take it as a hypothesis (`RingHom.AdicKerClosed`).

Together: a quotient of a complete adic ring by an adically closed ideal is again a complete
adic ring (`IsAdicRing.of_surjective_of_kerClosed`). This is the engine behind quotients of
restricted power series rings — the topologically-of-finite-type algebras in which the
Tate-curve constructions live (Bosch, §7) — and behind the affine case of formal completions.

## Main results

* `RingHom.AdicKerClosed`: the kernel of a ring homomorphism is closed for the `K`-adic
  topology of the source.
* `IsPrecomplete.of_surjective_algebraMap`: quotients of precomplete rings are precomplete.
* `IsHausdorff.of_surjective_of_kerClosed`: quotients by adically closed ideals are Hausdorff.
* `IsAdicComplete.of_surjective_of_kerClosed`, `IsAdicRing.of_surjective_of_kerClosed`: the
  combination, in ring form (for the extended ideal `K.map (algebraMap B A)` with its adic
  topology).
* `RingHom.adicKerClosed_of_noetherian`: **in the Noetherian setting the closedness hypothesis
  is automatic** — if `B` is Noetherian and `K`-adically complete then every kernel of a
  surjection out of `B` is `K`-adically closed (Krull intersection). Hence
  `IsAdicComplete.of_surjective_of_noetherian` and `IsAdicRing.of_surjective_of_noetherian`
  produce a complete adic ring from a surjection with no extra closedness input.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.3.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. 0, §7.
-/

noncomputable section

open Ideal

universe u

variable {B : Type u} [CommRing B]

/-- The kernel of `ψ` is **adically closed** for the `K`-adic topology: any element which is,
modulo every power of `K`, congruent to an element of the kernel lies in the kernel. In the
noetherian setting this is automatic (Artin–Rees/Krull intersection); in general it is a
genuine hypothesis. -/
def RingHom.AdicKerClosed {A : Type u} [CommRing A] (K : Ideal B) (ψ : B →+* A) : Prop :=
  ∀ x : B, (∀ n : ℕ, ∃ k ∈ RingHom.ker ψ, x - k ∈ K ^ n) → x ∈ RingHom.ker ψ

variable {A : Type u} [CommRing A] [Algebra B A] (K : Ideal B)

theorem mem_smul_top_iff_mem_map {n : ℕ} (x : A) :
    x ∈ (K ^ n • ⊤ : Submodule B A) ↔ x ∈ (K ^ n).map (algebraMap B A) := by
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]

/-- **Quotients of precomplete rings are precomplete**: if `B` is `K`-adically precomplete and
the structure map `B → A` is surjective, then `A` is `K`-adically precomplete. -/
theorem IsPrecomplete.of_surjective_algebraMap [IsPrecomplete K B]
    (hs : Function.Surjective (algebraMap B A)) : IsPrecomplete K A := by
  constructor
  intro f hf
  -- lift the sequence to a Cauchy sequence in `B`, correcting term by term
  have hdiff : ∀ n : ℕ, ∃ c ∈ K ^ n, algebraMap B A c = f (n + 1) - f n := by
    intro n
    have h := SModEq.sub_mem.mp (hf (Nat.le_succ n))
    rw [mem_smul_top_iff_mem_map] at h
    obtain ⟨c, hc, hcx⟩ := Ideal.mem_map_iff_of_surjective _ hs |>.mp (neg_mem h)
    exact ⟨c, hc, by rw [hcx]; ring⟩
  choose c hc hcψ using hdiff
  obtain ⟨b₀, hb₀⟩ := hs (f 0)
  -- the lifted sequence: `b n = b₀ + Σ_{i<n} c i`
  set b : ℕ → B := fun n => b₀ + (Finset.range n).sum c with hb
  have hψb : ∀ n, algebraMap B A (b n) = f n := by
    intro n
    induction n with
    | zero => simpa [hb] using hb₀
    | succ n ih =>
      have hstep : b (n + 1) = b n + c n := by
        simp [hb, Finset.sum_range_succ, add_assoc]
      rw [hstep, map_add, ih, hcψ n]
      ring
  have hbc : ∀ {m n : ℕ}, m ≤ n → b m ≡ b n [SMOD (K ^ m • ⊤ : Submodule B B)] := by
    intro m n hmn
    rw [SModEq.sub_mem]
    have hsum : b n - b m = (Finset.Ico m n).sum c := by
      simp only [hb]
      rw [← Finset.sum_range_add_sum_Ico c hmn]
      ring
    rw [show b m - b n = -(b n - b m) by ring, hsum]
    refine neg_mem (Submodule.sum_mem _ fun i hi => ?_)
    have hKm : c i ∈ K ^ m := Ideal.pow_le_pow_right (Finset.mem_Ico.mp hi).1 (hc i)
    rw [mem_smul_top_iff_mem_map]
    simpa using Ideal.mem_map_of_mem (algebraMap B B) hKm
  obtain ⟨L, hL⟩ := IsPrecomplete.prec ‹IsPrecomplete K B› @hbc
  refine ⟨algebraMap B A L, fun n => ?_⟩
  rw [SModEq.sub_mem, ← hψb n, ← map_sub, mem_smul_top_iff_mem_map]
  have h1 : b n - L ∈ (K ^ n).map (algebraMap B B) := by
    rw [← mem_smul_top_iff_mem_map]
    exact SModEq.sub_mem.mp (hL n)
  rw [Algebra.algebraMap_self, Ideal.map_id] at h1
  exact Ideal.mem_map_of_mem _ h1

/-- **Quotients by adically closed ideals are Hausdorff**: if the structure map `B → A` is
surjective with `K`-adically closed kernel, then `A` is `K`-adically Hausdorff. -/
theorem IsHausdorff.of_surjective_of_kerClosed
    (hs : Function.Surjective (algebraMap B A))
    (hker : (algebraMap B A).AdicKerClosed K) : IsHausdorff K A := by
  constructor
  intro x hx
  obtain ⟨y, rfl⟩ := hs x
  have hy : y ∈ RingHom.ker (algebraMap B A) := by
    refine hker y fun n => ?_
    have h := SModEq.zero.mp (hx n)
    rw [mem_smul_top_iff_mem_map] at h
    obtain ⟨d, hd, hdy⟩ := Ideal.mem_map_iff_of_surjective _ hs |>.mp h
    refine ⟨y - d, ?_, by simpa using hd⟩
    rw [RingHom.mem_ker, map_sub, hdy, sub_self]
  rwa [RingHom.mem_ker] at hy

/-- Quotients of complete rings by adically closed ideals are complete (for the filtration
`K ^ n • ⊤`). -/
theorem IsAdicComplete.of_surjective_of_kerClosed [IsAdicComplete K B]
    (hs : Function.Surjective (algebraMap B A))
    (hker : (algebraMap B A).AdicKerClosed K) : IsAdicComplete K A where
  toIsHausdorff := IsHausdorff.of_surjective_of_kerClosed K hs hker
  toIsPrecomplete := IsPrecomplete.of_surjective_algebraMap K hs

/-- **Quotients of complete adic rings by adically closed ideals are complete adic rings**, for
the extended ideal `K.map (algebraMap B A)` with its adic topology. -/
theorem IsAdicRing.of_surjective_of_kerClosed [IsAdicComplete K B]
    (hs : Function.Surjective (algebraMap B A))
    (hker : (algebraMap B A).AdicKerClosed K) :
    letI : TopologicalSpace A := (K.map (algebraMap B A)).adicTopology
    IsAdicRing (K.map (algebraMap B A)) := by
  letI : TopologicalSpace A := (K.map (algebraMap B A)).adicTopology
  have hc : IsAdicComplete K A := IsAdicComplete.of_surjective_of_kerClosed K hs hker
  exact
    { toIsAdicComplete := IsAdicComplete.map_algebraMap K hc
      isAdic := rfl }

/-- **Noetherian case: kernels are automatically adically closed.** If `B` is a Noetherian ring,
`K`-adically complete, and the structure map `B → A` is surjective, then the kernel of `B → A`
is `K`-adically closed. The point is Krull's intersection theorem: `A` is a finite `B`-module (a
surjective image of `B`), so it is `K`-adically Hausdorff because `K` lies in the Jacobson
radical of a complete ring (`IsHausdorff.of_le_jacobson`, `IsAdicComplete.le_jacobson_bot`); an
element of `B` congruent to the kernel modulo every `K ^ n` therefore maps into every
`K ^ n • ⊤` and so to `0`. This makes the closedness hypothesis of the lemmas above automatic in
the Noetherian setting (Artin–Rees, Bosch §7.3). -/
theorem RingHom.adicKerClosed_of_noetherian [IsNoetherianRing B] [IsAdicComplete K B]
    (hs : Function.Surjective (algebraMap B A)) : (algebraMap B A).AdicKerClosed K := by
  haveI : Module.Finite B A := Module.Finite.of_surjective (Algebra.linearMap B A) hs
  haveI hH : IsHausdorff K A := IsHausdorff.of_le_jacobson K A (IsAdicComplete.le_jacobson_bot K)
  intro x hx
  rw [RingHom.mem_ker]
  refine hH.haus (algebraMap B A x) fun n => ?_
  rw [SModEq.zero, mem_smul_top_iff_mem_map]
  obtain ⟨k, hk, hxk⟩ := hx n
  have hk0 : algebraMap B A k = 0 := RingHom.mem_ker.mp hk
  have hxx : algebraMap B A x = algebraMap B A (x - k) := by rw [map_sub, hk0, sub_zero]
  rw [hxx]
  exact Ideal.mem_map_of_mem _ hxk

/-- **Quotients of Noetherian complete adic rings are complete adic**, with no closedness
hypothesis: for `B` Noetherian and `K`-adically complete and `B → A` surjective, `A` is
`K`-adically complete. Combines `adicKerClosed_of_noetherian` with
`IsAdicComplete.of_surjective_of_kerClosed`. -/
theorem IsAdicComplete.of_surjective_of_noetherian [IsNoetherianRing B] [IsAdicComplete K B]
    (hs : Function.Surjective (algebraMap B A)) : IsAdicComplete K A :=
  IsAdicComplete.of_surjective_of_kerClosed K hs (RingHom.adicKerClosed_of_noetherian K hs)

/-- **Quotients of Noetherian complete adic rings are complete adic rings**, for the extended
ideal `K.map (algebraMap B A)` with its adic topology and with no closedness hypothesis. This is
the Noetherian specialization of `IsAdicRing.of_surjective_of_kerClosed`. -/
theorem IsAdicRing.of_surjective_of_noetherian [IsNoetherianRing B] [IsAdicComplete K B]
    (hs : Function.Surjective (algebraMap B A)) :
    letI : TopologicalSpace A := (K.map (algebraMap B A)).adicTopology
    IsAdicRing (K.map (algebraMap B A)) :=
  IsAdicRing.of_surjective_of_kerClosed K hs (RingHom.adicKerClosed_of_noetherian K hs)
