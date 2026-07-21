import FormalSchemes.AssociatedGraded
import FormalSchemes.Completion

set_option linter.style.header false

/-!
# Completion preserves the associated graded ring

For a commutative ring `B` and a finitely generated ideal `K : Ideal B`, let
`B̂ = AdicCompletion K B` be the `K`-adic completion and `K̂ = K·B̂` its ideal of definition.
Because completion does not change the infinitesimal thickenings
(`B̂ ⧸ K̂ ^ n ≅ B ⧸ K ^ n`, `AdicCompletion.quotientEquivPow`), the associated graded rings
agree:
```
gr_{K̂}(B̂) ≅ gr_K(B).
```

This is Atiyah–Macdonald's observation (Ch. 10, used in Prop. 10.26) that completion preserves
the associated graded. Its only downstream consumer (issue 145 / AM 10.26) needs it in the
form of a **Noetherian transport**: `gr_{K̂}(B̂)` is Noetherian whenever `B` is. We deliver
exactly that, via a *surjective* ring homomorphism

```
AssociatedGraded.completionHom : gr_K(B) →+* gr_{K̂}(B̂),
```

induced by the completion map `B → B̂` (which carries `K` into `K̂`), and then transport
Noetherianness along it. Surjectivity — the substantive content — rests on the fact that,
modulo `K̂ ^ (n+1)`, every element of `K̂ ^ n` is congruent to the image of an element of
`K ^ n` (`AssociatedGraded.exists_approx`), which in turn uses the density of `B` in `B̂`
(`AssociatedGraded.exists_sub_mem`).

We choose the surjection-plus-transport route (explicitly sanctioned by the issue) rather than a
full graded-ring isomorphism: the direction `gr_K(B) →+* gr_{K̂}(B̂)` is the one the completion
map `B → B̂` produces directly (there is no ring map `B̂ → B` to build the other direction), and
Noetherian transport is all that AM 10.26 consumes.

## Main results

* `AssociatedGraded.completionHom`: the ring homomorphism `gr_K(B) →+* gr_{K̂}(B̂)` induced by
  the completion map, with `completionHom_deg` describing its action on leading forms.
* `AssociatedGraded.completionHom_surjective`: it is surjective (for `K` finitely generated).
* `AssociatedGraded.isNoetherianRing_completion`: **completion preserves Noetherianness of the
  associated graded** — `gr_{K̂}(B̂)` is Noetherian when `B` is Noetherian and `K` is finitely
  generated. This is the transport corollary AM 10.26 (issue 145) consumes.

## References

* [Atiyah–Macdonald, *Introduction to Commutative Algebra*], Ch. 10 (completion preserves the
  associated graded, used in Prop. 10.26).
* [The Stacks Project, Tag 05GH](https://stacks.math.columbia.edu/tag/05GH).
-/

open Polynomial

noncomputable section

universe u

variable {B : Type u} [CommRing B] (K : Ideal B)

namespace AssociatedGraded

/-- The completion structure map `B → B̂` agrees with `AdicCompletion.of`. -/
theorem algebraMap_eq_of (x : B) :
    algebraMap B (AdicCompletion K B) x = AdicCompletion.of K B x := by
  rw [AdicCompletion.algebraMap_apply]; rfl

/-- The completion map carries `K ^ n` into `K̂ ^ n`. -/
theorem algebraMap_mem_pow (n : ℕ) {x : B} (hx : x ∈ K ^ n) :
    algebraMap B (AdicCompletion K B) x ∈ (AdicCompletion.idealOfDefinition K) ^ n := by
  rw [← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hx

/-- The completion map `B → B̂` lifts to the Rees algebras: since it carries `K ^ i` into
`K̂ ^ i`, mapping coefficients gives a ring homomorphism `reesAlgebra K → reesAlgebra K̂`. -/
def reesMap : reesAlgebra K →+* reesAlgebra (AdicCompletion.idealOfDefinition K) where
  toFun p := ⟨(p : B[X]).map (algebraMap B (AdicCompletion K B)), by
    rw [mem_reesAlgebra_iff]
    intro i
    rw [Polynomial.coeff_map, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ (p.2 i)⟩
  map_one' := Subtype.ext (by simp only [OneMemClass.coe_one, Polynomial.map_one])
  map_mul' a b := Subtype.ext (by
    simp only [MulMemClass.coe_mul, Polynomial.map_mul])
  map_zero' := Subtype.ext (by simp only [ZeroMemClass.coe_zero, Polynomial.map_zero])
  map_add' a b := Subtype.ext (by
    simp only [AddMemClass.coe_add, Polynomial.map_add])

@[simp] theorem reesMap_coe (p : reesAlgebra K) :
    ((reesMap K p : reesAlgebra (AdicCompletion.idealOfDefinition K)) : (AdicCompletion K B)[X]) =
      (p : B[X]).map (algebraMap B (AdicCompletion K B)) := rfl

/-- `reesMap` sends the constant `k` (`k ∈ K`) to the constant `algebraMap k` in the target Rees
algebra. -/
theorem reesMap_algebraMap (k : B) :
    reesMap K (algebraMap B (reesAlgebra K) k) =
      algebraMap (AdicCompletion K B) (reesAlgebra (AdicCompletion.idealOfDefinition K))
        (algebraMap B (AdicCompletion K B) k) := by
  apply Subtype.ext
  rw [reesMap_coe,
    show ((algebraMap B (reesAlgebra K) k : reesAlgebra K) : B[X]) = C k from by
      simp [Polynomial.algebraMap_eq],
    show ((algebraMap (AdicCompletion K B) (reesAlgebra (AdicCompletion.idealOfDefinition K))
        (algebraMap B (AdicCompletion K B) k)) :
        (AdicCompletion K B)[X]) = C (algebraMap B (AdicCompletion K B) k) from by
      simp [Polynomial.algebraMap_eq],
    Polynomial.map_C]

/-- **Completion induces a map on associated graded rings.** The completion map `B → B̂` carries
`K` into `K̂`, hence descends to a ring homomorphism `gr_K(B) →+* gr_{K̂}(B̂)`. -/
def completionHom : AssociatedGraded K →+* AssociatedGraded (AdicCompletion.idealOfDefinition K) :=
  Ideal.Quotient.lift (shiftIdeal K)
    ((mk (AdicCompletion.idealOfDefinition K)).comp (reesMap K)) (by
      have hle : shiftIdeal K ≤
          RingHom.ker ((mk (AdicCompletion.idealOfDefinition K)).comp (reesMap K)) := by
        rw [shiftIdeal, Ideal.map_le_iff_le_comap]
        intro k hk
        rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply, reesMap_algebraMap,
          mk_eq_zero_iff]
        exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hk)
      exact fun a ha => hle ha)

@[simp] theorem completionHom_mk (p : reesAlgebra K) :
    completionHom K (mk K p) = mk (AdicCompletion.idealOfDefinition K) (reesMap K p) :=
  Ideal.Quotient.lift_mk _ _ _

/-- The action of `completionHom` on a leading form: `deg K n k ↦ deg K̂ n (algebraMap k)`. -/
theorem completionHom_deg (n : ℕ) (k : (K ^ n : Ideal B)) :
    completionHom K (deg K n k) =
      deg (AdicCompletion.idealOfDefinition K) n
        ⟨algebraMap B (AdicCompletion K B) (k : B), algebraMap_mem_pow K n k.2⟩ := by
  have hmon : reesMap K (monomialRees K n k) =
      monomialRees (AdicCompletion.idealOfDefinition K) n
        ⟨algebraMap B (AdicCompletion K B) (k : B), algebraMap_mem_pow K n k.2⟩ := by
    apply Subtype.ext
    rw [reesMap_coe, monomialRees_coe, monomialRees_coe, Polynomial.map_monomial]
  rw [deg_apply, completionHom_mk, hmon, ← deg_apply]

/-- **Density of `B` in its completion**: every element of `B̂` is congruent modulo `K̂` to the
image of an element of `B`. -/
theorem exists_sub_mem (hK : K.FG) (b : AdicCompletion K B) :
    ∃ b₀ : B,
      b - algebraMap B (AdicCompletion K B) b₀ ∈ AdicCompletion.idealOfDefinition K := by
  obtain ⟨b₀, hb₀⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ K 1 b)
  refine ⟨b₀, ?_⟩
  have hzero : AdicCompletion.evalₐ K 1 (b - algebraMap B (AdicCompletion K B) b₀) = 0 := by
    rw [map_sub, algebraMap_eq_of, AdicCompletion.evalₐ_of, hb₀, sub_self]
  have hmem : b - algebraMap B (AdicCompletion K B) b₀ ∈
      (AdicCompletion.idealOfDefinition K) ^ 1 := by
    rw [← AdicCompletion.ker_evalₐ K hK 1, RingHom.mem_ker]
    exact hzero
  rwa [pow_one] at hmem

/-- Auxiliary ideal for the successive-approximation step: those `c ∈ B̂` for which some
`k ∈ K ^ n` has `c - algebraMap k ∈ K̂ ^ (n+1)`. Closure under `B̂`-multiplication is exactly the
density argument. -/
def approxIdeal (hK : K.FG) (n : ℕ) : Ideal (AdicCompletion K B) where
  carrier := {c | ∃ k : B, k ∈ K ^ n ∧
    c - algebraMap B (AdicCompletion K B) k ∈ (AdicCompletion.idealOfDefinition K) ^ (n + 1)}
  zero_mem' := ⟨0, zero_mem _, by rw [map_zero, sub_zero]; exact zero_mem _⟩
  add_mem' := by
    rintro a b ⟨k, hk, ha⟩ ⟨l, hl, hb⟩
    exact ⟨k + l, add_mem hk hl, by rw [map_add]; convert add_mem ha hb using 1; ring⟩
  smul_mem' := by
    rintro b c ⟨k, hk, hc⟩
    obtain ⟨b₀, hb₀⟩ := exists_sub_mem K hK b
    refine ⟨b₀ * k, Ideal.mul_mem_left _ b₀ hk, ?_⟩
    have halgk : algebraMap B (AdicCompletion K B) k ∈ (AdicCompletion.idealOfDefinition K) ^ n :=
      algebraMap_mem_pow K n hk
    have e : b • c - algebraMap B (AdicCompletion K B) (b₀ * k) =
        b * (c - algebraMap B (AdicCompletion K B) k) +
          (b - algebraMap B (AdicCompletion K B) b₀) * algebraMap B (AdicCompletion K B) k := by
      rw [map_mul, smul_eq_mul]; ring
    rw [e]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hc) ?_
    rw [pow_succ']
    exact Ideal.mul_mem_mul hb₀ halgk

/-- **The successive-approximation step** (the heart of "completion preserves the associated
graded"): every element of `K̂ ^ n` is, modulo `K̂ ^ (n+1)`, the image of an element of `K ^ n`. -/
theorem exists_approx (hK : K.FG) (n : ℕ) {c : AdicCompletion K B}
    (hc : c ∈ (AdicCompletion.idealOfDefinition K) ^ n) :
    ∃ k : B, k ∈ K ^ n ∧
      c - algebraMap B (AdicCompletion K B) k ∈ (AdicCompletion.idealOfDefinition K) ^ (n + 1) := by
  have hle : (AdicCompletion.idealOfDefinition K) ^ n ≤ approxIdeal K hK n := by
    rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap]
    exact ⟨x, hx, by rw [sub_self]; exact zero_mem _⟩
  exact hle hc

/-- **`completionHom` is surjective** (for `K` finitely generated): each graded piece
`K̂ ^ n / K̂ ^ (n+1)` is hit, because every element of `K̂ ^ n` agrees modulo `K̂ ^ (n+1)` with the
image of an element of `K ^ n`. -/
theorem completionHom_surjective (hK : K.FG) : Function.Surjective (completionHom K) := by
  intro y
  obtain ⟨p, rfl⟩ := mk_surjective (AdicCompletion.idealOfDefinition K) y
  have hp : mk (AdicCompletion.idealOfDefinition K) p =
      ∑ i ∈ (p : (AdicCompletion K B)[X]).support,
        deg (AdicCompletion.idealOfDefinition K) i
          ⟨(p : (AdicCompletion K B)[X]).coeff i, p.2 i⟩ := by
    have hpsum : p = ∑ i ∈ (p : (AdicCompletion K B)[X]).support,
        monomialRees (AdicCompletion.idealOfDefinition K) i
          ⟨(p : (AdicCompletion K B)[X]).coeff i, p.2 i⟩ := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      simp only [monomialRees_coe]
      exact (Polynomial.as_sum_support (p : (AdicCompletion K B)[X]))
    conv_lhs => rw [hpsum]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [← deg_apply]
  rw [hp]
  refine RingHom.mem_range.mp (Subring.sum_mem _ fun i _ => ?_)
  obtain ⟨k, hk, hdiff⟩ := exists_approx K hK i (p.2 i)
  refine RingHom.mem_range.mpr ⟨deg K i ⟨k, hk⟩, ?_⟩
  rw [completionHom_deg]
  have hz : deg (AdicCompletion.idealOfDefinition K) i
      (⟨(p : (AdicCompletion K B)[X]).coeff i, p.2 i⟩ -
        ⟨algebraMap B (AdicCompletion K B) k, algebraMap_mem_pow K i hk⟩) = 0 := by
    apply deg_eq_zero_of_mem_succ
    simpa only [Submodule.coe_sub] using hdiff
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

/-- **Completion preserves Noetherianness of the associated graded** (Atiyah–Macdonald 10.26).
When `B` is Noetherian and `K` is finitely generated, `gr_K(B)` is Noetherian, and it surjects
onto `gr_{K̂}(B̂)`; hence the latter is Noetherian too. This is the input to AM 10.26 (issue 145),
where `B̂ = AdicCompletion K B` is complete and separated but *not yet known* to be Noetherian. -/
theorem isNoetherianRing_completion [IsNoetherianRing B] (hK : K.FG) :
    IsNoetherianRing (AssociatedGraded (AdicCompletion.idealOfDefinition K)) :=
  isNoetherianRing_of_surjective (AssociatedGraded K) _ (completionHom K)
    (completionHom_surjective K hK)

end AssociatedGraded
