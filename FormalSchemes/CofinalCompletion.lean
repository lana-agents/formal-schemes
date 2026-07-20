import FormalSchemes.AdicCompletionLimit
import FormalSchemes.IdealsOfDefinition

set_option linter.style.header false

/-!
# Cofinal ideals have isomorphic adic completions

Two ideals `K`, `L` of a commutative ring `S` are *cofinal* if some power of each is contained in
the other (`K ^ b ≤ L` and `L ^ a ≤ K`); equivalently, they induce the same adic topology. This
file proves that cofinal ideals have canonically isomorphic adic completions:
```
AdicCompletion K S ≃+* AdicCompletion L S.
```

This is the commutative-algebra core of the fact that the affine formal scheme `Spf R` depends only
on the topological ring `R`, not on the chosen ideal of definition (EGA I, §10.3, goal 1 of the
structure-sheaf intertwining). The structure sheaf `O_{Spf R}` has, on a basic open `D(f)`, the
ring of sections `AdicCompletion (I · R_f) R_f` (issues 26–30); when `I`, `J` are two ideals of
definition of `R`, the ideals `I · R_f`, `J · R_f` are cofinal in `R_f`
(`nonempty_cofinalRingEquiv_map`), so the two structure sheaves agree on basic opens as rings.

## Main definitions and results

* `AdicCompletion.cofinalHom hb`: the ring homomorphism
  `AdicCompletion K S →+* AdicCompletion L S` induced by a containment `K ^ b ≤ L`, from
  the universal property of the completion applied to the factor maps
  `S ⧸ K ^ ((b + 1) * n) →+* S ⧸ L ^ n`.
* `AdicCompletion.cofinalRingEquiv hb ha`: the ring isomorphism
  `AdicCompletion K S ≃+* AdicCompletion L S` for cofinal `K`, `L`.
* `AdicCompletion.nonempty_cofinalRingEquiv_map`: two ideals of definition `I`, `J` of a
  topological ring `R` have, along any ring homomorphism `f : R →+* S`, isomorphic completions
  `AdicCompletion (I.map f) S ≃+* AdicCompletion (J.map f) S`. This is the ring-of-sections
  incarnation of `Spf`-independence.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], §10.3.
* [The Stacks Project, Tag 0AHZ](https://stacks.math.columbia.edu/tag/0AHZ).
-/

noncomputable section

open Topology

namespace AdicCompletion

universe u

variable {S : Type u} [CommRing S] {K L : Ideal S}

/-- If `K ^ b ≤ L`, then `K ^ ((b + 1) * n) ≤ L ^ n`. The shift `b + 1` guarantees the exponent
`(b + 1) * n` is at least `n`, which is convenient when composing the two directions of the
cofinality isomorphism. -/
theorem pow_mul_le_pow (hb : K ^ b ≤ L) (n : ℕ) : K ^ ((b + 1) * n) ≤ L ^ n := by
  rw [pow_mul]
  exact Ideal.pow_right_mono ((Ideal.pow_le_pow_right (Nat.le_succ b)).trans hb) n

/-- The `n`-th component `AdicCompletion K S →+* S ⧸ L ^ n` of the cofinal comparison map: the
factor map `S ⧸ K ^ ((b + 1) * n) →+* S ⧸ L ^ n` (well-defined by `pow_mul_le_pow`)
precomposed with the evaluation `evalₐ K ((b + 1) * n)`. -/
def cofinalLevel (hb : K ^ b ≤ L) (n : ℕ) : AdicCompletion K S →+* S ⧸ L ^ n :=
  (Ideal.Quotient.factor (pow_mul_le_pow hb n)).comp (evalₐ K ((b + 1) * n) : _ →+* _)

theorem cofinalLevel_apply (hb : K ^ b ≤ L) (n : ℕ) (x : AdicCompletion K S) :
    cofinalLevel hb n x =
      Ideal.Quotient.factor (pow_mul_le_pow hb n) (evalₐ K ((b + 1) * n) x) :=
  rfl

/-- The comparison components `cofinalLevel` are compatible with the factor maps of the `L`-adic
tower: `factorPow L hle` after level `n` is level `m`. This is the cocone condition that lets them
be assembled by the universal property of `AdicCompletion L S`. -/
theorem factorPow_cofinalLevel (hb : K ^ b ≤ L) {m n : ℕ} (hle : m ≤ n)
    (x : AdicCompletion K S) :
    Ideal.Quotient.factorPow L hle (cofinalLevel hb n x) = cofinalLevel hb m x := by
  rw [cofinalLevel_apply, cofinalLevel_apply,
    show (Ideal.Quotient.factorPow L hle) =
      Ideal.Quotient.factor (Ideal.pow_le_pow_right hle) from rfl,
    Ideal.Quotient.factor_comp_apply,
    ← factorPow_evalₐ K (Nat.mul_le_mul_left (b + 1) hle) x,
    show (Ideal.Quotient.factorPow K (Nat.mul_le_mul_left (b + 1) hle)) =
      Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.mul_le_mul_left (b + 1) hle)) from rfl,
    Ideal.Quotient.factor_comp_apply]

theorem factorPow_comp_cofinalLevel (hb : K ^ b ≤ L) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow L hle).comp (cofinalLevel hb n) = cofinalLevel hb m :=
  RingHom.ext (factorPow_cofinalLevel hb hle)

/-- The **cofinal comparison map** `AdicCompletion K S →+* AdicCompletion L S` induced by a
containment `K ^ b ≤ L`, obtained from the universal property of the `L`-adic completion applied
to the compatible family `cofinalLevel`. -/
def cofinalHom (hb : K ^ b ≤ L) : AdicCompletion K S →+* AdicCompletion L S :=
  AdicCompletion.liftRingHom L (cofinalLevel hb) (fun hle => factorPow_comp_cofinalLevel hb hle)

@[simp]
theorem evalₐ_cofinalHom (hb : K ^ b ≤ L) (n : ℕ) (x : AdicCompletion K S) :
    evalₐ L n (cofinalHom hb x) = cofinalLevel hb n x :=
  evalₐ_liftRingHom L _ _ n x

/-- The two cofinal comparison maps for `K ^ b ≤ L` and `L ^ a ≤ K` are mutually inverse:
composing them collapses, on each level, to an evaluation of the same completion via
`factorPow_evalₐ`. -/
theorem cofinalHom_comp_cofinalHom (hb : K ^ b ≤ L) (ha : L ^ a ≤ K) :
    (cofinalHom ha).comp (cofinalHom hb) = RingHom.id (AdicCompletion K S) := by
  refine RingHom.ext fun x => AdicCompletion.ext_evalₐ fun n => ?_
  have hnE : n ≤ (b + 1) * ((a + 1) * n) :=
    (Nat.le_mul_of_pos_left n (Nat.succ_pos a)).trans
      (Nat.le_mul_of_pos_left ((a + 1) * n) (Nat.succ_pos b))
  rw [RingHom.comp_apply, RingHom.id_apply, evalₐ_cofinalHom, cofinalLevel_apply,
    evalₐ_cofinalHom, cofinalLevel_apply, Ideal.Quotient.factor_comp_apply,
    ← factorPow_evalₐ K hnE x,
    show Ideal.Quotient.factorPow K hnE
        = Ideal.Quotient.factor (Ideal.pow_le_pow_right hnE) from rfl]

/-- **Cofinal ideals have isomorphic adic completions.** If `K ^ b ≤ L` and `L ^ a ≤ K` (so `K`
and `L` induce the same adic topology on `S`), the two adic completions are canonically
isomorphic. -/
def cofinalRingEquiv (hb : K ^ b ≤ L) (ha : L ^ a ≤ K) :
    AdicCompletion K S ≃+* AdicCompletion L S :=
  RingEquiv.ofRingHom (cofinalHom hb) (cofinalHom ha)
    (cofinalHom_comp_cofinalHom ha hb) (cofinalHom_comp_cofinalHom hb ha)

@[simp]
theorem cofinalRingEquiv_apply (hb : K ^ b ≤ L) (ha : L ^ a ≤ K) (x : AdicCompletion K S) :
    cofinalRingEquiv hb ha x = cofinalHom hb x :=
  rfl

@[simp]
theorem cofinalRingEquiv_symm_apply (hb : K ^ b ≤ L) (ha : L ^ a ≤ K) (x : AdicCompletion L S) :
    (cofinalRingEquiv hb ha).symm x = cofinalHom ha x :=
  rfl

/-- The existence form: cofinal ideals (some power of each inside the other) have isomorphic
completions. -/
theorem nonempty_cofinalRingEquiv (hKL : ∃ b, K ^ b ≤ L) (hLK : ∃ a, L ^ a ≤ K) :
    Nonempty (AdicCompletion K S ≃+* AdicCompletion L S) :=
  let ⟨_, hb⟩ := hKL
  let ⟨_, ha⟩ := hLK
  ⟨cofinalRingEquiv hb ha⟩

variable {R : Type u} [CommRing R] [TopologicalSpace R] {I J : Ideal R}

/-- **Ring-of-sections incarnation of `Spf`-independence.** Two ideals of definition `I`, `J` of a
topological ring `R` have, along any ring homomorphism `f : R →+* S`, isomorphic adic completions
`AdicCompletion (I.map f) S ≃+* AdicCompletion (J.map f) S`.

Applied to the localization map `f : R →+* R_f`, this says the two descriptions
`AdicCompletion (I · R_f) R_f` and `AdicCompletion (J · R_f) R_f` of the sections of `O_{Spf R}`
on the basic open `D(f)` agree: the structure sheaf does not depend on the chosen ideal of
definition. -/
theorem nonempty_cofinalRingEquiv_map (f : R →+* S) (hI : IsAdic I) (hJ : IsAdic J) :
    Nonempty (AdicCompletion (I.map f) S ≃+* AdicCompletion (J.map f) S) := by
  obtain ⟨a, ha⟩ := hI.exists_pow_le hJ
  obtain ⟨b, hb⟩ := hJ.exists_pow_le hI
  refine nonempty_cofinalRingEquiv ⟨b, ?_⟩ ⟨a, ?_⟩
  · rw [← Ideal.map_pow]
    exact Ideal.map_mono hb
  · rw [← Ideal.map_pow]
    exact Ideal.map_mono ha

end AdicCompletion
