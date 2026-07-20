import FormalSchemes.FormalScheme
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.RingHom
import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
import Mathlib.Algebra.MvPolynomial.CommRing

set_option linter.style.header false

/-!
# Restricted power series and the formal polydisc

For an adic ring `R` with ideal of definition `I`, the ring of **restricted power series**
`R{X₁, …, Xₙ}` is the ring of formal power series whose coefficients tend to zero `I`-adically;
equivalently, the `I`-adic completion of the polynomial ring `R[X₁, …, Xₙ]` (Bosch,
*Lectures on Formal and Rigid Geometry*, §7; Stacks, Tag 0AKA). Its formal spectrum is the
**formal polydisc** over `Spf R`, the building block of all formal schemes topologically of
finite type over `R` — in particular of the Tate-curve constructions.

**Design.** We *define* `RestrictedPowerSeries R I n` as
`AdicCompletion (I·R[X]) (MvPolynomial (Fin n) R)`; the description by null coefficient
sequences is then a theorem about `AdicCompletion` (not needed for the formal-geometry layer,
and left to future work). This makes the completion API of `Mathlib.RingTheory.AdicCompletion`
and of `FormalSchemes/AdicCompletionLimit.lean` directly available, at the price of the
definitional unfolding being a completion rather than a subring of power series.

On the way we provide the general facts, for a finitely generated ideal `K` of a commutative
ring `B`:

* the completion `AdicCompletion K B` is an adic ring for the extension of `K`
  (`AdicCompletion.isAdicRing_map`), via the transfer lemma
  `IsAdicComplete.map_algebraMap` identifying `K`-adic and `K·A`-adic completeness of a
  `B`-algebra `A`;
* consequently `Spf` of a completion makes sense, giving the **formal polydisc**
  `RestrictedPowerSeries.formalPolydisc` as a formal scheme.

Finally we construct the **evaluation maps** (the existence half of the universal property of
the polydisc, Bosch §7): for a complete adic `R`-algebra `S` and any `n`-tuple `s` of elements
of `S`, there is a ring homomorphism `R{X₁, …, Xₙ} →+* S` restricting to `p ↦ aeval s p` on
polynomials (`RestrictedPowerSeries.evalHom`, `RestrictedPowerSeries.evalHom_of`).

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
* [The Stacks Project, Tag 0AKA](https://stacks.math.columbia.edu/tag/0AKA)
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. 0, §7.5.
-/

noncomputable section

open Ideal AlgebraicGeometry

universe u

/-!
### `K`-adic versus `K·A`-adic completeness

`IsAdicComplete K A` for a `B`-algebra `A` is phrased through the submodules `K ^ n • ⊤` of
`A` as a `B`-module; the ring-theoretic notion for `A` uses the powers of the extended ideal
`K·A`. The two coincide, since `K ^ n • ⊤` and `(K·A) ^ n` have the same underlying set.
-/

section Transfer

variable {B : Type u} [CommRing B] {A : Type u} [CommRing A] [Algebra B A] (K : Ideal B)

theorem Ideal.mem_map_pow_iff_mem_smul_top (n : ℕ) (x : A) :
    x ∈ ((K.map (algebraMap B A)) ^ n • ⊤ : Submodule A A) ↔
      x ∈ (K ^ n • ⊤ : Submodule B A) := by
  rw [Ideal.smul_top_eq_map (K ^ n), Submodule.restrictScalars_mem,
    Ideal.smul_top_eq_map ((K.map (algebraMap B A)) ^ n), Submodule.restrictScalars_mem,
    Algebra.algebraMap_self, Ideal.map_id, ← Ideal.map_pow]

/-- Adic completeness transfers from the `B`-module structure to the `A`-ring structure: if a
`B`-algebra `A` is `K`-adically complete as a `B`-module, it is complete for the extended
ideal `K·A`. -/
theorem IsAdicComplete.map_algebraMap (h : IsAdicComplete K A) :
    IsAdicComplete (K.map (algebraMap B A)) A where
  haus' x hx :=
    h.toIsHausdorff.haus x fun n => SModEq.zero.mpr
      ((Ideal.mem_map_pow_iff_mem_smul_top K n x).mp (SModEq.zero.mp (hx n)))
  prec' f hf := by
    obtain ⟨L, hL⟩ := h.toIsPrecomplete.prec (f := f) (fun {m n} hmn =>
      SModEq.sub_mem.mpr ((Ideal.mem_map_pow_iff_mem_smul_top K m _).mp
        (SModEq.sub_mem.mp (hf hmn))))
    exact ⟨L, fun n => SModEq.sub_mem.mpr
      ((Ideal.mem_map_pow_iff_mem_smul_top K n _).mpr (SModEq.sub_mem.mp (hL n)))⟩

end Transfer

/-!
### The completion of a ring is an adic ring
-/

namespace AdicCompletion

variable {B : Type u} [CommRing B] (K : Ideal B)

/-- The topology on the completion `AdicCompletion K B`: the adic topology of the extension of
`K`. -/
instance : TopologicalSpace (AdicCompletion K B) :=
  (K.map (algebraMap B (AdicCompletion K B))).adicTopology

theorem isAdic_map : IsAdic (K.map (algebraMap B (AdicCompletion K B))) :=
  rfl

/-- The completion of a ring at a finitely generated ideal `K` is complete for the extension
of `K`. -/
theorem isAdicComplete_map (hK : K.FG) :
    IsAdicComplete (K.map (algebraMap B (AdicCompletion K B))) (AdicCompletion K B) :=
  IsAdicComplete.map_algebraMap K (AdicCompletion.isAdicComplete hK)

/-- The completion of a ring at a finitely generated ideal `K` is an **adic ring** with ideal
of definition the extension of `K`; in particular its formal spectrum is an affine formal
scheme. -/
theorem isAdicRing_map (hK : K.FG) :
    IsAdicRing (K.map (algebraMap B (AdicCompletion K B))) where
  toIsAdicComplete := isAdicComplete_map K hK
  isAdic := isAdic_map K

end AdicCompletion

/-!
### Restricted power series
-/

variable (R : Type u) [CommRing R] (I : Ideal R) (n : ℕ)

/-- The ring of **restricted power series** `R{X₁, …, Xₙ}` over `R` relative to the ideal `I`:
the power series whose coefficients tend to zero `I`-adically, realized as the `I`-adic
completion of the polynomial ring `R[X₁, …, Xₙ]` (see the module docstring for this design
choice). -/
abbrev RestrictedPowerSeries : Type u :=
  AdicCompletion (I.map (algebraMap R (MvPolynomial (Fin n) R))) (MvPolynomial (Fin n) R)

namespace RestrictedPowerSeries

/-- The identification of the restricted power series ring with the `I`-adic completion of the
polynomial ring, definitional with our choice of construction. -/
def equivAdicCompletion :
    RestrictedPowerSeries R I n ≃+*
      AdicCompletion (I.map (algebraMap R (MvPolynomial (Fin n) R)))
        (MvPolynomial (Fin n) R) :=
  RingEquiv.refl _

/-- The **ideal of definition** of the restricted power series ring: the extension of
`I·R[X]` to the completion. -/
abbrev idealOfDefinition : Ideal (RestrictedPowerSeries R I n) :=
  (I.map (algebraMap R (MvPolynomial (Fin n) R))).map
    (algebraMap (MvPolynomial (Fin n) R) (RestrictedPowerSeries R I n))

/-- The ideal of definition of `R{X₁, …, Xₙ}` is the extension of `I` itself. -/
theorem idealOfDefinition_eq_map :
    idealOfDefinition R I n = I.map (algebraMap R (RestrictedPowerSeries R I n)) := by
  change (I.map (algebraMap R (MvPolynomial (Fin n) R))).map
    (algebraMap (MvPolynomial (Fin n) R) (RestrictedPowerSeries R I n)) = _
  rw [Ideal.map_map]
  congr 1

/-- The restricted power series ring is an adic ring, with ideal of definition the extension
of `I`, provided `I` is finitely generated. -/
theorem isAdicRing (hI : I.FG) : IsAdicRing (idealOfDefinition R I n) :=
  AdicCompletion.isAdicRing_map _ (hI.map _)

/-- The **formal polydisc** `Spf R{X₁, …, Xₙ}` over `R`, as a formal scheme (`I` finitely
generated). -/
def formalPolydisc (hI : I.FG) : FormalScheme :=
  haveI := isAdicRing R I n hI
  FormalScheme.Spf (idealOfDefinition R I n)

/-!
### Evaluation: the universal property of the polydisc, existence half

Given a complete adic `R`-algebra `S` — complete for an ideal `L` containing `I·S` — and an
`n`-tuple `s` of elements of `S`, evaluation of polynomials extends to the restricted power
series: the assignment `Σ a_ν X^ν ↦ Σ a_ν s^ν` converges because the coefficients tend to
zero. Formally, the evaluation `aeval s` on polynomials is continuous for the `I·R[X]`-adic
and `L`-adic topologies, so it factors through the completion.
-/

section Eval

variable {S : Type u} [CommRing S] (L : Ideal S) [Algebra R S] [IsAdicComplete L S]
variable (hIL : I.map (algebraMap R S) ≤ L) (s : Fin n → S)

omit [IsAdicComplete L S] in
include hIL in
/-- The evaluation `aeval s` maps the powers of `I·R[X]` into the powers of `L`. -/
theorem aeval_pow_le (m : ℕ) :
    (I.map (algebraMap R (MvPolynomial (Fin n) R))) ^ m ≤
      (L ^ m).comap (MvPolynomial.aeval s).toRingHom := by
  rw [← Ideal.map_le_iff_le_comap, ← Ideal.map_pow, Ideal.map_map]
  have hcomp : ((MvPolynomial.aeval s).toRingHom.comp
      (algebraMap R (MvPolynomial (Fin n) R))) = algebraMap R S :=
    (MvPolynomial.aeval s).comp_algebraMap
  rw [hcomp, Ideal.map_pow]
  exact Ideal.pow_right_mono hIL m

/-- The level-`m` evaluation map `R{X} →+* S ⧸ L ^ m`. -/
def evalLevel (m : ℕ) : RestrictedPowerSeries R I n →+* S ⧸ L ^ m :=
  (Ideal.quotientMap (L ^ m) (MvPolynomial.aeval s).toRingHom
      (aeval_pow_le R I n L hIL s m)).comp
    (AdicCompletion.evalₐ (I.map (algebraMap R (MvPolynomial (Fin n) R))) m).toRingHom

omit [IsAdicComplete L S] in
theorem evalLevel_of (m : ℕ) (p : MvPolynomial (Fin n) R) :
    evalLevel R I n L hIL s m
        (AdicCompletion.of (I.map (algebraMap R (MvPolynomial (Fin n) R)))
          (MvPolynomial (Fin n) R) p) =
      Ideal.Quotient.mk (L ^ m) (MvPolynomial.aeval s p) := by
  simp only [evalLevel, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe]
  rw [AdicCompletion.evalₐ_of, Ideal.quotientMap_mk]
  rfl

omit [IsAdicComplete L S] in
theorem factorPow_comp_evalLevel {m m' : ℕ} (hle : m ≤ m') :
    (Ideal.Quotient.factorPow L hle).comp (evalLevel R I n L hIL s m') =
      evalLevel R I n L hIL s m := by
  refine RingHom.ext fun x => ?_
  simp only [RingHom.coe_comp, Function.comp_apply, evalLevel]
  -- both sides factor through `evalₐ` at levels `m'` and `m`, linked by `factorPow`
  have key : ∀ b : MvPolynomial (Fin n) R ⧸
      (I.map (algebraMap R (MvPolynomial (Fin n) R))) ^ m',
      Ideal.Quotient.factorPow L hle
        (Ideal.quotientMap (L ^ m') (MvPolynomial.aeval s).toRingHom
          (aeval_pow_le R I n L hIL s m') b) =
      Ideal.quotientMap (L ^ m) (MvPolynomial.aeval s).toRingHom
        (aeval_pow_le R I n L hIL s m)
        (Ideal.Quotient.factorPow (I.map (algebraMap R (MvPolynomial (Fin n) R))) hle b) := by
    intro b
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [Ideal.quotientMap_mk, Ideal.Quotient.factor_mk, Ideal.Quotient.factor_mk,
      Ideal.quotientMap_mk]
  rw [key]
  congr 1
  exact AdicCompletion.factorPow_evalₐ _ hle x

/-- **Evaluation of restricted power series** (the existence half of the universal property of
the formal polydisc, Bosch §7): for a complete adic `R`-algebra `S` — complete for an ideal
`L ⊇ I·S` — and elements `s₁, …, sₙ ∈ S`, evaluation of polynomials at `s` extends to a ring
homomorphism `R{X₁, …, Xₙ} →+* S`. -/
def evalHom : RestrictedPowerSeries R I n →+* S :=
  IsAdicComplete.liftRingHom L (fun m => evalLevel R I n L hIL s m)
    (fun hle => factorPow_comp_evalLevel R I n L hIL s hle)

theorem mk_evalHom (m : ℕ) (x : RestrictedPowerSeries R I n) :
    Ideal.Quotient.mk (L ^ m) (evalHom R I n L hIL s x) = evalLevel R I n L hIL s m x :=
  IsAdicComplete.mk_liftRingHom _ _ _ _ _

/-- On polynomials, `evalHom` is the usual evaluation `aeval s`. -/
theorem evalHom_of (p : MvPolynomial (Fin n) R) :
    evalHom R I n L hIL s
        (AdicCompletion.of (I.map (algebraMap R (MvPolynomial (Fin n) R)))
          (MvPolynomial (Fin n) R) p) =
      MvPolynomial.aeval s p := by
  have h : ∀ m : ℕ, Ideal.Quotient.mk (L ^ m)
      (evalHom R I n L hIL s (AdicCompletion.of _ _ p)) =
      Ideal.Quotient.mk (L ^ m) (MvPolynomial.aeval s p) := fun m => by
    rw [mk_evalHom, evalLevel_of]
  have hmem : ∀ (m : ℕ) (z : S), z ∈ (L ^ m • ⊤ : Submodule S S) ↔ z ∈ L ^ m := by
    intro m z
    rw [Ideal.smul_top_eq_map (L ^ m), Submodule.restrictScalars_mem, Algebra.algebraMap_self,
      Ideal.map_id]
  refine (IsHausdorff.eq_iff_smodEq (I := L)).mpr fun m => ?_
  rw [SModEq.sub_mem]
  exact (hmem m _).mpr (Ideal.Quotient.eq.mp (h m))

end Eval

end RestrictedPowerSeries
