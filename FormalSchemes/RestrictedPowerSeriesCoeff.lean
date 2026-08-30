import FormalSchemes.RestrictedPowerSeries

set_option linter.style.header false

/-!
# Coefficients of restricted power series

`RestrictedPowerSeries R I n = R{X₁, …, Xₙ}` is the `I`-adic completion of the polynomial ring
`R[X₁, …, Xₙ]` (`FormalSchemes.RestrictedPowerSeries`). Its API so far consists of the ideal of
definition, the adic-ring structure and evaluation at a tuple; **nothing reads a single
coefficient, and there is no extensionality principle in those terms.** This file supplies both,
for a base ring that is `I`-adically complete.

It is the several-variable analogue of `FormalSchemes.RestrictedLaurentCoeff`, which does the
same job for `R{X, X⁻¹}` in one variable, and it is written to be read against that file: every
declaration below has a counterpart there, except the three noted under *What is new here*.

## The construction

`MvPolynomial (Fin n) R` is `(Fin n →₀ ℕ) →₀ R`, so `MvPolynomial.lcoeff R d` — the coefficient
of the monomial `Xᵈ`, as an `R`-linear map — is already in Mathlib. It carries `K • ⊤` onto `K`
in both directions (`MvPolynomial.mem_smul_top_iff_lcoeff_mem`), so it descends to every level of
the filtration, and the descended maps are compatible with the transition maps.
`IsAdicComplete.lift` then assembles them into `RestrictedPowerSeries.coeff`.

The one wrinkle is that `RestrictedPowerSeries R I n` is the completion of `R[X₁, …, Xₙ]` at an
ideal **of `R[X₁, …, Xₙ]`**, whereas the coefficient is only `R`-linear. The bridge is
`Ideal.mem_map_pow_iff_mem_smul_top` (`FormalSchemes.RestrictedPowerSeries`): the two filtrations
`(I·R[X])^m • ⊤` over `R[X]` and `I^m • ⊤` over `R` have the same underlying set, and
`Submodule.Quotient.restrictScalarsEquiv` turns that into an `R`-linear identification of the two
quotients.

## Main results

* `MvPolynomial.mem_smul_top_iff_lcoeff_mem`: `p ∈ K • ⊤` exactly when every coefficient of `p`
  lies in `K`, for an arbitrary index type. Both directions are used — the forward one to descend
  the coefficient to the quotients, the backward one for extensionality.
* `RestrictedPowerSeries.coeff`: **the `d`-th coefficient of a restricted power series**, an
  `R`-linear map `R{X₁, …, Xₙ} →ₗ[R] R`, for `[IsAdicComplete I R]`.
* `RestrictedPowerSeries.coeff_of`, `RestrictedPowerSeries.coeff_monomial`,
  `RestrictedPowerSeries.coeff_X`, `RestrictedPowerSeries.coeff_algebraMap`,
  `RestrictedPowerSeries.coeff_one` and `RestrictedPowerSeries.coeff_algebraMap_mul`: its values
  on the image of a polynomial, on a monomial, on a variable and on the structural image of a
  scalar, and the fact that scalars pull out.
* `RestrictedPowerSeries.coeff_mem_pow`: `RestrictedPowerSeries.coeff` is continuous — a
  coefficient of an element of the `m`-th step of the filtration lies in `I ^ m`.
* **`RestrictedPowerSeries.ext_coeff`**: a restricted power series is determined by its
  coefficients, with `RestrictedPowerSeries.coeff_eq_zero_iff` and
  `RestrictedPowerSeries.eq_zero_of_coeff_eq_zero`.

## What is new here, relative to the one-variable file

Three declarations have no counterpart in `FormalSchemes.RestrictedLaurentCoeff`.

* `RestrictedPowerSeries.mem_pow_smul_top_iff_coeff_mem`: the **converse** of continuity —
  membership in the `m`-th step of the filtration is exactly the statement that every coefficient
  lies in `I ^ m`. The one-variable file proves only the forward direction.
* `RestrictedPowerSeries.eq_of_eq_on_polynomials`: **two continuous `R`-linear functionals that
  agree on polynomials are equal.** `FormalSchemes.RestrictedLaurentCoeffInv`'s `coeff_rlsInv`
  runs this argument inline; here it is a lemma, so a successor does not repeat it.
* `RestrictedPowerSeries.coeff_monomial_mul`: **multiplication by a monomial shifts the
  coefficients**, `coeff d (Xᵉ·c · z) = c · coeff (d − e) z` when `e ≤ d` and `0` otherwise. This
  is the rule an induction along `MvPolynomial.induction_on` needs and
  `FormalSchemes.RestrictedLaurentCoeff` does not have.

## What is *not* proved

**No multiplicativity beyond a monomial factor.** `RestrictedPowerSeries.coeff` is `R`-linear,
and `RestrictedPowerSeries.coeff_monomial_mul` handles a monomial on the left; the convolution
formula for the coefficients of a general product is **not** proved.

**Nothing about the Tate annulus.** The intended consumer is
`A = R{x, y}/(x·y − q)` of `FormalSchemes.TateAnnulus` and the separation property
`AlgebraicGeometry.IsTateInvCoordSeparating` of `FormalSchemes.TateInvGlobalNormalForm`, which
needs in addition a division of `R{x, y}` by `x·y − q`. **That division is not attempted here and
no statement below mentions `x·y − q`.** In particular this file does not discharge
`IsTateInvCoordSeparating` for any base with `I ≠ ⊥`.

**Nothing about the description by null coefficient sequences.** That `R{X₁, …, Xₙ}` *is* the ring
of power series whose coefficients tend to `0` — i.e. that
`z ↦ (RestrictedPowerSeries.coeff I n · z)` is injective onto such families — is only half proved:
injectivity is `RestrictedPowerSeries.ext_coeff`, and surjectivity is not attempted.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. 0, §7.5.
* [The Stacks Project, Tag 0AKA](https://stacks.math.columbia.edu/tag/0AKA)
-/

noncomputable section

open Ideal Submodule

universe u v

namespace MvPolynomial

variable {R : Type u} [CommRing R] {σ : Type v}

/-- Every coefficient of an element of `K • ⊤` lies in `K`. The submodule is generated by the
`r • p` with `r ∈ K`, and `MvPolynomial.lcoeff` is `R`-linear, so this is
`Submodule.smul_induction_on`. -/
theorem lcoeff_mem_of_mem_smul_top {K : Ideal R} {p : MvPolynomial σ R}
    (hp : p ∈ (K • ⊤ : Submodule R (MvPolynomial σ R))) (d : σ →₀ ℕ) :
    lcoeff R d p ∈ K := by
  refine Submodule.smul_induction_on hp ?_ ?_
  · intro r hr x _
    have hsmul : lcoeff R d (r • x) = r * lcoeff R d x := by rw [map_smul]; rfl
    rw [hsmul]
    exact K.mul_mem_right _ hr
  · intro x y hx hy
    rw [map_add]
    exact K.add_mem hx hy

/-- Conversely, a polynomial all of whose coefficients lie in `K` lies in `K • ⊤`: it is the
finite sum of its monomials, and `monomial d c` is `c • monomial d 1`. -/
theorem mem_smul_top_of_lcoeff_mem {K : Ideal R} {p : MvPolynomial σ R}
    (h : ∀ d, lcoeff R d p ∈ K) : p ∈ (K • ⊤ : Submodule R (MvPolynomial σ R)) := by
  have hsum : (∑ v ∈ p.support, (monomial v) (coeff v p)) ∈
      (K • ⊤ : Submodule R (MvPolynomial σ R)) := by
    refine Submodule.sum_mem _ fun v _ => ?_
    have hv : (monomial v) (coeff v p) = coeff v p • (monomial v (1 : R)) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [hv]
    exact Submodule.smul_mem_smul (h v) Submodule.mem_top
  rwa [support_sum_monomial_coeff] at hsum

/-- **`K • ⊤` is cut out coefficientwise.** -/
theorem mem_smul_top_iff_lcoeff_mem {K : Ideal R} {p : MvPolynomial σ R} :
    p ∈ (K • ⊤ : Submodule R (MvPolynomial σ R)) ↔ ∀ d, lcoeff R d p ∈ K :=
  ⟨fun hp => lcoeff_mem_of_mem_smul_top hp, mem_smul_top_of_lcoeff_mem⟩

end MvPolynomial

namespace RestrictedPowerSeries

variable {R : Type u} [CommRing R] (I : Ideal R) (n : ℕ)

/-! ### The coefficient at a single level of the filtration -/

/-- The `d`-th coefficient kills the `m`-th step of the filtration, modulo `I ^ m`. The two
filtrations agree by `Ideal.mem_map_pow_iff_mem_smul_top`. -/
theorem le_ker_lcoeff (d : Fin n →₀ ℕ) (m : ℕ) :
    Submodule.restrictScalars R
        (((I.map (algebraMap R (MvPolynomial (Fin n) R))) ^ m • ⊤ :
          Submodule (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R))) ≤
      LinearMap.ker ((I ^ m • ⊤ : Submodule R R).mkQ ∘ₗ MvPolynomial.lcoeff R d) := by
  intro p hp
  rw [Submodule.restrictScalars_mem, Ideal.mem_map_pow_iff_mem_smul_top] at hp
  simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  rw [Ideal.mem_smul_top_self_iff]
  exact MvPolynomial.lcoeff_mem_of_mem_smul_top hp d

/-- The `d`-th coefficient at the `m`-th level of the filtration, as a map of quotients. -/
def coeffQuot (d : Fin n →₀ ℕ) (m : ℕ) :
    MvPolynomial (Fin n) R ⧸ ((I.map (algebraMap R (MvPolynomial (Fin n) R))) ^ m • ⊤ :
        Submodule (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R)) →ₗ[R]
      R ⧸ (I ^ m • ⊤ : Submodule R R) :=
  Submodule.liftQ _ ((I ^ m • ⊤ : Submodule R R).mkQ ∘ₗ MvPolynomial.lcoeff R d)
    (le_ker_lcoeff I n d m) ∘ₗ (Submodule.Quotient.restrictScalarsEquiv R _).symm.toLinearMap

@[simp]
theorem coeffQuot_mk (d : Fin n →₀ ℕ) (m : ℕ) (p : MvPolynomial (Fin n) R) :
    coeffQuot I n d m (Submodule.Quotient.mk p) =
      Submodule.Quotient.mk (MvPolynomial.lcoeff R d p) := rfl

/-- The level maps commute with the transition maps of the two filtrations. -/
theorem coeffQuot_transitionMap (d : Fin n →₀ ℕ) {m k : ℕ} (hle : m ≤ k)
    (w : MvPolynomial (Fin n) R ⧸ ((I.map (algebraMap R (MvPolynomial (Fin n) R))) ^ k • ⊤ :
      Submodule (MvPolynomial (Fin n) R) (MvPolynomial (Fin n) R))) :
    coeffQuot I n d m (AdicCompletion.transitionMap _ _ hle w) =
      Submodule.factorPow I R hle (coeffQuot I n d k w) := by
  obtain ⟨p, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rfl

/-- The `d`-th coefficient of a restricted power series, read modulo `I ^ m`. -/
def coeffLevel (d : Fin n →₀ ℕ) (m : ℕ) :
    RestrictedPowerSeries R I n →ₗ[R] R ⧸ (I ^ m • ⊤ : Submodule R R) :=
  coeffQuot I n d m ∘ₗ
    (AdicCompletion.eval (I.map (algebraMap R (MvPolynomial (Fin n) R)))
      (MvPolynomial (Fin n) R) m).restrictScalars R

@[simp]
theorem coeffLevel_apply (d : Fin n →₀ ℕ) (m : ℕ) (z : RestrictedPowerSeries R I n) :
    coeffLevel I n d m z = coeffQuot I n d m (z.val m) := rfl

/-- The levels of the `d`-th coefficient form a compatible family, so they can be lifted. -/
theorem coeffLevel_compat (d : Fin n →₀ ℕ) {m k : ℕ} (hle : m ≤ k) :
    Submodule.factorPow I R hle ∘ₗ coeffLevel I n d k = coeffLevel I n d m :=
  LinearMap.ext fun z => by
    rw [LinearMap.comp_apply, coeffLevel_apply, coeffLevel_apply, ← z.property hle,
      coeffQuot_transitionMap]

/-! ### Density of the polynomials, and multiplication by a polynomial -/

/-- **The image of `R[X₁, …, Xₙ]` is dense**: every restricted power series agrees with a
polynomial modulo the `m`-th step of the filtration. This is `AdicCompletion.eval` being
surjective, read through `AdicCompletion.pow_smul_top_eq_ker_eval`. -/
theorem exists_sub_mem_smul_top (hI : I.FG) (m : ℕ) (z : RestrictedPowerSeries R I n) :
    ∃ p : MvPolynomial (Fin n) R,
      z - AdicCompletion.of (I.map (algebraMap R (MvPolynomial (Fin n) R)))
          (MvPolynomial (Fin n) R) p ∈
        ((I.map (algebraMap R (MvPolynomial (Fin n) R))) ^ m • ⊤ :
          Submodule (MvPolynomial (Fin n) R) (RestrictedPowerSeries R I n)) := by
  obtain ⟨p, hp⟩ := Submodule.Quotient.mk_surjective _ (z.val m)
  refine ⟨p, ?_⟩
  rw [AdicCompletion.pow_smul_top_eq_ker_eval (hI.map _), LinearMap.mem_ker, map_sub,
    AdicCompletion.eval_apply, AdicCompletion.eval_of, Submodule.mkQ_apply, ← hp, sub_self]

/-- Multiplying by the image of a polynomial is the `R[X₁, …, Xₙ]`-action. This is what makes the
`m`-th step of the filtration — an `R[X₁, …, Xₙ]`-submodule — stable under multiplication by the
image of a polynomial. -/
theorem of_mul_eq_smul (p : MvPolynomial (Fin n) R) (z : RestrictedPowerSeries R I n) :
    AdicCompletion.of (I.map (algebraMap R (MvPolynomial (Fin n) R)))
      (MvPolynomial (Fin n) R) p * z = p • z := by
  rw [Algebra.smul_def]; rfl

/-- `AdicCompletion.of` is multiplicative. It is stated as a `LinearMap`, so `map_mul` does not
apply to it directly; this is that statement. -/
theorem of_mul_of (a b : MvPolynomial (Fin n) R) :
    AdicCompletion.of (I.map (algebraMap R (MvPolynomial (Fin n) R)))
        (MvPolynomial (Fin n) R) a *
      AdicCompletion.of (I.map (algebraMap R (MvPolynomial (Fin n) R)))
        (MvPolynomial (Fin n) R) b =
      AdicCompletion.of (I.map (algebraMap R (MvPolynomial (Fin n) R)))
        (MvPolynomial (Fin n) R) (a * b) := by
  rw [of_mul_eq_smul, ← map_smul, smul_eq_mul]

/-! ### The coefficient itself -/

section Complete

variable [IsAdicComplete I R]

/-- **The `d`-th coefficient of a restricted power series**, an `R`-linear map
`R{X₁, …, Xₙ} →ₗ[R] R`, for a base ring that is `I`-adically complete. It is the lift of the
compatible family `RestrictedPowerSeries.coeffLevel` along the universal property of
`IsAdicComplete`. -/
def coeff (d : Fin n →₀ ℕ) : RestrictedPowerSeries R I n →ₗ[R] R :=
  IsAdicComplete.lift I (coeffLevel I n d) fun hle => coeffLevel_compat I n d hle

@[simp]
theorem mk_coeff (d : Fin n →₀ ℕ) (m : ℕ) (z : RestrictedPowerSeries R I n) :
    (Submodule.Quotient.mk (coeff I n d z) : R ⧸ (I ^ m • ⊤ : Submodule R R)) =
      coeffLevel I n d m z :=
  IsAdicComplete.mk_lift I (fun hle => coeffLevel_compat I n d hle) m z

/-- **The coefficient of the image of a polynomial is its coefficient.** -/
@[simp]
theorem coeff_of (d : Fin n →₀ ℕ) (p : MvPolynomial (Fin n) R) :
    coeff I n d (AdicCompletion.of (I.map (algebraMap R (MvPolynomial (Fin n) R)))
      (MvPolynomial (Fin n) R) p) = MvPolynomial.coeff d p := by
  rw [IsHausdorff.eq_iff_smodEq (I := I)]
  intro m
  rw [SModEq.def, mk_coeff, coeffLevel_apply, AdicCompletion.of_apply, Submodule.mkQ_apply,
    coeffQuot_mk, MvPolynomial.lcoeff_apply]

/-- **The coefficients of a monomial.** -/
@[simp]
theorem coeff_monomial (d e : Fin n →₀ ℕ) (c : R) :
    coeff I n d (AdicCompletion.of (I.map (algebraMap R (MvPolynomial (Fin n) R)))
      (MvPolynomial (Fin n) R) (MvPolynomial.monomial e c)) = if e = d then c else 0 := by
  rw [coeff_of, MvPolynomial.coeff_monomial]

/-- **The coefficients of a variable.** -/
@[simp]
theorem coeff_X (d : Fin n →₀ ℕ) (i : Fin n) :
    coeff I n d (AdicCompletion.of (I.map (algebraMap R (MvPolynomial (Fin n) R)))
      (MvPolynomial (Fin n) R) (MvPolynomial.X i)) =
      if Finsupp.single i 1 = d then 1 else 0 := by
  rw [coeff_of, MvPolynomial.coeff_X]

/-- **The coefficients of a constant.** -/
@[simp]
theorem coeff_algebraMap (d : Fin n →₀ ℕ) (r : R) :
    coeff I n d (algebraMap R (RestrictedPowerSeries R I n) r) = if 0 = d then r else 0 := by
  have hr : algebraMap R (RestrictedPowerSeries R I n) r =
      AdicCompletion.of (I.map (algebraMap R (MvPolynomial (Fin n) R)))
        (MvPolynomial (Fin n) R) (MvPolynomial.C r) := by
    rw [IsScalarTower.algebraMap_apply R (MvPolynomial (Fin n) R) (RestrictedPowerSeries R I n),
      AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
      ← MvPolynomial.algebraMap_eq]
  rw [hr, coeff_of, MvPolynomial.coeff_C]

/-- **The coefficients of `1`.** -/
@[simp]
theorem coeff_one (d : Fin n →₀ ℕ) :
    coeff I n d (1 : RestrictedPowerSeries R I n) = if 0 = d then 1 else 0 := by
  rw [← map_one (algebraMap R (RestrictedPowerSeries R I n)), coeff_algebraMap]

/-- **Scalars pull out of a coefficient.** Multiplication by the structural image of `r` is the
`R`-action, and `RestrictedPowerSeries.coeff` is `R`-linear. -/
theorem coeff_algebraMap_mul (d : Fin n →₀ ℕ) (r : R) (z : RestrictedPowerSeries R I n) :
    coeff I n d (algebraMap R (RestrictedPowerSeries R I n) r * z) = r * coeff I n d z := by
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

/-- **A coefficient of an element of the `m`-th filtration step lies in `I ^ m`** — the statement
that `RestrictedPowerSeries.coeff` is continuous. -/
theorem coeff_mem_pow (hI : I.FG) (d : Fin n →₀ ℕ) (m : ℕ)
    {z : RestrictedPowerSeries R I n}
    (hz : z ∈ ((I.map (algebraMap R (MvPolynomial (Fin n) R))) ^ m • ⊤ :
      Submodule (MvPolynomial (Fin n) R) (RestrictedPowerSeries R I n))) :
    coeff I n d z ∈ I ^ m := by
  rw [AdicCompletion.pow_smul_top_eq_ker_eval (hI.map _), LinearMap.mem_ker,
    AdicCompletion.eval_apply] at hz
  have h0 : (Submodule.Quotient.mk (coeff I n d z) : R ⧸ (I ^ m • ⊤ : Submodule R R)) = 0 := by
    rw [mk_coeff, coeffLevel_apply, hz, map_zero]
  rw [Submodule.Quotient.mk_eq_zero, Ideal.mem_smul_top_self_iff] at h0
  exact h0

/-- **The converse of continuity: the filtration is cut out coefficientwise.** An element lies in
the `m`-th step exactly when every one of its coefficients lies in `I ^ m`. The one-variable file
`FormalSchemes.RestrictedLaurentCoeff` proves only the forward direction. -/
theorem mem_pow_smul_top_iff_coeff_mem (hI : I.FG) (m : ℕ) (z : RestrictedPowerSeries R I n) :
    z ∈ ((I.map (algebraMap R (MvPolynomial (Fin n) R))) ^ m • ⊤ :
      Submodule (MvPolynomial (Fin n) R) (RestrictedPowerSeries R I n)) ↔
      ∀ d, coeff I n d z ∈ I ^ m := by
  refine ⟨fun hz d => coeff_mem_pow I n hI d m hz, fun h => ?_⟩
  rw [AdicCompletion.pow_smul_top_eq_ker_eval (hI.map _), LinearMap.mem_ker,
    AdicCompletion.eval_apply]
  obtain ⟨p, hp⟩ := Submodule.Quotient.mk_surjective _ (z.val m)
  have hcoeff : ∀ d, MvPolynomial.lcoeff R d p ∈ I ^ m := by
    intro d
    have h0 : (Submodule.Quotient.mk (MvPolynomial.lcoeff R d p) :
        R ⧸ (I ^ m • ⊤ : Submodule R R)) = Submodule.Quotient.mk (coeff I n d z) := by
      rw [mk_coeff, coeffLevel_apply, ← hp, coeffQuot_mk]
    have h2 := (Submodule.Quotient.eq _).1 h0
    rw [Ideal.mem_smul_top_self_iff] at h2
    have h3 := (I ^ m).add_mem h2 (h d)
    rwa [sub_add_cancel] at h3
  rw [← hp, Submodule.Quotient.mk_eq_zero, Ideal.mem_map_pow_iff_mem_smul_top I m p]
  exact MvPolynomial.mem_smul_top_of_lcoeff_mem hcoeff

/-! ### Density, and multiplication by a monomial -/

/-- **Two continuous `R`-linear functionals that agree on polynomials are equal.** Split `z` as a
polynomial plus an element of the `m`-th filtration step; the two functionals agree on the first
summand and each sends the second into `I ^ m`, so their difference lies in every `I ^ m` and `R`
is Hausdorff.

`FormalSchemes.RestrictedLaurentCoeffInv`'s `RestrictedLaurentSeries.coeff_rlsInv` runs exactly
this argument inline in the one-variable case. -/
theorem eq_of_eq_on_polynomials (hI : I.FG) {φ ψ : RestrictedPowerSeries R I n →ₗ[R] R}
    (hφ : ∀ (m : ℕ) {w : RestrictedPowerSeries R I n},
      w ∈ ((I.map (algebraMap R (MvPolynomial (Fin n) R))) ^ m • ⊤ :
        Submodule (MvPolynomial (Fin n) R) (RestrictedPowerSeries R I n)) → φ w ∈ I ^ m)
    (hψ : ∀ (m : ℕ) {w : RestrictedPowerSeries R I n},
      w ∈ ((I.map (algebraMap R (MvPolynomial (Fin n) R))) ^ m • ⊤ :
        Submodule (MvPolynomial (Fin n) R) (RestrictedPowerSeries R I n)) → ψ w ∈ I ^ m)
    (h : ∀ p : MvPolynomial (Fin n) R,
      φ (AdicCompletion.of (I.map (algebraMap R (MvPolynomial (Fin n) R)))
          (MvPolynomial (Fin n) R) p) =
        ψ (AdicCompletion.of (I.map (algebraMap R (MvPolynomial (Fin n) R)))
          (MvPolynomial (Fin n) R) p))
    (z : RestrictedPowerSeries R I n) : φ z = ψ z := by
  rw [← sub_eq_zero]
  refine (inferInstance : IsHausdorff I R).haus _ fun m => ?_
  rw [SModEq.zero, Ideal.mem_smul_top_self_iff]
  obtain ⟨p, hp⟩ := exists_sub_mem_smul_top I n hI m z
  have hz : z = (z - AdicCompletion.of (I.map (algebraMap R (MvPolynomial (Fin n) R)))
      (MvPolynomial (Fin n) R) p) +
      AdicCompletion.of (I.map (algebraMap R (MvPolynomial (Fin n) R)))
        (MvPolynomial (Fin n) R) p := by ring
  rw [hz, map_add, map_add, h p, add_sub_add_right_eq_sub]
  exact Ideal.sub_mem _ (hφ m hp) (hψ m hp)

/-- **Multiplication by a monomial shifts the coefficients.** Both sides are continuous `R`-linear
functionals of `z`, and on polynomials the identity is `MvPolynomial.coeff_monomial_mul'`, so
`RestrictedPowerSeries.eq_of_eq_on_polynomials` applies. -/
theorem coeff_monomial_mul (hI : I.FG) (d e : Fin n →₀ ℕ) (c : R)
    (z : RestrictedPowerSeries R I n) :
    coeff I n d (AdicCompletion.of (I.map (algebraMap R (MvPolynomial (Fin n) R)))
        (MvPolynomial (Fin n) R) (MvPolynomial.monomial e c) * z) =
      if e ≤ d then c * coeff I n (d - e) z else 0 := by
  classical
  let φ : RestrictedPowerSeries R I n →ₗ[R] R :=
    { toFun := fun u => coeff I n d (AdicCompletion.of
        (I.map (algebraMap R (MvPolynomial (Fin n) R))) (MvPolynomial (Fin n) R)
        (MvPolynomial.monomial e c) * u)
      map_add' := fun u v => by rw [mul_add, map_add]
      map_smul' := fun r u => by rw [mul_smul_comm, map_smul, RingHom.id_apply] }
  have hφ : ∀ (m : ℕ) {w : RestrictedPowerSeries R I n},
      w ∈ ((I.map (algebraMap R (MvPolynomial (Fin n) R))) ^ m • ⊤ :
        Submodule (MvPolynomial (Fin n) R) (RestrictedPowerSeries R I n)) → φ w ∈ I ^ m := by
    intro m w hw
    change coeff I n d (AdicCompletion.of (I.map (algebraMap R (MvPolynomial (Fin n) R)))
      (MvPolynomial (Fin n) R) (MvPolynomial.monomial e c) * w) ∈ I ^ m
    rw [of_mul_eq_smul]
    exact coeff_mem_pow I n hI d m (Submodule.smul_mem _ _ hw)
  by_cases hle : e ≤ d
  · rw [if_pos hle]
    refine eq_of_eq_on_polynomials I n hI (φ := φ) (ψ := c • coeff I n (d - e)) hφ ?_ ?_ z
    · intro m w hw
      change c * coeff I n (d - e) w ∈ I ^ m
      exact Ideal.mul_mem_left _ _ (coeff_mem_pow I n hI (d - e) m hw)
    · intro p
      change coeff I n d (AdicCompletion.of (I.map (algebraMap R (MvPolynomial (Fin n) R)))
        (MvPolynomial (Fin n) R) (MvPolynomial.monomial e c) *
        AdicCompletion.of (I.map (algebraMap R (MvPolynomial (Fin n) R)))
          (MvPolynomial (Fin n) R) p) =
        c * coeff I n (d - e) (AdicCompletion.of
          (I.map (algebraMap R (MvPolynomial (Fin n) R))) (MvPolynomial (Fin n) R) p)
      rw [of_mul_of, coeff_of, MvPolynomial.coeff_monomial_mul', if_pos hle, coeff_of]
  · rw [if_neg hle]
    refine eq_of_eq_on_polynomials I n hI (φ := φ) (ψ := 0) hφ ?_ ?_ z
    · intro m w _
      exact (I ^ m).zero_mem
    · intro p
      change coeff I n d (AdicCompletion.of (I.map (algebraMap R (MvPolynomial (Fin n) R)))
        (MvPolynomial (Fin n) R) (MvPolynomial.monomial e c) *
        AdicCompletion.of (I.map (algebraMap R (MvPolynomial (Fin n) R)))
          (MvPolynomial (Fin n) R) p) = 0
      rw [of_mul_of, coeff_of, MvPolynomial.coeff_monomial_mul', if_neg hle]

/-! ### Extensionality -/

/-- **A restricted power series with all coefficients zero is zero.** At each level its
representative has every coefficient in `I ^ m`, hence lies in the `m`-th step of the filtration
by `MvPolynomial.mem_smul_top_of_lcoeff_mem`. -/
theorem eq_zero_of_coeff_eq_zero {z : RestrictedPowerSeries R I n}
    (h : ∀ d, coeff I n d z = 0) : z = 0 := by
  refine AdicCompletion.ext fun m => ?_
  obtain ⟨p, hp⟩ := Submodule.Quotient.mk_surjective _ (z.val m)
  have hcoeff : ∀ d, MvPolynomial.lcoeff R d p ∈ I ^ m := by
    intro d
    have h0 : (Submodule.Quotient.mk (coeff I n d z) : R ⧸ (I ^ m • ⊤ : Submodule R R)) =
        Submodule.Quotient.mk (MvPolynomial.lcoeff R d p) := by
      rw [mk_coeff, coeffLevel_apply, ← hp, coeffQuot_mk]
    rw [h d] at h0
    have hmem := (Submodule.Quotient.eq _).1 h0
    rw [zero_sub, Submodule.neg_mem_iff, Ideal.mem_smul_top_self_iff] at hmem
    exact hmem
  rw [← hp, AdicCompletion.val_zero_apply, Submodule.Quotient.mk_eq_zero,
    Ideal.mem_map_pow_iff_mem_smul_top I m p]
  exact MvPolynomial.mem_smul_top_of_lcoeff_mem hcoeff

/-- **A restricted power series is zero exactly when all its coefficients are.** -/
theorem coeff_eq_zero_iff {z : RestrictedPowerSeries R I n} :
    (∀ d, coeff I n d z = 0) ↔ z = 0 :=
  ⟨eq_zero_of_coeff_eq_zero I n, fun hz d => by rw [hz, map_zero]⟩

/-- **Extensionality: a restricted power series is determined by its coefficients.** -/
theorem ext_coeff {z w : RestrictedPowerSeries R I n}
    (h : ∀ d, coeff I n d z = coeff I n d w) : z = w := by
  rw [← sub_eq_zero]
  refine eq_zero_of_coeff_eq_zero I n fun d => ?_
  rw [map_sub, h d, sub_self]

end Complete

end RestrictedPowerSeries
