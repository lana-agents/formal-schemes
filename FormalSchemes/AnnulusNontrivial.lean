import FormalSchemes.TateAnnulus

set_option linter.style.header false

/-!
# Nontriviality of the Tate annulus and nonemptiness of its formal spectrum

Fix an adic base `(R, I)` and a Tate parameter `q ∈ I`. The Tate annulus
`A = R{x, y} / (x·y − q)` (`FormalSchemes.TateAnnulus`) has a natural **augmentation**
`A → R ⧸ I` sending both coordinates `x, y` to `0` — this is well-defined precisely because
`q ≡ 0 (mod I)`, so the relation `x·y − q` maps to `0 · 0 − 0 = 0` in the special fibre. This
augmentation is the evaluation of restricted power series at the origin of `Spec (R ⧸ I)`
(`RestrictedPowerSeries.evalHom` at `s = 0`, over the discrete target `R ⧸ I`).

The augmentation is a section of the structural map on the special fibre, hence surjective; in
particular, when `I ≠ ⊤` (so `R ⧸ I` is nontrivial) it forces the ideal of definition `I·A` of
the annulus to be a proper ideal, so the special fibre `A ⧸ (I·A)` is a nontrivial ring and the
formal spectrum `Spf A = Spec (A ⧸ I·A)` is **nonempty**.

This is the ring-theoretic input the Tate-chain freeness argument needs: a properly discontinuous
action on a chain of *nonempty* patches has no nontrivial period of absolute value `≥ 2`, since a
patch is disjoint from its far translates (`FormalSchemes.TateAction`,
`tateShift_properlyDiscontinuous`), yet an equal (identified) translate would force the patch to be
empty — the freeness assembly for issue 135 consumes `annulus_formalSpectrum_nonempty` for exactly
that contradiction.

## Main results

* `annulusAug`: the augmentation `R{x, y} →+* R ⧸ I`, `x, y ↦ 0`.
* `annulusAugAlg`: its descent `A →+* R ⧸ I` to the annulus (killing `x·y − q`).
* `annulusIdealOfDefinition_ne_top`: for `I ≠ ⊤`, the ideal of definition `I·A` is proper.
* `annulus_nontrivial`: for `I ≠ ⊤`, the special fibre `A ⧸ (I·A)` is a nontrivial ring.
* `annulus_formalSpectrum_nonempty`: for `I ≠ ⊤`, `Spf A` has nonempty underlying space.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.
-/

noncomputable section

open Ideal AlgebraicGeometry RestrictedPowerSeries

universe u

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- The **augmentation** `R{x, y} →+* R ⧸ I` of the polydisc: evaluation of restricted power
series at the origin `x = y = 0` of the special fibre `Spec (R ⧸ I)`. It sends `Σ aᵥ Xᵛ` to the
residue of its constant term. -/
def annulusAug : annulusRing R I →+* R ⧸ I :=
  RestrictedPowerSeries.evalHom R I 2 (⊥ : Ideal (R ⧸ I))
    (by rw [Ideal.Quotient.algebraMap_eq]; exact (Ideal.map_quotient_self I).le)
    (0 : Fin 2 → R ⧸ I)

@[simp]
theorem annulusAug_of (p : MvPolynomial (Fin 2) R) :
    annulusAug R I (AdicCompletion.of _ _ p) =
      MvPolynomial.aeval (0 : Fin 2 → R ⧸ I) p :=
  RestrictedPowerSeries.evalHom_of R I 2 _ _ _ p

@[simp]
theorem annulusAug_annulusX : annulusAug R I (annulusX R I) = 0 := by
  rw [annulusX, annulusAug_of, MvPolynomial.aeval_X, Pi.zero_apply]

@[simp]
theorem annulusAug_annulusY : annulusAug R I (annulusY R I) = 0 := by
  rw [annulusY, annulusAug_of, MvPolynomial.aeval_X, Pi.zero_apply]

theorem annulusAug_algebraMap (r : R) :
    annulusAug R I (algebraMap R (annulusRing R I) r) = algebraMap R (R ⧸ I) r := by
  rw [AdicCompletion.algebraMap_apply, annulusAug_of]
  exact (MvPolynomial.aeval (0 : Fin 2 → R ⧸ I)).commutes r

/-- The augmentation kills the Tate relation `x·y − q`, since `q ∈ I` forces its residue to
vanish: `0 · 0 − q̄ = 0` in `R ⧸ I`. -/
theorem annulusAug_annulusRel (hq : q ∈ I) : annulusAug R I (annulusRel R I q) = 0 := by
  rw [annulusRel, map_sub, map_mul, annulusAug_annulusX, annulusAug_annulusY, mul_zero,
    annulusAug_algebraMap, zero_sub, neg_eq_zero, Ideal.Quotient.algebraMap_eq,
    Ideal.Quotient.eq_zero_iff_mem]
  exact hq

/-- The augmentation descends to the annulus `A = R{x, y} / (x·y − q)`, giving a ring
homomorphism `A →+* R ⧸ I`. -/
def annulusAugAlg (hq : q ∈ I) : annulusAlgebra R I q →+* R ⧸ I :=
  Ideal.Quotient.lift (annulusIdeal R I q) (annulusAug R I) <| by
    intro a ha
    rw [annulusIdeal, Ideal.mem_span_singleton] at ha
    obtain ⟨b, rfl⟩ := ha
    rw [map_mul, annulusAug_annulusRel R I q hq, zero_mul]

@[simp]
theorem annulusAugAlg_mk (hq : q ∈ I) (p : annulusRing R I) :
    annulusAugAlg R I q hq (annulusMk R I q p) = annulusAug R I p :=
  rfl

theorem annulusAugAlg_algebraMap (hq : q ∈ I) (r : R) :
    annulusAugAlg R I q hq (algebraMap R (annulusAlgebra R I q) r) = algebraMap R (R ⧸ I) r := by
  rw [← AlgHom.commutes (annulusMk R I q) r, annulusAugAlg_mk, annulusAug_algebraMap]

/-- **The ideal of definition of the Tate annulus is proper** when `I ≠ ⊤`. Indeed the
augmentation `A →+* R ⧸ I` sends every element of `I·A` to `0` (it is an `R`-algebra map killing
`I`), so if `1 ∈ I·A` then `1 = 0` in the nontrivial ring `R ⧸ I` — a contradiction. -/
theorem annulusIdealOfDefinition_ne_top (hq : q ∈ I) (hI : I ≠ ⊤) :
    annulusIdealOfDefinition R I q ≠ ⊤ := by
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  -- the augmentation kills `I·A = I.map (algebraMap R A)`
  have hker : I.map (algebraMap R (annulusAlgebra R I q)) ≤
      RingHom.ker (annulusAugAlg R I q hq) := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    simp only [Ideal.mem_comap, RingHom.mem_ker, annulusAugAlg_algebraMap,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact hr
  rw [← annulus_map_eq]
  intro htop
  have h1 : (1 : annulusAlgebra R I q) ∈ I.map (algebraMap R (annulusAlgebra R I q)) :=
    htop ▸ Submodule.mem_top
  have : annulusAugAlg R I q hq 1 = 0 := hker h1
  rw [map_one] at this
  exact one_ne_zero this

/-- **The special fibre of the Tate annulus is nontrivial** when `I ≠ ⊤`: the ring
`A ⧸ (I·A) = (R ⧸ I){x, y}/(xy)` is not the zero ring. -/
theorem annulus_nontrivial (hq : q ∈ I) (hI : I ≠ ⊤) :
    Nontrivial (annulusAlgebra R I q ⧸ annulusIdealOfDefinition R I q) :=
  Ideal.Quotient.nontrivial_iff.mpr (annulusIdealOfDefinition_ne_top R I q hq hI)

/-- **The formal spectrum of the Tate annulus is nonempty** when `I ≠ ⊤`: `Spf A` has at least
one open prime, being `Spec` of the nontrivial special fibre `A ⧸ (I·A)`. -/
theorem annulus_formalSpectrum_nonempty (hq : q ∈ I) (hI : I ≠ ⊤) :
    Nonempty (FormalSpectrum (annulusIdealOfDefinition R I q)) := by
  haveI := annulus_nontrivial R I q hq hI
  exact PrimeSpectrum.nonempty_iff_nontrivial.mpr inferInstance

end
