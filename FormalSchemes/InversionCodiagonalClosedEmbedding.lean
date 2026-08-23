import FormalSchemes.AwayCompletionSurjective
import FormalSchemes.DiagonalClosedEmbedding
import FormalSchemes.TateOverlapInversion

set_option linter.style.header false

/-!
# The inversion localized codiagonal `A ⊗̂_R A → A{1/x}` and its closed-embedding formal spectrum

Fix an adic ring `(R, I)` (with `I` finitely generated) and a Tate parameter `q ∈ R`, and let
`A = R{x, y}/(x·y − q)` be the coordinate ring of the formal Tate annulus (`annulusAlgebra`). Its
`x`-overlap chart `A{1/x} = annulusOverlap` is a copy of the formal multiplicative group
`Ĝm = R{X, X⁻¹}` via the crux identification `overlapEquiv` (`x ↦ X`).

The **inversion localized codiagonal** is the lift of the two `R`-algebra maps

```
locX     : A →ₐ[R] A{1/x}          (the away-localization/completion map, `x ↦ x`)
invLocX  : A →ₐ[R] A{1/x}          (`invAutX ∘ locX`, `x ↦ x⁻¹`)
```

into the complete adic ring `A{1/x}`, where `invAutX : A{1/x} ≃ₐ[R] A{1/x}` is the 𝔾m-inversion
automorphism (`annulusOverlapInvX`, `x ↦ x⁻¹`). Concretely

```
∇ᵢ : A ⊗̂_R A →+* A{1/x},   inl a ↦ locX a,   inr a ↦ invLocX a = invAutX (locX a).
```

Unlike the merged **right codiagonal** `A ⊗̂_R A{1/x} → A{1/x}` (`RightCodiagonalClosedEmbedding`,
whose domain is *localized*, giving only a locally-closed range), `∇ᵢ` has domain the un-localized
`A ⊗̂_R A` and is **surjective**: `inl` reaches `x` and `inr` reaches `x⁻¹`, and together with the
base `R` they topologically generate `A{1/x} = R{X, X⁻¹}`. This is exactly what the 𝔾m-**inversion**
model buys — under the earlier coordinate-*swap* model the analogous map had image the sub-annulus
`R{x, q·x⁻¹} ⊊ A{1/x}` and was *not* surjective. Surjectivity makes the base map of

```
Spf (A{1/x}) ⟶ Spf (A ⊗̂_R A)
```

a **closed** topological embedding into *all* of `Spf (A ⊗̂_R A)` (not merely a basic open), the
shape needed for the off-diagonal charts of the Tate self-product diagonal (issue 411b/424, route
(b) global closedness, EGA I §10.15).

## Main definitions and results

* `localizedCodiagInvX`: the map `∇ᵢ : A ⊗̂_R A →+* A{1/x}`, `inl a ↦ locX a`,
  `inr a ↦ invAutX (locX a)`.
* `localizedCodiagInvX_surjective`: `∇ᵢ` is surjective.
* `map_localizedCodiagInvX_eq`: `∇ᵢ` carries the ideal of definition of `A ⊗̂_R A` onto that of
  `A{1/x}` (`I·A{1/x}`).
* `isClosedEmbedding_map_localizedCodiagInvX`: the base map `Spf (A{1/x}) → Spf (A ⊗̂_R A)` of
  `Spf ∇ᵢ` is a closed topological embedding.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7, §9.
-/

noncomputable section

open Ideal AlgebraicGeometry CategoryTheory FormalSpectrum Topology RestrictedLaurentSeries

universe u

namespace CompletedTensorProduct

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)
variable [TopologicalSpace R] [IsAdicRing I]

/-- The away-localization/completion `R`-algebra map `locX : A →ₐ[R] A{1/x}`, `x ↦ x`. -/
abbrev locX : annulusAlgebra R I q →ₐ[R] annulusOverlap R I q :=
  IsScalarTower.toAlgHom R (annulusAlgebra R I q) (annulusOverlap R I q)

variable {R I q}

/-- The 𝔾m-inversion automorphism `invAutX : A{1/x} ≃ₐ[R] A{1/x}`, `x ↦ x⁻¹`, packaged as an
`R`-algebra equivalence from the ring equivalence `annulusOverlapInvX` (which fixes the base). -/
def invAutX (hI : I.FG) : annulusOverlap R I q ≃ₐ[R] annulusOverlap R I q :=
  AlgEquiv.ofRingEquiv (f := annulusOverlapInvX R I q hI) (annulusOverlapInvX_algebraMap R I q hI)

set_option linter.unusedSectionVars false in
@[simp] theorem invAutX_apply (hI : I.FG) (x : annulusOverlap R I q) :
    invAutX hI x = annulusOverlapInvX R I q hI x := rfl

variable (R I q) in
/-- The second leg `invLocX = invAutX ∘ locX : A →ₐ[R] A{1/x}`, `x ↦ x⁻¹`. -/
def invLocX (hI : I.FG) : annulusAlgebra R I q →ₐ[R] annulusOverlap R I q :=
  (invAutX hI).toAlgHom.comp (locX R I q)

set_option linter.unusedSectionVars false in
@[simp] theorem invLocX_apply (hI : I.FG) (a : annulusAlgebra R I q) :
    invLocX R I q hI a = annulusOverlapInvX R I q hI (locX R I q a) := rfl

variable (R I q) in
/-- **The inversion localized codiagonal** `∇ᵢ : A ⊗̂_R A →+* A{1/x}`, the lift of the pair
`(locX, invLocX)`: `inl a ↦ locX a`, `inr a ↦ invAutX (locX a)`. -/
def localizedCodiagInvX (hI : I.FG) :
    CompletedTensorProduct R I (annulusAlgebra R I q) (annulusAlgebra R I q) →+*
      annulusOverlap R I q :=
  haveI : IsAdicComplete (annulusOverlapIdeal R I q) (annulusOverlap R I q) :=
    (annulusOverlap_isAdicRing R I q hI).toIsAdicComplete
  lift (annulusOverlapIdeal R I q) (le_of_eq (overlapIdeal_eq_map R I q).symm)
    (locX R I q) (invLocX R I q hI)

set_option linter.unusedSectionVars false in
@[simp]
theorem localizedCodiagInvX_inl (hI : I.FG) (a : annulusAlgebra R I q) :
    localizedCodiagInvX R I q hI (inl R I _ _ a) = locX R I q a := by
  haveI : IsAdicComplete (annulusOverlapIdeal R I q) (annulusOverlap R I q) :=
    (annulusOverlap_isAdicRing R I q hI).toIsAdicComplete
  rw [localizedCodiagInvX, lift_inl]

set_option linter.unusedSectionVars false in
@[simp]
theorem localizedCodiagInvX_inr (hI : I.FG) (a : annulusAlgebra R I q) :
    localizedCodiagInvX R I q hI (inr R I _ _ a) = annulusOverlapInvX R I q hI (locX R I q a) := by
  haveI : IsAdicComplete (annulusOverlapIdeal R I q) (annulusOverlap R I q) :=
    (annulusOverlap_isAdicRing R I q hI).toIsAdicComplete
  rw [localizedCodiagInvX, lift_inr, invLocX_apply]

set_option linter.unusedSectionVars false in
/-- The inversion localized codiagonal is an `R`-algebra map: it sends `algebraMap R (A ⊗̂_R A)` to
`algebraMap R (A{1/x})`. -/
theorem localizedCodiagInvX_comp_algebraMap (hI : I.FG) :
    (localizedCodiagInvX R I q hI).comp
        (algebraMap R (CompletedTensorProduct R I (annulusAlgebra R I q) (annulusAlgebra R I q))) =
      algebraMap R (annulusOverlap R I q) := by
  ext r
  rw [RingHom.comp_apply,
    ← (inl R I (annulusAlgebra R I q) (annulusAlgebra R I q)).commutes r,
    localizedCodiagInvX_inl, AlgHom.commutes]

set_option linter.unusedSectionVars false in
/-- `∇ᵢ (inl a) = algebraMap L (A{1/x}) (algebraMap A L a)`: the first leg factors through the
away-localization `L = A[x⁻¹]` before completing to `A{1/x}`. -/
theorem localizedCodiagInvX_inl_apply (hI : I.FG) (a : annulusAlgebra R I q) :
    localizedCodiagInvX R I q hI
        (inl R I (annulusAlgebra R I q) (annulusAlgebra R I q) a)
      = algebraMap (annulusLoc R I q) (annulusOverlap R I q)
          (algebraMap (annulusAlgebra R I q) (annulusLoc R I q) a) := by
  rw [localizedCodiagInvX_inl, IsScalarTower.toAlgHom_apply,
    IsScalarTower.algebraMap_apply (annulusAlgebra R I q) (annulusLoc R I q)
      (annulusOverlap R I q)]

set_option linter.unusedSectionVars false in
/-- `∇ᵢ (inr x) = algebraMap L (A{1/x}) (x⁻¹)`: the second leg sends the coordinate `x` to the
localization inverse `x⁻¹`. Both `algebraMap L (A{1/x}) (x⁻¹)` and `∇ᵢ (inr x) = x⁻¹`
(`annulusOverlapInvX` applied to `x`) are two-sided inverses of `algebraMap A (A{1/x}) x` in the
commutative ring `A{1/x}` — the second via the crux `𝔾m`-identification `overlapEquiv` sending
`x ↦ X 1` and `x⁻¹ ↦ X (-1)` — so they coincide. -/
theorem localizedCodiagInvX_inr_overlapX (hI : I.FG) :
    localizedCodiagInvX R I q hI
        (inr R I (annulusAlgebra R I q) (annulusAlgebra R I q) (overlapX R I q))
      = algebraMap (annulusLoc R I q) (annulusOverlap R I q)
          (IsLocalization.Away.invSelf (overlapX R I q)) := by
  rw [localizedCodiagInvX_inr, IsScalarTower.toAlgHom_apply]
  -- both sides are the (two-sided) inverse of `algebraMap A (A{1/x}) x`
  have hu_of : algebraMap (annulusAlgebra R I q) (annulusOverlap R I q) (overlapX R I q)
      = algebraMap (annulusLoc R I q) (annulusOverlap R I q)
          (algebraMap (annulusAlgebra R I q) (annulusLoc R I q) (overlapX R I q)) :=
    IsScalarTower.algebraMap_apply (annulusAlgebra R I q) (annulusLoc R I q)
      (annulusOverlap R I q) (overlapX R I q)
  have ha : algebraMap (annulusLoc R I q) (annulusOverlap R I q)
        (IsLocalization.Away.invSelf (overlapX R I q))
      * algebraMap (annulusAlgebra R I q) (annulusOverlap R I q) (overlapX R I q) = 1 := by
    rw [hu_of, ← map_mul, mul_comm (IsLocalization.Away.invSelf (overlapX R I q)),
      IsLocalization.Away.mul_invSelf, map_one]
  have hb : annulusOverlapInvX R I q hI
        (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q) (overlapX R I q))
      * algebraMap (annulusAlgebra R I q) (annulusOverlap R I q) (overlapX R I q) = 1 := by
    apply (overlapEquiv R I q hI).injective
    have hidx : (-1 : ℤ) + 1 = 0 := by ring
    rw [map_mul, overlapEquiv_annulusOverlapInvX_overlapX, overlapEquiv_overlapX, map_one,
      X_add, hidx, X_zero]
  have huniq : ∀ a b : annulusOverlap R I q,
      a * algebraMap (annulusAlgebra R I q) (annulusOverlap R I q) (overlapX R I q) = 1 →
      b * algebraMap (annulusAlgebra R I q) (annulusOverlap R I q) (overlapX R I q) = 1 →
      a = b := by
    intro a b hna hnb
    calc a = a * (b * algebraMap (annulusAlgebra R I q) (annulusOverlap R I q)
              (overlapX R I q)) := by rw [hnb, mul_one]
      _ = (a * algebraMap (annulusAlgebra R I q) (annulusOverlap R I q) (overlapX R I q))
            * b := by ring
      _ = b := by rw [hna, one_mul]
  exact huniq _ _ hb ha

set_option linter.unusedSectionVars false in
/-- If a completion element `y : A{1/x}` and the image of a localization element `w : L = A[x⁻¹]`
share their first thickening (`mk w = evalₐ 1 y`), then they differ by an element of the ideal of
definition `annulusOverlapIdeal = I·A{1/x}` — the level-`1` step of successive approximation. The
Tate spelling of `FormalSpectrum.sub_algebraMap_mem_idealOfDefinition`. -/
theorem sub_algebraMap_mem_annulusOverlapIdeal (hI : I.FG) (y : annulusOverlap R I q)
    (w : annulusLoc R I q)
    (hw : Ideal.Quotient.mk ((annulusLocIdeal R I q) ^ 1) w
      = AdicCompletion.evalₐ (annulusLocIdeal R I q) 1 y) :
    y - algebraMap (annulusLoc R I q) (annulusOverlap R I q) w ∈ annulusOverlapIdeal R I q :=
  FormalSpectrum.sub_algebraMap_mem_idealOfDefinition (overlapX R I q) (annulusLocIdeal R I q)
    (hI.map _) y w hw

set_option linter.unusedSectionVars false in
/-- `∇ᵢ` carries the ideal of definition of `A ⊗̂_R A` onto that of `A{1/x}` (`I·A{1/x}`). Same
statement as `map_localizedCodiagInvX_eq`, restated here so it is usable inside the surjectivity
proof (which precedes the `IsAdicRing` variable block). -/
theorem map_idealOfDefinition_localizedCodiagInvX (hI : I.FG) :
    (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)).map
        (localizedCodiagInvX R I q hI) = annulusOverlapIdeal R I q := by
  rw [idealOfDefinition_eq_map (R := R) (I := I) (A := annulusAlgebra R I q)
      (B := annulusAlgebra R I q), Ideal.map_map, localizedCodiagInvX_comp_algebraMap,
    ← overlapIdeal_eq_map]

set_option linter.unusedSectionVars false in
/-- Any element `w` of the away-localization `L = A[x⁻¹]` is `(algebraMap A L r)·(x⁻¹)ⁿ` for the
chosen numerator/exponent `(r, n) = sec x w`. The Tate spelling of
`FormalSpectrum.localizationAway_eq_sec`. -/
theorem annulusLoc_eq_sec (w : annulusLoc R I q) :
    w = algebraMap (annulusAlgebra R I q) (annulusLoc R I q)
          (IsLocalization.Away.sec (overlapX R I q) w).1
        * IsLocalization.Away.invSelf (overlapX R I q)
            ^ (IsLocalization.Away.sec (overlapX R I q) w).2 :=
  FormalSpectrum.localizationAway_eq_sec (overlapX R I q) w

set_option linter.unusedSectionVars false in
/-- The explicit lift of `w : L = A[x⁻¹]` through `∇ᵢ`: with `(r, n) = sec x w`, the element
`inl r · (inr x)ⁿ` of `A ⊗̂_R A` maps to `algebraMap L (A{1/x}) w`, using
`∇ᵢ (inl r) = algebraMap L (A{1/x}) (algebraMap A L r)`,
`∇ᵢ (inr x) = algebraMap L (A{1/x}) (x⁻¹)` and the decomposition `w = (algebraMap A L r)·(x⁻¹)ⁿ`. -/
theorem localizedCodiagInvX_sec_witness (hI : I.FG) (w : annulusLoc R I q) :
    localizedCodiagInvX R I q hI
        (inl R I (annulusAlgebra R I q) (annulusAlgebra R I q)
            (IsLocalization.Away.sec (overlapX R I q) w).1
          * (inr R I (annulusAlgebra R I q) (annulusAlgebra R I q) (overlapX R I q))
              ^ (IsLocalization.Away.sec (overlapX R I q) w).2)
      = algebraMap (annulusLoc R I q) (annulusOverlap R I q) w := by
  rw [map_mul, map_pow, localizedCodiagInvX_inl_apply, localizedCodiagInvX_inr_overlapX,
    ← map_pow, ← map_mul, ← annulusLoc_eq_sec]

set_option linter.unusedSectionVars false in
/-- **The inversion localized codiagonal `∇ᵢ` is surjective.** Modulo the ideal of definition
`A{1/x}` is the localization `Ā[x⁻¹]` of `Ā = A/I·A` at `x̄`; the image of `∇ᵢ` mod `I` contains
`Ā` (via `inl`/`locX`) and the unit `x̄⁻¹` (via `inr`), so it is all of `Ā[x⁻¹]`. This lifts to
surjectivity by successive approximation for complete adic rings.

That argument is `FormalSpectrum.surjective_of_algebraMap_mem_range'`
(`FormalSchemes/AwayCompletionSurjective.lean`), and this theorem is an application of it: the two
hypotheses are exactly `localizedCodiagInvX_inl_apply` and `localizedCodiagInvX_inr_overlapX`. Note
that the *primed* form is the one needed — the target `A{1/x} = annulusOverlap` completes at
`annulusLocIdeal = I·A[x⁻¹]`, the extension of the ideal of the **base** `R`, so it is not literally
a `FormalSpectrum.awayCompletion` of an ideal of `A` (the two ideals agree only by `Ideal.map_map`,
not definitionally). -/
theorem localizedCodiagInvX_surjective (hI : I.FG) :
    Function.Surjective (localizedCodiagInvX R I q hI) := by
  haveI : IsPrecomplete (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))
      (CompletedTensorProduct R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :=
    (isAdicRing R I (annulusAlgebra R I q) (annulusAlgebra R I q)
      hI).toIsAdicComplete.toIsPrecomplete
  exact FormalSpectrum.surjective_of_algebraMap_mem_range' (overlapX R I q)
    (annulusLocIdeal R I q) (hI.map _) _ _
    (map_idealOfDefinition_localizedCodiagInvX (R := R) (I := I) (q := q) hI)
    (fun c => ⟨inl R I _ _ c, localizedCodiagInvX_inl_apply hI c⟩)
    ⟨inr R I _ _ (overlapX R I q), localizedCodiagInvX_inr_overlapX hI⟩

variable
  [TopologicalSpace (CompletedTensorProduct R I (annulusAlgebra R I q) (annulusAlgebra R I q))]
  [IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))]

set_option linter.unusedSectionVars false in
/-- `∇ᵢ` carries the ideal of definition of `A ⊗̂_R A` exactly onto that of `A{1/x}`
(`annulusOverlapIdeal = I·A{1/x}`). -/
theorem map_localizedCodiagInvX_eq (hI : I.FG) :
    (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)).map
        (localizedCodiagInvX R I q hI) = annulusOverlapIdeal R I q := by
  rw [idealOfDefinition_eq_map (R := R) (I := I) (A := annulusAlgebra R I q)
      (B := annulusAlgebra R I q), Ideal.map_map, localizedCodiagInvX_comp_algebraMap,
    ← overlapIdeal_eq_map]

set_option linter.unusedSectionVars false in
/-- `∇ᵢ` carries the ideal of definition of `A ⊗̂_R A` into the ideal of definition
`annulusOverlapIdeal` of `A{1/x}` — the continuity/adic-compatibility input making `∇ᵢ` induce a
morphism of formal spectra. -/
theorem localizedCodiagInvX_le_comap (hI : I.FG) :
    idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≤
      (annulusOverlapIdeal R I q).comap (localizedCodiagInvX R I q hI) := by
  haveI : IsAdicComplete (annulusOverlapIdeal R I q) (annulusOverlap R I q) :=
    (annulusOverlap_isAdicRing R I q hI).toIsAdicComplete
  exact lift_le_comap (le_of_eq (overlapIdeal_eq_map R I q).symm)
    (locX R I q) (invLocX R I q hI) hI

set_option linter.unusedSectionVars false in
/-- **The base map of `Spf ∇ᵢ : Spf (A{1/x}) → Spf (A ⊗̂_R A)` is a closed topological embedding.**
`∇ᵢ` is surjective (`localizedCodiagInvX_surjective`), and `Spf` of a surjection is a closed
embedding (`FormalSpectrum.isClosedEmbedding_map_of_surjective`). This is the shape the merged right
codiagonal (`RightCodiagonalClosedEmbedding`) could *not* provide: its range is closed in *all* of
`Spf (A ⊗̂_R A)`, not merely in an open subset. -/
theorem isClosedEmbedding_map_localizedCodiagInvX (hI : I.FG) :
    IsClosedEmbedding
      (FormalSpectrum.map
        (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))
        (annulusOverlapIdeal R I q) (localizedCodiagInvX R I q hI)
        (localizedCodiagInvX_le_comap hI)) :=
  FormalSpectrum.isClosedEmbedding_map_of_surjective
    (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))
    (annulusOverlapIdeal R I q) (localizedCodiagInvX R I q hI)
    (localizedCodiagInvX_le_comap hI) (localizedCodiagInvX_surjective hI)

end CompletedTensorProduct
