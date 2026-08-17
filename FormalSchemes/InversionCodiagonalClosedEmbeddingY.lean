import FormalSchemes.InversionCodiagonalClosedEmbedding

set_option linter.style.header false

/-!
# The y-side inversion localized codiagonal `A ⊗̂_R A → A{1/y}` and its closed-embedding spectrum

This is the `y`-side mirror of `InversionCodiagonalClosedEmbedding` (the `x`-side inversion
localized codiagonal `∇ᵢ : A ⊗̂_R A → A{1/x}`). Fix an adic ring `(R, I)` (with `I` finitely
generated) and a Tate parameter `q ∈ R`, let `A = annulusAlgebra R I q` be the formal Tate annulus,
and let `A{1/y} = annulusOverlapY` be its `y`-overlap chart. The **y-side inversion localized
codiagonal** is the composite of the `x`-side map with the 𝔾m-inversion overlap transition
`annulusOverlapInversion : A{1/x} ≃+* A{1/y}` (`x ↦ y⁻¹`, the geometrically-correct Tate 2-gon
gluing; the underlying ring equivalence of `annulusOverlapInversionAlg`):

```
∇ᵢʸ : A ⊗̂_R A →+* A{1/y},   ∇ᵢʸ = annulusOverlapInversion ∘ ∇ᵢ.
```

Because `annulusOverlapInversion` is an `R`-algebra isomorphism, `∇ᵢʸ` inherits from `∇ᵢ` every
property that made the `x`-side brick usable in the off-diagonal assembly: it is **surjective**
(a bijection composed with a surjection), it carries the ideal of definition of `A ⊗̂_R A` onto that
of `A{1/y}` (`I·A{1/y}`), and hence the base map of

```
Spf (A{1/y}) ⟶ Spf (A ⊗̂_R A)
```

is a **closed** topological embedding into *all* of `Spf (A ⊗̂_R A)` (not merely a basic open). This
is the missing **first-factor-overlap** affine brick the mixed-chart assembly of the Tate
self-product diagonal needs (issue 424-ii/503), complementing the `x`-side second-factor-overlap
brick (issue 502/#225).

## Main definitions and results

* `annulusOverlapIdealY`, `annulusOverlapY_isAdicRing`, `overlapIdealY_eq_map`: the y-side
  ideal-of-definition infrastructure (mirroring the x-side objects in `TateOverlap`).
* `localizedCodiagInvY`: the map `∇ᵢʸ : A ⊗̂_R A →+* A{1/y}`.
* `localizedCodiagInvY_surjective`: `∇ᵢʸ` is surjective.
* `map_localizedCodiagInvY_eq`: `∇ᵢʸ` carries the ideal of definition of `A ⊗̂_R A` onto that of
  `A{1/y}` (`I·A{1/y}`).
* `isClosedEmbedding_map_localizedCodiagInvY`: the base map `Spf (A{1/y}) → Spf (A ⊗̂_R A)` of
  `Spf ∇ᵢʸ` is a closed topological embedding.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7, §9.
-/

noncomputable section

open Ideal AlgebraicGeometry CategoryTheory FormalSpectrum Topology RestrictedLaurentSeries

universe u

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-! ### The y-side ideal-of-definition infrastructure (mirror of `TateOverlap`) -/

/-- The ideal of definition of `A[y⁻¹]^∧`: the extension of `I·A[y⁻¹]` to the completion. -/
abbrev annulusOverlapIdealY : Ideal (annulusOverlapY R I q) :=
  (annulusLocIdealY R I q).map (algebraMap (annulusLocY R I q) (annulusOverlapY R I q))

/-- `A[y⁻¹]^∧` is a complete adic ring with ideal of definition `I·A[y⁻¹]^∧` (`I` f.g.). -/
theorem annulusOverlapY_isAdicRing (hI : I.FG) :
    IsAdicRing (annulusOverlapIdealY R I q) :=
  AdicCompletion.isAdicRing_map _ (hI.map _)

theorem annulusOverlapY_isAdicComplete (hI : I.FG) :
    IsAdicComplete (annulusOverlapIdealY R I q) (annulusOverlapY R I q) :=
  AdicCompletion.isAdicComplete_map _ (hI.map _)

/-- The ideal of definition of `A[y⁻¹]^∧` is the extension of `I` itself. -/
theorem overlapIdealY_eq_map :
    annulusOverlapIdealY R I q = I.map (algebraMap R (annulusOverlapY R I q)) := by
  change (I.map (algebraMap R (annulusLocY R I q))).map
      (algebraMap (annulusLocY R I q) (annulusOverlapY R I q)) = _
  rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R (annulusLocY R I q) (annulusOverlapY R I q)]

namespace CompletedTensorProduct

variable [TopologicalSpace R] [IsAdicRing I]

/-- **The y-side inversion localized codiagonal** `∇ᵢʸ : A ⊗̂_R A →+* A{1/y}`, the `x`-side map
`∇ᵢ` followed by the 𝔾m-inversion overlap transition `annulusOverlapInversion : A{1/x} ≃+* A{1/y}`
(the underlying ring equivalence of `annulusOverlapInversionAlg`). -/
def localizedCodiagInvY (hI : I.FG) :
    CompletedTensorProduct R I (annulusAlgebra R I q) (annulusAlgebra R I q) →+*
      annulusOverlapY R I q :=
  (annulusOverlapInversion R I q hI : annulusOverlap R I q →+* annulusOverlapY R I q).comp
    (localizedCodiagInvX R I q hI)

variable {R I q}

set_option linter.unusedSectionVars false in
theorem localizedCodiagInvY_apply (hI : I.FG)
    (t : CompletedTensorProduct R I (annulusAlgebra R I q) (annulusAlgebra R I q)) :
    localizedCodiagInvY R I q hI t =
      annulusOverlapInversion R I q hI (localizedCodiagInvX R I q hI t) := rfl

set_option linter.unusedSectionVars false in
@[simp]
theorem localizedCodiagInvY_inl (hI : I.FG) (a : annulusAlgebra R I q) :
    localizedCodiagInvY R I q hI (inl R I _ _ a) =
      annulusOverlapInversion R I q hI (locX R I q a) := by
  rw [localizedCodiagInvY_apply, localizedCodiagInvX_inl]

set_option linter.unusedSectionVars false in
@[simp]
theorem localizedCodiagInvY_inr (hI : I.FG) (a : annulusAlgebra R I q) :
    localizedCodiagInvY R I q hI (inr R I _ _ a) =
      annulusOverlapInversion R I q hI (annulusOverlapInvX R I q hI (locX R I q a)) := by
  rw [localizedCodiagInvY_apply, localizedCodiagInvX_inr]

set_option linter.unusedSectionVars false in
/-- The y-side inversion localized codiagonal is an `R`-algebra map: both legs and the inversion
transition commute with `algebraMap R`. -/
theorem localizedCodiagInvY_comp_algebraMap (hI : I.FG) :
    (localizedCodiagInvY R I q hI).comp
        (algebraMap R (CompletedTensorProduct R I (annulusAlgebra R I q) (annulusAlgebra R I q))) =
      algebraMap R (annulusOverlapY R I q) := by
  ext r
  have hx : localizedCodiagInvX R I q hI
      (algebraMap R (CompletedTensorProduct R I (annulusAlgebra R I q) (annulusAlgebra R I q)) r)
      = algebraMap R (annulusOverlap R I q) r := by
    rw [← RingHom.comp_apply, localizedCodiagInvX_comp_algebraMap]
  rw [RingHom.comp_apply, localizedCodiagInvY_apply, hx, annulusOverlapInversion_algebraMap]

set_option linter.unusedSectionVars false in
/-- **The y-side inversion localized codiagonal `∇ᵢʸ` is surjective**: `∇ᵢ` is surjective
(`localizedCodiagInvX_surjective`) and `annulusOverlapInversion` is a bijection. -/
theorem localizedCodiagInvY_surjective (hI : I.FG) :
    Function.Surjective (localizedCodiagInvY R I q hI) := by
  intro z
  obtain ⟨y, rfl⟩ := (annulusOverlapInversion R I q hI).surjective z
  obtain ⟨t, rfl⟩ := localizedCodiagInvX_surjective (R := R) (I := I) (q := q) hI y
  exact ⟨t, rfl⟩

set_option linter.unusedSectionVars false in
/-- The inversion transition carries the x-side ideal of definition `I·A{1/x}` onto the y-side one
`I·A{1/y}` (it is an `R`-algebra isomorphism). -/
theorem map_annulusOverlapInversion_annulusOverlapIdeal (hI : I.FG) :
    (annulusOverlapIdeal R I q).map
        (annulusOverlapInversion R I q hI : annulusOverlap R I q →+* annulusOverlapY R I q)
      = annulusOverlapIdealY R I q := by
  have he : (annulusOverlapInversion R I q hI :
        annulusOverlap R I q →+* annulusOverlapY R I q).comp
        (algebraMap R (annulusOverlap R I q)) = algebraMap R (annulusOverlapY R I q) :=
    RingHom.ext fun r => annulusOverlapInversion_algebraMap R I q hI r
  rw [overlapIdeal_eq_map, Ideal.map_map, he, ← overlapIdealY_eq_map]

set_option linter.unusedSectionVars false in
/-- `∇ᵢʸ` carries the ideal of definition of `A ⊗̂_R A` exactly onto that of `A{1/y}`
(`annulusOverlapIdealY = I·A{1/y}`). -/
theorem map_localizedCodiagInvY_eq (hI : I.FG) :
    (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)).map
        (localizedCodiagInvY R I q hI) = annulusOverlapIdealY R I q := by
  rw [localizedCodiagInvY, ← Ideal.map_map,
    map_idealOfDefinition_localizedCodiagInvX (R := R) (I := I) (q := q) hI,
    map_annulusOverlapInversion_annulusOverlapIdeal]

set_option linter.unusedSectionVars false in
/-- `∇ᵢʸ` carries the ideal of definition of `A ⊗̂_R A` into that of `A{1/y}` — the
continuity/adic-compatibility input making `∇ᵢʸ` induce a morphism of formal spectra. -/
theorem localizedCodiagInvY_le_comap (hI : I.FG) :
    idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≤
      (annulusOverlapIdealY R I q).comap (localizedCodiagInvY R I q hI) := by
  rw [← map_localizedCodiagInvY_eq (R := R) (I := I) (q := q) hI]
  exact Ideal.le_comap_map

set_option linter.unusedSectionVars false in
/-- **The base map of `Spf ∇ᵢʸ : Spf (A{1/y}) → Spf (A ⊗̂_R A)` is a closed topological embedding.**
`∇ᵢʸ` is surjective (`localizedCodiagInvY_surjective`), and `Spf` of a surjection is a closed
embedding (`FormalSpectrum.isClosedEmbedding_map_of_surjective`). Closed into *all* of
`Spf (A ⊗̂_R A)` — the shape the mixed-chart assembly (issue 503) consumes for its
first-factor-overlap piece. -/
theorem isClosedEmbedding_map_localizedCodiagInvY (hI : I.FG) :
    IsClosedEmbedding
      (FormalSpectrum.map
        (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))
        (annulusOverlapIdealY R I q) (localizedCodiagInvY R I q hI)
        (localizedCodiagInvY_le_comap hI)) :=
  FormalSpectrum.isClosedEmbedding_map_of_surjective
    (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))
    (annulusOverlapIdealY R I q) (localizedCodiagInvY R I q hI)
    (localizedCodiagInvY_le_comap hI) (localizedCodiagInvY_surjective hI)

end CompletedTensorProduct
