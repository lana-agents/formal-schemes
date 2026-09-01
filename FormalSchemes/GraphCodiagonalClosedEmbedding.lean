import FormalSchemes.InversionCodiagonalClosedEmbeddingY

set_option linter.style.header false

/-!
# The graph codiagonals `A ⊗̂_R A → A{1/x}`, `A ⊗̂_R A → A{1/y}` of the Tate gluing

Fix an adic ring `(R, I)` (with `I` finitely generated) and a Tate parameter `q ∈ R`, let
`A = annulusAlgebra R I q` be the formal Tate annulus and `A{1/x} = annulusOverlap`,
`A{1/y} = annulusOverlapY` its two overlap charts.

The Tate curve model `𝔈_q` glues two copies of `Spf A` along `Spf A{1/x} ⨿ Spf A{1/y}`, the
`x`-overlap of the *first* chart being identified with the `y`-overlap of the *second* one through
the 𝔾m-inversion transition `annulusOverlapInversion : A{1/x} ≃+* A{1/y}` (`x ↦ y⁻¹`). Consequently
the diagonal of `𝔈_q ×_{Spf R} 𝔈_q`, read in a **mixed** chart `Spf(A ⊗̂_R A)` (first factor the
curve chart `b`, second factor the curve chart `¬b`), is the **graph of that gluing**: the union of

* the piece parametrised by `Spf A{1/x}`, whose first factor is the point `x`-invertible in chart
  `b` and whose second factor is its `y`-invertible partner in chart `¬b`; and
* the piece parametrised by `Spf A{1/y}`, with the roles of `x` and `y` exchanged.

The two ring maps cutting these pieces out are the **graph codiagonals**

```
∇ˣ : A ⊗̂_R A →+* A{1/x},   inl a ↦ locX a,   inr a ↦ x⁻¹-inversion of `locX (flip a)`
∇ʸ : A ⊗̂_R A →+* A{1/y},   inl a ↦ locY a,   inr a ↦ annulusOverlapInversion (locX a)
```

where `flip = annulusFlip : A ≃ₐ[R] A` is the coordinate swap `x ↔ y`. Both are **surjective**
(each is the already-merged inversion localized codiagonal `localizedCodiagInvX` precomposed with
an automorphism of `A ⊗̂_R A`), so the base maps of `Spf ∇ˣ` and `Spf ∇ʸ` are **closed** topological
embeddings into *all* of `Spf(A ⊗̂_R A)`.

## Relation to `InversionCodiagonalClosedEmbedding{,Y}`

The merged bricks `localizedCodiagInvX` (`inl a ↦ locX a`, `inr a ↦ locX a` inverted) and
`localizedCodiagInvY = annulusOverlapInversion ∘ localizedCodiagInvX` differ by an *isomorphism* of
the target, so the base maps of their formal spectra have the **same range**; they therefore cut out
a single closed subset, not the two distinct mixed-chart pieces. The two pieces above are instead
obtained by precomposing `localizedCodiagInvX` with the automorphisms `A ⊗̂_R A ≃ A ⊗̂_R A` given by
`id ⊗̂ flip` and (for the `y`-piece) `commHom ∘ (flip ⊗̂ id)`; this is what the present file does.

## Main definitions and results

* `CompletedTensorProduct.graphCodiagX`, `...graphCodiagY`: the two graph codiagonals.
* `...graphCodiagX_inl`/`_inr`, `...graphCodiagY_inl`/`_inr`: their legs.
* `...graphCodiagX_surjective`, `...graphCodiagY_surjective`: surjectivity.
* `...map_graphCodiagX_eq`, `...map_graphCodiagY_eq`: they carry the ideal of definition of
  `A ⊗̂_R A` onto `I·A{1/x}`, resp. `I·A{1/y}`.
* `...isClosedEmbedding_map_graphCodiagX`, `...isClosedEmbedding_map_graphCodiagY`: the base maps of
  their formal spectra are closed topological embeddings.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7, §9.
-/

noncomputable section

open Ideal AlgebraicGeometry CategoryTheory FormalSpectrum Topology RestrictedLaurentSeries

universe u

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-! ### Three transition identities -/

/-- The `x`-side 𝔾m-inversion is an involution. -/
theorem annulusOverlapInvX_annulusOverlapInvX (hI : I.FG) (z : annulusOverlap R I q) :
    annulusOverlapInvX R I q hI (annulusOverlapInvX R I q hI z) = z := by
  apply (overlapEquiv R I q hI).injective
  rw [overlapEquiv_annulusOverlapInvX, overlapEquiv_annulusOverlapInvX, rlsInv_rlsInv]

/-- The flip transition `A{1/x} ≃+* A{1/y}` intertwines the two structural maps from `A` through
the coordinate swap `annulusFlip`. -/
theorem annulusOverlapTransition_algebraMap_annulus (hI : I.FG) (a : annulusAlgebra R I q) :
    annulusOverlapTransition R I q hI
        (algebraMap (annulusAlgebra R I q) (annulusOverlap R I q) a) =
      algebraMap (annulusAlgebra R I q) (annulusOverlapY R I q) (annulusFlip R I q hI a) := by
  rw [annulusOverlapTransition_apply,
    IsScalarTower.algebraMap_apply (annulusAlgebra R I q) (annulusLoc R I q)
      (annulusOverlap R I q),
    annulusOverlapTransitionHom_algebraMap, annulusLocTransition_algebraMap,
    ← IsScalarTower.algebraMap_apply (annulusAlgebra R I q) (annulusLocY R I q)
      (annulusOverlapY R I q)]

/-- Precomposing the 𝔾m-inversion transition `x ↦ y⁻¹` with the `x`-side inversion `x ↦ x⁻¹`
recovers the plain flip transition `x ↦ y`. -/
theorem annulusOverlapInversion_annulusOverlapInvX (hI : I.FG) (z : annulusOverlap R I q) :
    annulusOverlapInversion R I q hI (annulusOverlapInvX R I q hI z) =
      annulusOverlapTransition R I q hI z := by
  rw [annulusOverlapInversion_apply, annulusOverlapInvX_annulusOverlapInvX]

namespace CompletedTensorProduct

variable [TopologicalSpace R] [IsAdicRing I]

/-- The `y`-side away-localization/completion `R`-algebra map `locY : A →ₐ[R] A{1/y}`. -/
abbrev locY : annulusAlgebra R I q →ₐ[R] annulusOverlapY R I q :=
  IsScalarTower.toAlgHom R (annulusAlgebra R I q) (annulusOverlapY R I q)

/-! ### The two automorphisms of `A ⊗̂_R A` -/

set_option linter.unusedSectionVars false in
/-- `id ⊗̂ flip` is surjective: it is an involution of `A ⊗̂_R A`, by functoriality of
`CompletedTensorProduct.map` and the involutivity of the coordinate swap `annulusFlip`. -/
theorem map_id_flip_surjective (hI : I.FG) :
    Function.Surjective
      (map hI (AlgHom.id R (annulusAlgebra R I q)) (annulusFlipHom R I q hI)) := by
  intro t
  refine ⟨map hI (AlgHom.id R (annulusAlgebra R I q)) (annulusFlipHom R I q hI) t, ?_⟩
  rw [← RingHom.comp_apply, ← map_comp, AlgHom.id_comp, annulusFlipHom_annulusFlipHom, map_id,
    RingHom.id_apply]

set_option linter.unusedSectionVars false in
/-- The swap `commHom : A ⊗̂_R A →+* A ⊗̂_R A` is surjective (it underlies `commEquiv`). -/
theorem commHom_surjective_self (hI : I.FG) :
    Function.Surjective (commHom (R := R) (I := I) (A := annulusAlgebra R I q)
      (B := annulusAlgebra R I q) hI) :=
  (commEquiv (R := R) (I := I) (A := annulusAlgebra R I q)
    (B := annulusAlgebra R I q) hI).surjective

/-! ### The `x`-side graph codiagonal -/

/-- **The `x`-side graph codiagonal** `∇ˣ : A ⊗̂_R A →+* A{1/x}`: the inversion localized codiagonal
`localizedCodiagInvX` precomposed with the automorphism `id ⊗̂ flip` of `A ⊗̂_R A`. Its legs are
`inl a ↦ locX a` and `inr a ↦ annulusOverlapInvX (locX (flip a))`. -/
def graphCodiagX (hI : I.FG) :
    CompletedTensorProduct R I (annulusAlgebra R I q) (annulusAlgebra R I q) →+*
      annulusOverlap R I q :=
  (localizedCodiagInvX R I q hI).comp
    (map hI (AlgHom.id R (annulusAlgebra R I q)) (annulusFlipHom R I q hI))

variable {R I q}

set_option linter.unusedSectionVars false in
@[simp] theorem graphCodiagX_inl (hI : I.FG) (a : annulusAlgebra R I q) :
    graphCodiagX R I q hI (inl R I _ _ a) = locX R I q a := by
  rw [graphCodiagX, RingHom.comp_apply, map_inl, AlgHom.id_apply, localizedCodiagInvX_inl]

set_option linter.unusedSectionVars false in
@[simp] theorem graphCodiagX_inr (hI : I.FG) (a : annulusAlgebra R I q) :
    graphCodiagX R I q hI (inr R I _ _ a) =
      annulusOverlapInvX R I q hI (locX R I q (annulusFlipHom R I q hI a)) := by
  rw [graphCodiagX, RingHom.comp_apply, map_inr, localizedCodiagInvX_inr]

set_option linter.unusedSectionVars false in
/-- **The `x`-side graph codiagonal is surjective**: it is the surjection `localizedCodiagInvX`
precomposed with the automorphism `id ⊗̂ flip`. -/
theorem graphCodiagX_surjective (hI : I.FG) :
    Function.Surjective (graphCodiagX R I q hI) :=
  (localizedCodiagInvX_surjective (R := R) (I := I) (q := q) hI).comp
    (map_id_flip_surjective (R := R) (I := I) (q := q) hI)

set_option linter.unusedSectionVars false in
/-- `∇ˣ` is an `R`-algebra map. -/
theorem graphCodiagX_comp_algebraMap (hI : I.FG) :
    (graphCodiagX R I q hI).comp
        (algebraMap R (CompletedTensorProduct R I (annulusAlgebra R I q)
          (annulusAlgebra R I q))) =
      algebraMap R (annulusOverlap R I q) := by
  rw [graphCodiagX, RingHom.comp_assoc, map_comp_algebraMap, localizedCodiagInvX_comp_algebraMap]

set_option linter.unusedSectionVars false in
/-- `∇ˣ` carries the ideal of definition of `A ⊗̂_R A` exactly onto `I·A{1/x}`. -/
theorem map_graphCodiagX_eq (hI : I.FG) :
    (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)).map
        (graphCodiagX R I q hI) = annulusOverlapIdeal R I q := by
  rw [idealOfDefinition_eq_map (R := R) (I := I) (A := annulusAlgebra R I q)
      (B := annulusAlgebra R I q), Ideal.map_map, graphCodiagX_comp_algebraMap,
    ← overlapIdeal_eq_map]

set_option linter.unusedSectionVars false in
/-- `∇ˣ` is continuous for the adic topologies. -/
theorem graphCodiagX_le_comap (hI : I.FG) :
    idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≤
      (annulusOverlapIdeal R I q).comap (graphCodiagX R I q hI) := by
  rw [← map_graphCodiagX_eq (R := R) (I := I) (q := q) hI]
  exact Ideal.le_comap_map

/-! ### The `y`-side graph codiagonal -/

variable (R I q)

/-- **The `y`-side graph codiagonal** `∇ʸ : A ⊗̂_R A →+* A{1/y}`: the `x`-side graph codiagonal
precomposed with the swap `commHom` and postcomposed with the 𝔾m-inversion transition. Its legs are
`inl a ↦ locY a` and `inr a ↦ annulusOverlapInversion (locX a)`. -/
def graphCodiagY (hI : I.FG) :
    CompletedTensorProduct R I (annulusAlgebra R I q) (annulusAlgebra R I q) →+*
      annulusOverlapY R I q :=
  (annulusOverlapInversion R I q hI : annulusOverlap R I q →+* annulusOverlapY R I q).comp
    ((graphCodiagX R I q hI).comp
      (commHom (R := R) (I := I) (A := annulusAlgebra R I q)
        (B := annulusAlgebra R I q) hI))

variable {R I q}

set_option linter.unusedSectionVars false in
@[simp] theorem graphCodiagY_inl (hI : I.FG) (a : annulusAlgebra R I q) :
    graphCodiagY R I q hI (inl R I _ _ a) = locY R I q a := by
  rw [graphCodiagY, RingHom.comp_apply, RingHom.comp_apply, commHom_inl, graphCodiagX_inr,
    IsScalarTower.toAlgHom_apply, RingHom.coe_coe, annulusOverlapInversion_annulusOverlapInvX,
    annulusOverlapTransition_algebraMap_annulus, annulusFlip_apply, ← AlgHom.comp_apply,
    annulusFlipHom_annulusFlipHom, AlgHom.id_apply, IsScalarTower.toAlgHom_apply]

set_option linter.unusedSectionVars false in
@[simp] theorem graphCodiagY_inr (hI : I.FG) (a : annulusAlgebra R I q) :
    graphCodiagY R I q hI (inr R I _ _ a) =
      annulusOverlapInversion R I q hI (locX R I q a) := by
  rw [graphCodiagY, RingHom.comp_apply, RingHom.comp_apply, commHom_inr, graphCodiagX_inl,
    RingHom.coe_coe]

set_option linter.unusedSectionVars false in
/-- **The `y`-side graph codiagonal is surjective.** -/
theorem graphCodiagY_surjective (hI : I.FG) :
    Function.Surjective (graphCodiagY R I q hI) :=
  ((annulusOverlapInversion R I q hI).surjective.comp
    (graphCodiagX_surjective (R := R) (I := I) (q := q) hI)).comp
      (commHom_surjective_self (R := R) (I := I) (q := q) hI)

set_option linter.unusedSectionVars false in
/-- `∇ʸ` is an `R`-algebra map. -/
theorem graphCodiagY_comp_algebraMap (hI : I.FG) :
    (graphCodiagY R I q hI).comp
        (algebraMap R (CompletedTensorProduct R I (annulusAlgebra R I q)
          (annulusAlgebra R I q))) =
      algebraMap R (annulusOverlapY R I q) := by
  ext r
  have hc : commHom (R := R) (I := I) (A := annulusAlgebra R I q)
      (B := annulusAlgebra R I q) hI
      (algebraMap R (CompletedTensorProduct R I (annulusAlgebra R I q)
        (annulusAlgebra R I q)) r) =
      algebraMap R (CompletedTensorProduct R I (annulusAlgebra R I q)
        (annulusAlgebra R I q)) r := by
    have h1 : inl R I (annulusAlgebra R I q) (annulusAlgebra R I q)
        (algebraMap R (annulusAlgebra R I q) r) =
        algebraMap R (CompletedTensorProduct R I (annulusAlgebra R I q)
          (annulusAlgebra R I q)) r :=
      (inl R I (annulusAlgebra R I q) (annulusAlgebra R I q)).commutes r
    have h2 : inr R I (annulusAlgebra R I q) (annulusAlgebra R I q)
        (algebraMap R (annulusAlgebra R I q) r) =
        algebraMap R (CompletedTensorProduct R I (annulusAlgebra R I q)
          (annulusAlgebra R I q)) r :=
      (inr R I (annulusAlgebra R I q) (annulusAlgebra R I q)).commutes r
    conv_lhs => rw [← h1]
    rw [commHom_inl, h2]
  have hx : graphCodiagX R I q hI
      (algebraMap R (CompletedTensorProduct R I (annulusAlgebra R I q)
        (annulusAlgebra R I q)) r) = algebraMap R (annulusOverlap R I q) r := by
    rw [← RingHom.comp_apply, graphCodiagX_comp_algebraMap]
  rw [RingHom.comp_apply, graphCodiagY, RingHom.comp_apply, RingHom.comp_apply, hc, hx,
    RingHom.coe_coe, annulusOverlapInversion_algebraMap]

set_option linter.unusedSectionVars false in
/-- `∇ʸ` carries the ideal of definition of `A ⊗̂_R A` exactly onto `I·A{1/y}`. -/
theorem map_graphCodiagY_eq (hI : I.FG) :
    (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q)).map
        (graphCodiagY R I q hI) = annulusOverlapIdealY R I q := by
  rw [idealOfDefinition_eq_map (R := R) (I := I) (A := annulusAlgebra R I q)
      (B := annulusAlgebra R I q), Ideal.map_map, graphCodiagY_comp_algebraMap,
    ← overlapIdealY_eq_map]

set_option linter.unusedSectionVars false in
/-- `∇ʸ` is continuous for the adic topologies. -/
theorem graphCodiagY_le_comap (hI : I.FG) :
    idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q) ≤
      (annulusOverlapIdealY R I q).comap (graphCodiagY R I q hI) := by
  rw [← map_graphCodiagY_eq (R := R) (I := I) (q := q) hI]
  exact Ideal.le_comap_map

/-! ### The two closed embeddings -/

variable
  [TopologicalSpace (CompletedTensorProduct R I (annulusAlgebra R I q) (annulusAlgebra R I q))]
  [IsAdicRing (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))]

set_option linter.unusedSectionVars false in
/-- **The base map of `Spf ∇ˣ : Spf (A{1/x}) → Spf (A ⊗̂_R A)` is a closed topological embedding.**
This is the `x`-piece of the mixed-chart preimage of the Tate diagonal. -/
theorem isClosedEmbedding_map_graphCodiagX (hI : I.FG) :
    IsClosedEmbedding
      (FormalSpectrum.map
        (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))
        (annulusOverlapIdeal R I q) (graphCodiagX R I q hI)
        (graphCodiagX_le_comap hI)) :=
  FormalSpectrum.isClosedEmbedding_map_of_surjective
    (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))
    (annulusOverlapIdeal R I q) (graphCodiagX R I q hI)
    (graphCodiagX_le_comap hI) (graphCodiagX_surjective hI)

set_option linter.unusedSectionVars false in
/-- **The base map of `Spf ∇ʸ : Spf (A{1/y}) → Spf (A ⊗̂_R A)` is a closed topological embedding.**
This is the `y`-piece of the mixed-chart preimage of the Tate diagonal. -/
theorem isClosedEmbedding_map_graphCodiagY (hI : I.FG) :
    IsClosedEmbedding
      (FormalSpectrum.map
        (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))
        (annulusOverlapIdealY R I q) (graphCodiagY R I q hI)
        (graphCodiagY_le_comap hI)) :=
  FormalSpectrum.isClosedEmbedding_map_of_surjective
    (idealOfDefinition R I (annulusAlgebra R I q) (annulusAlgebra R I q))
    (annulusOverlapIdealY R I q) (graphCodiagY R I q hI)
    (graphCodiagY_le_comap hI) (graphCodiagY_surjective hI)

end CompletedTensorProduct
