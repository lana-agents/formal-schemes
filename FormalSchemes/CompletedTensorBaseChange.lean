import FormalSchemes.ClosedImmersionAffine

set_option linter.style.header false

/-!
# The completed tensor product under a change of base ring

For a tower `R → R'` of commutative rings and two algebras `A`, `B` over both, compatibly, the
completed tensor products `A ⊗̂_R B` and `A ⊗̂_{R'} B` are taken over *different* bases. This file
builds the comparison between them and identifies what it is geometrically.

The uncompleted comparison `A ⊗[R] B →ₐ[R] A ⊗[R'] B` is the tensor-product lift of the two
inclusions, and it is **surjective** — `A ⊗[R'] B` is the quotient of `A ⊗[R] B` that imposes
`r'·a ⊗ b = a ⊗ r'·b`. Its completion is `CompletedTensorProduct.baseChangeHom`, and the two ideals
of definition match **on the nose exactly when `I'` is the extension `I·R'`**: the source ideal is
`I·(A ⊗ B)` and its image is `I·(A ⊗' B)`, which is `I'·(A ⊗' B)` for that `I'` and for no other.
That single hypothesis is what the whole file runs on, and it is not a convenience — it is the
hypothesis that the general-base continuity question (`FormalSchemes.AdicOnSections`, and the
account in `FormalSchemes.AwayCompletionUniversal`) refutes for an arbitrary `I'`.

With the ideal of definition carried **onto** the ideal of definition, the completed comparison
meets `FormalSpectrum.isClosedEmbedding_base_and_surjective_stalkMap_of_surjective`
(`FormalSchemes.ClosedImmersionSections`) with nothing left to discharge, so

```
Spf (A ⊗̂_{R'} B) ⟶ Spf (A ⊗̂_R B)
```

is a closed immersion of formal schemes. This is the affine shadow of the classical reason
separatedness cancels on the left: `X ×_{Spf R'} X` sits inside `X ×_{Spf R} X` as a closed
subscheme, so a closed diagonal over `R` restricts to a closed diagonal over `R'`.

## Main definitions and results

* `CompletedTensorProduct.tensorBaseChangeHom`: the uncompleted comparison
  `A ⊗[R] B →ₐ[R] A ⊗[R'] B`, with `CompletedTensorProduct.tensorBaseChangeHom_tmul` computing it
  on pure tensors and `CompletedTensorProduct.tensorBaseChangeHom_surjective`.
* `CompletedTensorProduct.map_tensorBaseChangeHom`: the extension of `I` to `A ⊗[R] B` is carried
  **onto** the extension of `I'` to `A ⊗[R'] B`, for `I' = I·R'`.
* `CompletedTensorProduct.baseChangeHom`: the comparison `A ⊗̂_R B →+* A ⊗̂_{R'} B`, with
  `CompletedTensorProduct.baseChangeHom_surjective` and `CompletedTensorProduct.map_baseChangeHom`
  (ideal of definition onto ideal of definition), and
  `CompletedTensorProduct.baseChangeHom_inl` / `CompletedTensorProduct.baseChangeHom_inr`: it
  commutes with both factor inclusions.
* `CompletedTensorProduct.schemeBaseChange`: the induced morphism of formal schemes
  `Spf (A ⊗̂_{R'} B) ⟶ Spf (A ⊗̂_R B)`, and
  `CompletedTensorProduct.schemeBaseChange_isClosedImmersion`: it is a closed immersion.

## What is not proved here

* **Nothing glued.** The comparison here is between two *affine* completed tensor products. The
  charts of a general fibre product `AlgebraicGeometry.BothChartedFibreDatum.generalFibreProduct`
  (`FormalSchemes.GeneralFibreProductBothObject`) are of exactly this shape, one per ordered pair
  of charts, but assembling these affine comparisons into a morphism of glued formal schemes needs
  them to commute with the datum's transitions, and that is not done here.
* **No cancellation.** Nothing here says a closed diagonal over `R` gives a closed diagonal over
  `R'`. That needs the glued comparison above, and is then topological rather than algebraic:
  separatedness is closedness of the diagonal's range
  (`AlgebraicGeometry.BothChartedFibreDatumXY.isSeparated_iff_isClosed_range_diagonal_base`,
  `FormalSchemes.GeneralSeparatedRange`), and the range of a map is the preimage of the range of
  its composite with an injection.
* **The general base is not available and is not an oversight.** Every statement below carries
  `I.map (algebraMap R R') = I'`. Dropping it breaks `CompletedTensorProduct.map_baseChangeHom`,
  and with it the closed immersion; the containment `I' ≤ (I·A).comap` that a general base would
  need is refuted on this tree (`FormalSchemes.AdicOnSections`, witness
  `FormalSpectrum.cofinalSpfIso`).

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7, §10.15.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
* [The Stacks Project, Tag 01HJ](https://stacks.math.columbia.edu/tag/01HJ).
-/

noncomputable section

open Ideal TensorProduct CategoryTheory AlgebraicGeometry Topology

universe u

namespace CompletedTensorProduct

variable {R R' A B : Type u} [CommRing R] [CommRing R'] [CommRing A] [CommRing B]
variable [Algebra R R'] [Algebra R A] [Algebra R B] [Algebra R' A] [Algebra R' B]
variable [IsScalarTower R R' A] [IsScalarTower R R' B]

/-! ### The uncompleted comparison -/

/-- **The base-change comparison of the underlying tensor products**, `A ⊗[R] B →ₐ[R] A ⊗[R'] B`:
the lift of the two inclusions of `A ⊗[R'] B`, read as `R`-algebra maps through the towers. -/
def tensorBaseChangeHom : A ⊗[R] B →ₐ[R] A ⊗[R'] B :=
  Algebra.TensorProduct.lift
    ((Algebra.TensorProduct.includeLeft : A →ₐ[R'] A ⊗[R'] B).restrictScalars R)
    ((Algebra.TensorProduct.includeRight : B →ₐ[R'] A ⊗[R'] B).restrictScalars R)
    (fun _ _ => Commute.all _ _)

@[simp]
theorem tensorBaseChangeHom_tmul (a : A) (b : B) :
    tensorBaseChangeHom (R := R) (R' := R') (a ⊗ₜ[R] b) = a ⊗ₜ[R'] b := by
  simp [tensorBaseChangeHom]

/-- **The uncompleted comparison is surjective**: `A ⊗[R'] B` is generated as an additive group by
the pure tensors, and every pure tensor is hit by the pure tensor with the same entries. -/
theorem tensorBaseChangeHom_surjective :
    Function.Surjective (tensorBaseChangeHom (R := R) (R' := R') (A := A) (B := B)) := by
  intro x
  induction x with
  | zero => exact ⟨0, map_zero _⟩
  | tmul a b => exact ⟨a ⊗ₜ[R] b, tensorBaseChangeHom_tmul a b⟩
  | add x y hx hy =>
      obtain ⟨u, rfl⟩ := hx
      obtain ⟨v, rfl⟩ := hy
      exact ⟨u + v, map_add _ _ _⟩

variable {I : Ideal R} {I' : Ideal R'}

/-- The comparison is a map under `R`, so the extension of `I` to `A ⊗[R] B` is carried to the
extension of `I` to `A ⊗[R'] B` — which is the extension of `I' = I·R'` along the tower. This is
the computation the whole file turns on, and it is an **equality**, not a containment. -/
theorem map_tensorBaseChangeHom (hII' : I.map (algebraMap R R') = I') :
    (I.map (algebraMap R (A ⊗[R] B))).map
        (tensorBaseChangeHom (R := R) (R' := R') (A := A) (B := B)).toRingHom =
      I'.map (algebraMap R' (A ⊗[R'] B)) := by
  rw [Ideal.map_map]
  have h : ((tensorBaseChangeHom (R := R) (R' := R') (A := A) (B := B)).toRingHom).comp
      (algebraMap R (A ⊗[R] B)) = algebraMap R (A ⊗[R'] B) :=
    RingHom.ext fun r => (tensorBaseChangeHom (R := R) (R' := R')).commutes r
  rw [h, ← hII', Ideal.map_map, ← IsScalarTower.algebraMap_eq R R' (A ⊗[R'] B)]

/-- `I'` is finitely generated whenever `I` is, since it is the extension of `I`. -/
theorem fg_of_map_eq (hI : I.FG) (hII' : I.map (algebraMap R R') = I') : I'.FG :=
  hII' ▸ hI.map (algebraMap R R')

/-! ### The completed comparison -/

/-- **The base-change comparison of completed tensor products**, `A ⊗̂_R B →+* A ⊗̂_{R'} B`: the
completion of `CompletedTensorProduct.tensorBaseChangeHom`, which carries the ideal of definition
of the source to that of the target by `CompletedTensorProduct.map_tensorBaseChangeHom`. -/
def baseChangeHom (hI : I.FG) (hII' : I.map (algebraMap R R') = I') :
    CompletedTensorProduct R I A B →+* CompletedTensorProduct R' I' A B :=
  AdicCompletion.mapCompletion
    (tensorBaseChangeHom (R := R) (R' := R') (A := A) (B := B)).toRingHom
    (le_of_eq (map_tensorBaseChangeHom hII'))
    ((fg_of_map_eq hI hII').map (algebraMap R' (A ⊗[R'] B)))

/-- **The completed comparison is surjective.** Both completions are complete adic rings, the
uncompleted map is surjective, and it carries the one ideal of definition exactly onto the other,
which is what `AdicCompletion.mapCompletion_surjective` asks for. -/
theorem baseChangeHom_surjective (hI : I.FG) (hII' : I.map (algebraMap R R') = I') :
    Function.Surjective (baseChangeHom (A := A) (B := B) hI hII') :=
  AdicCompletion.mapCompletion_surjective (hI.map _)
    ((fg_of_map_eq hI hII').map _) _ tensorBaseChangeHom_surjective
    (map_tensorBaseChangeHom hII')

/-- **The comparison carries the ideal of definition onto the ideal of definition.** Together with
surjectivity this is the whole input of the closed-immersion criterion; a containment would not
do. -/
theorem map_baseChangeHom (hI : I.FG) (hII' : I.map (algebraMap R R') = I') :
    (idealOfDefinition R I A B).map (baseChangeHom (A := A) (B := B) hI hII') =
      idealOfDefinition R' I' A B := by
  unfold baseChangeHom idealOfDefinition
  rw [Ideal.map_map, AdicCompletion.mapCompletion_comp_algebraMap, ← Ideal.map_map,
    map_tensorBaseChangeHom hII']

/-- The comparison is an adic ring homomorphism: it carries the ideal of definition into the ideal
of definition, which is the form `FormalSpectrum.map` consumes. -/
theorem le_comap_baseChangeHom (hI : I.FG) (hII' : I.map (algebraMap R R') = I') :
    idealOfDefinition R I A B ≤
      (idealOfDefinition R' I' A B).comap (baseChangeHom (A := A) (B := B) hI hII') :=
  Ideal.le_comap_of_map_le (le_of_eq (map_baseChangeHom hI hII'))

/-- **The comparison commutes with the inclusion of the first factor.** Both sides are the image of
the pure tensor `a ⊗ₜ 1` in their respective completions, and `CompletedTensorProduct.inl` factors
through `algebraMap`, so `AdicCompletion.mapCompletion_algebraMap` together with
`CompletedTensorProduct.tensorBaseChangeHom_tmul` is the whole content. -/
theorem baseChangeHom_inl (hI : I.FG) (hII' : I.map (algebraMap R R') = I') (a : A) :
    baseChangeHom (A := A) (B := B) hI hII' (inl R I A B a) = inl R' I' A B a := by
  unfold baseChangeHom inl
  simp [AdicCompletion.mapCompletion_algebraMap]

/-- **The comparison commutes with the inclusion of the second factor**, by the same computation as
`CompletedTensorProduct.baseChangeHom_inl` on the other side of the tensor. -/
theorem baseChangeHom_inr (hI : I.FG) (hII' : I.map (algebraMap R R') = I') (b : B) :
    baseChangeHom (A := A) (B := B) hI hII' (inr R I A B b) = inr R' I' A B b := by
  unfold baseChangeHom inr
  simp [AdicCompletion.mapCompletion_algebraMap]

/-! ### The comparison of formal spectra -/

/-- **`Spf` of the comparison is a closed immersion**, in the two-part conjunction of
`FormalSchemes.ClosedImmersionSections`: the base map is a closed topological embedding and every
stalk map is surjective. Nothing is left to discharge — the criterion asks for a surjection
carrying the ideal of definition onto the ideal of definition, and that is
`CompletedTensorProduct.baseChangeHom_surjective` together with
`CompletedTensorProduct.map_baseChangeHom`. -/
theorem isClosedEmbedding_base_and_surjective_stalkMap_baseChange
    (hI : I.FG) (hII' : I.map (algebraMap R R') = I') :
    IsClosedEmbedding (FormalSpectrum.map (idealOfDefinition R I A B)
        (idealOfDefinition R' I' A B) (baseChangeHom (A := A) (B := B) hI hII')
        (le_comap_baseChangeHom hI hII')) ∧
      ∀ y, Function.Surjective ((FormalSpectrum.presheafedSpaceMap (idealOfDefinition R I A B)
        (idealOfDefinition R' I' A B) (baseChangeHom (A := A) (B := B) hI hII')
        (le_comap_baseChangeHom hI hII')).stalkMap y).hom :=
  FormalSpectrum.isClosedEmbedding_base_and_surjective_stalkMap_of_surjective _ _ _ _
    (idealOfDefinition_fg R I A B hI) (baseChangeHom_surjective hI hII')
    (map_baseChangeHom hI hII')

section Scheme

variable [TopologicalSpace R] [IsAdicRing I]
variable [TopologicalSpace A] [IsAdicRing (I.map (algebraMap R A))]
variable [TopologicalSpace B] [IsAdicRing (I.map (algebraMap R B))]
variable [TopologicalSpace (CompletedTensorProduct R I A B)]
  [IsAdicRing (idealOfDefinition R I A B)]
variable [TopologicalSpace (CompletedTensorProduct R' I' A B)]
  [IsAdicRing (idealOfDefinition R' I' A B)]

/-- **The base-change comparison as a morphism of formal schemes**,
`Spf (A ⊗̂_{R'} B) ⟶ Spf (A ⊗̂_R B)`. -/
def schemeBaseChange (hI : I.FG) (hII' : I.map (algebraMap R R') = I') :
    FormalScheme.Spf (idealOfDefinition R' I' A B) ⟶ schemeFibreProduct R I A B :=
  schemeSpfMap (baseChangeHom (A := A) (B := B) hI hII') (le_comap_baseChangeHom hI hII')

/-- **The base-change comparison of affine fibre products is a closed immersion of formal
schemes.** This is the affine shadow of left-cancellation for separatedness: `X ×_{Spf R'} X` is a
closed subscheme of `X ×_{Spf R} X`, at the level of a single pair of charts. -/
theorem schemeBaseChange_isClosedImmersion (hI : I.FG) (hII' : I.map (algebraMap R R') = I') :
    FormalScheme.IsClosedImmersion (schemeBaseChange (A := A) (B := B) hI hII') where
  base_closedEmbedding := (isClosedEmbedding_base_and_surjective_stalkMap_baseChange hI hII').1
  surjective_stalkMap := (isClosedEmbedding_base_and_surjective_stalkMap_baseChange hI hII').2

end Scheme

end CompletedTensorProduct

end
