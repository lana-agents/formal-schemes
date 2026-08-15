import FormalSchemes.DiagonalClosedEmbedding

set_option linter.style.header false

/-!
# The right codiagonal `A ⊗̂_R C → C` and its closed-embedding formal spectrum

For a base adic ring `(R, I)` (with `I` finitely generated), a complete adic `R`-algebra `A` and a
complete adic `R`-algebra `C` equipped with an `R`-algebra map `f : A →ₐ[R] C`, the **right
codiagonal**

```
∇_f : A ⊗̂_R C →+* C,   inl a ↦ f a,   inr c ↦ c,
```

is the lift of the pair `(f, id_C)`. Like the ordinary codiagonal `∇ : A ⊗̂_R A →+* A`
(`CompletedTensorProduct.codiagonal`, the case `C = A`, `f = id`), it is **surjective** — it splits
the second canonical inclusion `inr : C → A ⊗̂_R C` — so its formal spectrum

```
Spf C ⟶ Spf (A ⊗̂_R C)
```

has a **closed topological embedding** as underlying continuous map
(`FormalSpectrum.isClosedEmbedding_map_of_surjective`).

This is the affine building block of the **off-diagonal** charts of the Tate self-product diagonal
(issue 411b / 424, EGA I §10.15): over each piece of the second-factor overlap
`Spf(A ⊗̂_R A{1/x}) ⨿ Spf(A ⊗̂_R A{1/y})` of the four-chart glue, the glued diagonal `Δ` restricts
to `Spf` of a right codiagonal `A ⊗̂_R A{1/x} → A{1/x}` (resp. `A ⊗̂_R A{1/y} → A{1/y}`), whose
second factor `C = A{1/x}` no longer coincides with the first factor `A`. The ordinary codiagonal
of `AffineSeparated`/`DiagonalClosedEmbedding` handles only the *diagonal* charts `(b, b)`.

## Main definitions and results

* `CompletedTensorProduct.rightCodiagonal`: the map `∇_f : A ⊗̂_R C →+* C`, `inl a ↦ f a`,
  `inr c ↦ c`.
* `CompletedTensorProduct.rightCodiagonal_surjective`: `∇_f` is surjective (it splits `inr`).
* `CompletedTensorProduct.map_rightCodiagonal_eq`: `∇_f` carries the ideal of definition of
  `A ⊗̂_R C` exactly onto that of `C` (`I·C`).
* `CompletedTensorProduct.isClosedEmbedding_map_rightCodiagonal`: the base map
  `Spf C → Spf (A ⊗̂_R C)` of `Spf ∇_f` is a closed topological embedding.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
-/

noncomputable section

open Ideal AlgebraicGeometry CategoryTheory FormalSpectrum Topology

universe u

namespace CompletedTensorProduct

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {A : Type u} [CommRing A] [Algebra R A]
variable {C : Type u} [CommRing C] [Algebra R C]
variable [TopologicalSpace R] [IsAdicRing I]
variable [TopologicalSpace A] [IsAdicRing (I.map (algebraMap R A))]
variable [TopologicalSpace C] [IsAdicRing (I.map (algebraMap R C))]

variable (R I A C) in
/-- The **right codiagonal** `∇_f : A ⊗̂_R C →+* C`, obtained as the lift of the pair `(f, id_C)`:
it sends `inl a ↦ f a` and `inr c ↦ c`. For `C = A` and `f = id` it is the ordinary codiagonal
`CompletedTensorProduct.codiagonal`. -/
def rightCodiagonal (f : A →ₐ[R] C) : CompletedTensorProduct R I A C →+* C :=
  haveI : IsAdicComplete (I.map (algebraMap R C)) C :=
    ‹IsAdicRing (I.map (algebraMap R C))›.toIsAdicComplete
  lift (I.map (algebraMap R C)) (le_refl _) f (AlgHom.id R C)

set_option linter.unusedSectionVars false in
@[simp]
theorem rightCodiagonal_inr (f : A →ₐ[R] C) (c : C) :
    rightCodiagonal R I A C f (inr R I A C c) = c := by
  haveI : IsAdicComplete (I.map (algebraMap R C)) C :=
    ‹IsAdicRing (I.map (algebraMap R C))›.toIsAdicComplete
  rw [rightCodiagonal, lift_inr, AlgHom.id_apply]

set_option linter.unusedSectionVars false in
@[simp]
theorem rightCodiagonal_inl (f : A →ₐ[R] C) (a : A) :
    rightCodiagonal R I A C f (inl R I A C a) = f a := by
  haveI : IsAdicComplete (I.map (algebraMap R C)) C :=
    ‹IsAdicRing (I.map (algebraMap R C))›.toIsAdicComplete
  rw [rightCodiagonal, lift_inl]

set_option linter.unusedSectionVars false in
/-- The right codiagonal `∇_f : A ⊗̂_R C →+* C` is **surjective**: it splits the canonical second
inclusion `inr : C → A ⊗̂_R C`. This is the ring-level input to `Spf ∇_f` being a closed
embedding. -/
theorem rightCodiagonal_surjective (f : A →ₐ[R] C) :
    Function.Surjective (rightCodiagonal R I A C f) :=
  fun c => ⟨inr R I A C c, rightCodiagonal_inr f c⟩

set_option linter.unusedSectionVars false in
/-- The right codiagonal is an `R`-algebra map: it sends `algebraMap R (A ⊗̂_R C)` to
`algebraMap R C`. -/
theorem rightCodiagonal_comp_algebraMap (f : A →ₐ[R] C) :
    (rightCodiagonal R I A C f).comp (algebraMap R (CompletedTensorProduct R I A C)) =
      algebraMap R C := by
  haveI : IsAdicComplete (I.map (algebraMap R C)) C :=
    ‹IsAdicRing (I.map (algebraMap R C))›.toIsAdicComplete
  ext r
  rw [RingHom.comp_apply, AdicCompletion.algebraMap_apply]
  unfold rightCodiagonal
  rw [lift_of]
  exact AlgHom.commutes _ r

variable [TopologicalSpace (CompletedTensorProduct R I A C)]
  [IsAdicRing (idealOfDefinition R I A C)]

set_option linter.unusedSectionVars false in
/-- The right codiagonal `∇_f` carries the ideal of definition of `A ⊗̂_R C` exactly onto that of
`C` (`I·C`); it is surjective, so the containment `rightCodiagonal_le_comap` is an equality. -/
theorem map_rightCodiagonal_eq (f : A →ₐ[R] C) :
    (idealOfDefinition R I A C).map (rightCodiagonal R I A C f) = I.map (algebraMap R C) := by
  rw [idealOfDefinition_eq_map, Ideal.map_map, rightCodiagonal_comp_algebraMap]

set_option linter.unusedSectionVars false in
/-- The right codiagonal `∇_f` carries the ideal of definition `idealOfDefinition R I A C` of
`A ⊗̂_R C` into the ideal of definition `I·C` of `C` — the continuity/adic-compatibility input
making `∇_f` induce a morphism of formal spectra. -/
theorem rightCodiagonal_le_comap (hI : I.FG) (f : A →ₐ[R] C) :
    idealOfDefinition R I A C ≤ (I.map (algebraMap R C)).comap (rightCodiagonal R I A C f) := by
  haveI : IsAdicComplete (I.map (algebraMap R C)) C :=
    ‹IsAdicRing (I.map (algebraMap R C))›.toIsAdicComplete
  exact lift_le_comap (le_refl _) f (AlgHom.id R C) hI

set_option linter.unusedSectionVars false in
/-- **The base map of `Spf ∇_f : Spf C → Spf (A ⊗̂_R C)` is a closed topological embedding.** The
right codiagonal `∇_f : A ⊗̂_R C →+* C` is surjective (`rightCodiagonal_surjective`), and `Spf`
(i.e. `Spec` of the level-`0` reduction) of a surjection is a closed embedding
(`FormalSpectrum.isClosedEmbedding_map_of_surjective`). This is the affine off-diagonal analogue of
`CompletedTensorProduct.isClosedEmbedding_diagonal_base`. -/
theorem isClosedEmbedding_map_rightCodiagonal (hI : I.FG) (f : A →ₐ[R] C) :
    IsClosedEmbedding
      (FormalSpectrum.map (idealOfDefinition R I A C) (I.map (algebraMap R C))
        (rightCodiagonal R I A C f) (rightCodiagonal_le_comap hI f)) :=
  FormalSpectrum.isClosedEmbedding_map_of_surjective (idealOfDefinition R I A C)
    (I.map (algebraMap R C)) (rightCodiagonal R I A C f) (rightCodiagonal_le_comap hI f)
    (rightCodiagonal_surjective f)

end CompletedTensorProduct
