import FormalSchemes.AffineFibreProduct

set_option linter.style.header false

/-!
# The diagonal of an affine formal spectrum

For a base adic ring `(R, I)` (with `I` finitely generated) and a complete adic `R`-algebra `A`
whose ideal of definition is the extension `I·A`, the affine fibre product `Spf (A ⊗̂_R A)` is the
product `Spf A ×_{Spf R} Spf A` (`FormalSchemes.AffineFibreProduct`, EGA I 10.7). This file packages
the **diagonal morphism**

```
Δ_{A/R} : Spf A ⟶ Spf (A ⊗̂_R A)
```

as the mediating morphism of that fibre product for the pair `(id_A, id_A)`. Its underlying ring
map is the codiagonal (multiplication) `A ⊗̂_R A → A`, `a ⊗ b ↦ a·b`. The two defining identities

```
Δ_{A/R} ≫ pr₁ = 𝟙 (Spf A)     and     Δ_{A/R} ≫ pr₂ = 𝟙 (Spf A)
```

exhibit `Δ_{A/R}` as a common section of both projections — the characteristic property of the
diagonal, and the affine input to the separatedness (diagonal) criterion of EGA I §10.15.

## Main definitions and results

* `CompletedTensorProduct.diagonal`: the diagonal morphism `Spf A ⟶ Spf (A ⊗̂_R A)`.
* `CompletedTensorProduct.diagonal_comp_pr₁`, `diagonal_comp_pr₂`: the diagonal is a section of both
  projections of the fibre product `Spf A ×_{Spf R} Spf A`.

**Scope.** This delivers the diagonal morphism and its two section identities — the affine content
that every affine formal spectrum `Spf A` is separated over `Spf R` (its diagonal is a monomorphism,
in fact a closed immersion, since the codiagonal `A ⊗̂_R A → A` is surjective). Upgrading the
diagonal to a *closed immersion of locally ringed spaces* needs the surjective-`c`-component /
sheaf-level closed-immersion infrastructure (the sheaf-level task also flagged for EGA I §10.14, cf.
issue 163's `c_iso` work); and the general separatedness of a non-affine `X ⟶ Y` needs the fibre
product of general formal schemes over the affine cover (`FormalScheme.OpenCover`, issue 191). Both
are recorded as follow-ups.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7, §10.15.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
-/

noncomputable section

open Ideal AlgebraicGeometry CategoryTheory FormalSpectrum

universe u

namespace CompletedTensorProduct

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {A : Type u} [CommRing A] [Algebra R A]
variable [TopologicalSpace R] [IsAdicRing I]
variable [TopologicalSpace A] [IsAdicRing (I.map (algebraMap R A))]
variable [TopologicalSpace (CompletedTensorProduct R I A A)]
  [IsAdicRing (idealOfDefinition R I A A)]

/-- The **diagonal morphism** `Δ_{A/R} : Spf A ⟶ Spf (A ⊗̂_R A)` of the affine fibre product
`Spf A ×_{Spf R} Spf A`, namely the mediating morphism `fibreLift` for the pair of identity
`R`-algebra maps `(id_A, id_A)`. Its underlying ring map is the codiagonal `A ⊗̂_R A → A`,
`a ⊗ b ↦ a·b`. The `IsAdicRing (idealOfDefinition R I A A)` instance is
`CompletedTensorProduct.isAdicRing hI` for `hI : I.FG`; supply it with `haveI` at the call site. -/
def diagonal (hI : I.FG) :
    locallyRingedSpaceObj (I.map (algebraMap R A)) ⟶
      locallyRingedSpaceObj (idealOfDefinition R I A A) :=
  fibreLift (le_refl _) (AlgHom.id R A) (AlgHom.id R A) hI

set_option linter.unusedSectionVars false in
/-- The diagonal is a **section of the first projection**: `Δ_{A/R} ≫ pr₁ = 𝟙 (Spf A)`. -/
theorem diagonal_comp_pr₁ (hI : I.FG) :
    diagonal (A := A) hI ≫ fibrePr₁ (R := R) (A := A) (B := A) =
      𝟙 (locallyRingedSpaceObj (I.map (algebraMap R A))) := by
  rw [diagonal, fibreLift_comp_pr₁]
  exact locallyRingedSpaceMap_id (I := I.map (algebraMap R A))

set_option linter.unusedSectionVars false in
/-- The diagonal is a **section of the second projection**: `Δ_{A/R} ≫ pr₂ = 𝟙 (Spf A)`. -/
theorem diagonal_comp_pr₂ (hI : I.FG) :
    diagonal (A := A) hI ≫ fibrePr₂ (R := R) (A := A) (B := A) =
      𝟙 (locallyRingedSpaceObj (I.map (algebraMap R A))) := by
  rw [diagonal, fibreLift_comp_pr₂]
  exact locallyRingedSpaceMap_id (I := I.map (algebraMap R A))

end CompletedTensorProduct
