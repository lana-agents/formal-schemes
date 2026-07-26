import FormalSchemes.AffineSeparated
import Mathlib.RingTheory.Spectrum.Prime.RingHom

set_option linter.style.header false

/-!
# The diagonal of an affine formal spectrum is a closed embedding

For a base adic ring `(R, I)` (with `I` finitely generated) and a complete adic `R`-algebra `A`
whose ideal of definition is the extension `I·A`, the affine diagonal
(`FormalSchemes.AffineDiagonal`)

```
Δ_{A/R} : Spf A ⟶ Spf (A ⊗̂_R A)
```

is `Spf` of the **codiagonal** (multiplication) map `∇ : A ⊗̂_R A →+* A`, which is *surjective*
(`FormalSchemes.AffineSeparated`, `CompletedTensorProduct.codiagonal_surjective`). This file
delivers the **topological `base_closed` half** of the statement that `Δ_{A/R}` is a closed
immersion (EGA I §10.15): its underlying continuous map is a *closed topological embedding*.

This is the separatedness criterion at the level of topological spaces — a formal spectrum is
separated over the base precisely when its diagonal is closed — and the diagonal-analogue of the
open embedding `FormalSpectrum.isOpenEmbedding_basicOpenChartBase` of the basic-open chart and of
the closed embedding `FormalSpectrum.isClosedEmbedding_closedSubschemeBase` of a closed formal
subscheme.

## Main results

* `FormalSpectrum.isClosedEmbedding_map_of_surjective`: `FormalSpectrum.map` of a **surjective**
  adic ring homomorphism is a closed topological embedding, with
  `FormalSpectrum.range_map_of_surjective` computing its range as a vanishing locus. This is the
  general topological content of a closed immersion of formal spectra; the `Ideal.Quotient.mk`
  case is `FormalSpectrum.isClosedEmbedding_closedSubschemeBase`.
* `CompletedTensorProduct.isClosedEmbedding_diagonal_base`: the underlying continuous map of the
  affine diagonal `Δ_{A/R}` is a closed topological embedding — the topological half of EGA I
  §10.15 separatedness — with `CompletedTensorProduct.range_diagonal_base` describing its range as
  the vanishing locus of the level-`0` reduction of the codiagonal's kernel.

**Scope.** This delivers the `base_closed` half only. Upgrading `Δ_{A/R}` to a genuine *closed
immersion of locally ringed spaces* (the full EGA I §10.15 statement) additionally needs the
surjective-`c`-component / sheaf-level closed-immersion infrastructure (the sheaf-level task also
flagged for EGA I §10.14, cf. issue 163's `c_iso` work), which `codiagonal_surjective` feeds; and
the general separatedness of a non-affine `X ⟶ Y` needs the fibre product of general formal schemes
over the affine cover (`FormalScheme.OpenCover`, issue 191). Both are recorded as follow-ups.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.14, §10.15.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
-/

noncomputable section

open Ideal AlgebraicGeometry CategoryTheory Topology FormalSpectrum

universe u

namespace FormalSpectrum

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] (I : Ideal R) (J : Ideal S)

/-- `FormalSpectrum.map` of a **surjective** ring homomorphism `φ : R →+* S` (carrying the ideal of
definition of `R` into that of `S`) is a **closed topological embedding** `Spf S → Spf R`: the
induced map of level-`0` thickenings `R ⧸ I → S ⧸ J` is surjective, and `Spec` of a surjection is a
closed embedding. This is the general topological content of a closed immersion of formal spectra
(EGA I §10.14); the special case `φ = Ideal.Quotient.mk a` is
`FormalSpectrum.isClosedEmbedding_closedSubschemeBase`. -/
theorem isClosedEmbedding_map_of_surjective (φ : R →+* S) (h : I ≤ J.comap φ)
    (hφ : Function.Surjective φ) :
    IsClosedEmbedding (map I J φ h) := by
  change IsClosedEmbedding (PrimeSpectrum.comap (Ideal.quotientMap J φ h))
  exact PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _
    (Ideal.quotientMap_surjective hφ)

/-- The **range** of `FormalSpectrum.map` of a surjective ring homomorphism `φ` is the vanishing
locus of the kernel of the induced level-`0` map `R ⧸ I → S ⧸ J`: the closed formal subscheme cut
out by `φ` is supported on that closed subset (EGA I §10.14). -/
theorem range_map_of_surjective (φ : R →+* S) (h : I ≤ J.comap φ)
    (hφ : Function.Surjective φ) :
    Set.range (map I J φ h) =
      (PrimeSpectrum.zeroLocus (RingHom.ker (Ideal.quotientMap J φ h)) :
        Set (FormalSpectrum I)) := by
  change Set.range (PrimeSpectrum.comap (Ideal.quotientMap J φ h)) = _
  rw [range_comap_of_surjective _ _ (Ideal.quotientMap_surjective hφ)]

end FormalSpectrum

namespace CompletedTensorProduct

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {A : Type u} [CommRing A] [Algebra R A]
variable [TopologicalSpace R] [IsAdicRing I]
variable [TopologicalSpace A] [IsAdicRing (I.map (algebraMap R A))]
variable [TopologicalSpace (CompletedTensorProduct R I A A)]
  [IsAdicRing (idealOfDefinition R I A A)]

set_option linter.unusedSectionVars false in
/-- The codiagonal `∇ : A ⊗̂_R A →+* A` carries the ideal of definition `idealOfDefinition R I A A`
of `A ⊗̂_R A` into the ideal of definition `I·A` of `A` — the continuity/adic-compatibility input
making `∇` induce a morphism of formal spectra. It is `CompletedTensorProduct.lift_le_comap`
specialised to the pair `(id_A, id_A)` (recall `∇ = lift (id_A, id_A)`). -/
theorem codiagonal_le_comap (hI : I.FG) :
    idealOfDefinition R I A A ≤ (I.map (algebraMap R A)).comap (codiagonal R I A) := by
  haveI : IsAdicComplete (I.map (algebraMap R A)) A :=
    ‹IsAdicRing (I.map (algebraMap R A))›.toIsAdicComplete
  exact lift_le_comap (le_refl _) (AlgHom.id R A) (AlgHom.id R A) hI

/-- The affine diagonal `Δ_{A/R} : Spf A ⟶ Spf (A ⊗̂_R A)` is, on underlying continuous maps,
`FormalSpectrum.map` of the codiagonal `∇`. -/
theorem diagonal_base_eq (hI : I.FG) :
    ⇑(diagonal (A := A) hI).base =
      FormalSpectrum.map (idealOfDefinition R I A A) (I.map (algebraMap R A)) (codiagonal R I A)
        (codiagonal_le_comap hI) :=
  rfl

/-- The underlying continuous map of the affine diagonal `Δ_{A/R} : Spf A ⟶ Spf (A ⊗̂_R A)` is a
**closed topological embedding** (EGA I §10.15): `Spf A` maps homeomorphically onto a closed subset
of `Spf (A ⊗̂_R A)`. This is the topological `base_closed` half of "`Δ_{A/R}` is a closed
immersion", i.e. the statement that the affine formal spectrum `Spf A` is separated over `Spf R`;
it follows
from the surjectivity of the codiagonal `∇` (`codiagonal_surjective`). -/
theorem isClosedEmbedding_diagonal_base (hI : I.FG) :
    IsClosedEmbedding ⇑(diagonal (A := A) hI).base := by
  rw [diagonal_base_eq hI]
  exact isClosedEmbedding_map_of_surjective (idealOfDefinition R I A A) (I.map (algebraMap R A))
    (codiagonal R I A) (codiagonal_le_comap hI) codiagonal_surjective

/-- The **range** of the diagonal's base map is the vanishing locus of the kernel of the level-`0`
reduction of the codiagonal: the image of `Δ_{A/R}` is the closed "diagonal locus" in
`Spf (A ⊗̂_R A)` (EGA I §10.15). -/
theorem range_diagonal_base (hI : I.FG) :
    Set.range ⇑(diagonal (A := A) hI).base =
      (PrimeSpectrum.zeroLocus (RingHom.ker (Ideal.quotientMap (I.map (algebraMap R A))
        (codiagonal R I A) (codiagonal_le_comap hI))) :
          Set (FormalSpectrum (idealOfDefinition R I A A))) := by
  rw [diagonal_base_eq hI]
  exact range_map_of_surjective (idealOfDefinition R I A A) (I.map (algebraMap R A))
    (codiagonal R I A) (codiagonal_le_comap hI) codiagonal_surjective

end CompletedTensorProduct
