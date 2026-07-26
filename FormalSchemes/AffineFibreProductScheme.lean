import FormalSchemes.AffineFibreProductUniqueness
import FormalSchemes.AffineDiagonal
import FormalSchemes.FormalScheme

set_option linter.style.header false

/-!
# The affine fibre product as an object of the category of formal schemes

The affine fibre product `Spf (A ⊗̂_R B) ≅ Spf A ×_{Spf R} Spf B` (EGA I, 10.7) was constructed in
`FormalSchemes.AffineFibreProduct` / `AffineFibreProductUniqueness` (issue 202) at the level of
**locally ringed spaces** — as `FormalSpectrum.locallyRingedSpaceObj` together with the projections
`fibrePr₁`, `fibrePr₂`, the structural morphism `fibreStructMap`, the mediating morphism `fibreLift`
and its uniqueness `fibreLift_unique`. This file repackages that data one level up, in the category
`AlgebraicGeometry.FormalScheme` itself: the object is the affine formal scheme
`FormalScheme.Spf (A ⊗̂_R B)` and the projections/structural morphism/mediating morphism are the
corresponding `FormalScheme.Hom`s.

This is the form the **general (glued) fibre product** of formal schemes (issue 227) consumes: the
charts of `X ×_S Y` are the affine products `Spf (A_i ⊗̂_{R_k} B_j)` living in `FormalScheme`, so a
`FormalScheme.GlueData` needs the affine product and its projection cone as morphisms of formal
schemes, not merely of locally ringed spaces. It also delivers the affine case of §10.15
separatedness *at the categorical level*: the diagonal `Spf A ⟶ Spf (A ⊗̂_R A)` is a split
monomorphism in `FormalScheme`, so `Spf A` is separated over `Spf R`.

The repackaging is transparent because `FormalScheme` is a *full* subcategory of
`LocallyRingedSpace` (`FormalScheme.forgetToLocallyRingedSpace` is full and faithful) and
`(FormalScheme.Spf J).toLocallyRingedSpace` is definitionally
`FormalSpectrum.locallyRingedSpaceObj J` — so `FormalScheme.Hom.mk` wraps each
locally-ringed-space morphism directly and every identity
reduces, via `FormalScheme.Hom.ext'`, to its already-established locally-ringed-space counterpart.

## Main definitions and results

* `CompletedTensorProduct.schemeFibreProduct`: the affine fibre product `Spf (A ⊗̂_R B)` as a
  `FormalScheme`.
* `CompletedTensorProduct.schemePr₁`, `schemePr₂`, `schemeStructMap`: the two projections
  `⟶ Spf A`, `⟶ Spf B` and the structural morphism `⟶ Spf R`, as morphisms of formal schemes.
* `CompletedTensorProduct.scheme_cone_comm`: the fibre-product square commutes over `Spf R`.
* `CompletedTensorProduct.schemeFibreLift`, `schemeFibreLift_comp_pr₁`, `schemeFibreLift_comp_pr₂`,
  `schemeFibreLift_unique`: the mediating morphism from an affine target and its universal property
  (existence, factorisation, and uniqueness among `Spf`-of-ring-map morphisms — the regime available
  before the Spf–Γ adjunction, exactly as at the locally-ringed-space level).
* `CompletedTensorProduct.schemeDiagonal`, `isSplitMono_schemeDiagonal`, `mono_schemeDiagonal`: the
  affine diagonal `Δ_{A/R} : Spf A ⟶ Spf (A ⊗̂_R A)` in `FormalScheme` is a split mono, hence a
  mono; i.e. `Spf A` is separated over `Spf R` (EGA I §10.15, affine case, categorical level).

**Scope.** As at the locally-ringed-space level (`AffineFibreProduct`), full uniqueness of the
mediating morphism *among arbitrary morphisms of formal schemes* requires recognising an arbitrary
morphism into `Spf (A ⊗̂_R B)` as `Spf` of a ring homomorphism (the Spf–Γ correspondence, issue 96);
uniqueness among `Spf`-of-ring-map morphisms is delivered here. The **general** fibre product of
non-affine formal schemes — gluing these affine charts over an affine cover of the base — remains
the open goal of issue 227.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7, §10.15.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
-/

noncomputable section

open Ideal AlgebraicGeometry CategoryTheory FormalSpectrum

universe u

namespace CompletedTensorProduct

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
variable [TopologicalSpace R] [IsAdicRing I]
variable [TopologicalSpace A] [IsAdicRing (I.map (algebraMap R A))]
variable [TopologicalSpace B] [IsAdicRing (I.map (algebraMap R B))]
variable [TopologicalSpace (CompletedTensorProduct R I A B)]
  [IsAdicRing (idealOfDefinition R I A B)]

/-- The **affine fibre product** `Spf (A ⊗̂_R B)`, as an object of the category of formal schemes.
Its underlying locally ringed space is `FormalSpectrum.locallyRingedSpaceObj (idealOfDefinition …)`,
the object of `FormalSchemes.AffineFibreProduct`. The `IsAdicRing (idealOfDefinition R I A B)` and
`TopologicalSpace (CompletedTensorProduct R I A B)` instances are
`CompletedTensorProduct.isAdicRing hI` / the adic topology, for `hI : I.FG`. -/
def schemeFibreProduct (R : Type u) [CommRing R] (I : Ideal R) (A B : Type u)
    [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [TopologicalSpace R] [IsAdicRing I]
    [TopologicalSpace A] [IsAdicRing (I.map (algebraMap R A))]
    [TopologicalSpace B] [IsAdicRing (I.map (algebraMap R B))]
    [TopologicalSpace (CompletedTensorProduct R I A B)]
    [IsAdicRing (idealOfDefinition R I A B)] : FormalScheme.{u} :=
  FormalScheme.Spf (idealOfDefinition R I A B)

/-- The **first projection** `Spf (A ⊗̂_R B) ⟶ Spf A` of the affine fibre product, as a morphism of
formal schemes. -/
def schemePr₁ :
    schemeFibreProduct R I A B ⟶ FormalScheme.Spf (I.map (algebraMap R A)) :=
  FormalScheme.Hom.mk fibrePr₁

/-- The **second projection** `Spf (A ⊗̂_R B) ⟶ Spf B` of the affine fibre product, as a morphism of
formal schemes. -/
def schemePr₂ :
    schemeFibreProduct R I A B ⟶ FormalScheme.Spf (I.map (algebraMap R B)) :=
  FormalScheme.Hom.mk fibrePr₂

/-- The **structural morphism** `Spf (A ⊗̂_R B) ⟶ Spf R` of the affine fibre product, as a morphism
of formal schemes. -/
def schemeStructMap :
    schemeFibreProduct R I A B ⟶ FormalScheme.Spf I :=
  FormalScheme.Hom.mk fibreStructMap

/-- The structural morphism `Spf A ⟶ Spf R` of the first factor, as a morphism of formal schemes. -/
def schemeStructMapₗ :
    FormalScheme.Spf (I.map (algebraMap R A)) ⟶ FormalScheme.Spf I :=
  FormalScheme.Hom.mk (IsAdicHom.of_map I (A := A)).spfMap

/-- The structural morphism `Spf B ⟶ Spf R` of the second factor, as a formal-scheme morphism. -/
def schemeStructMapᵣ :
    FormalScheme.Spf (I.map (algebraMap R B)) ⟶ FormalScheme.Spf I :=
  FormalScheme.Hom.mk (IsAdicHom.of_map I (A := B)).spfMap

set_option linter.unusedSectionVars false in
/-- The fibre-product square commutes over `Spf R` on the first factor. -/
theorem schemePr₁_comp_structMap :
    schemePr₁ (R := R) (I := I) (A := A) (B := B) ≫ schemeStructMapₗ =
      schemeStructMap (R := R) (I := I) (A := A) (B := B) := by
  apply FormalScheme.Hom.ext'
  exact fibrePr₁_comp_structMap

set_option linter.unusedSectionVars false in
/-- The fibre-product square commutes over `Spf R` on the second factor. -/
theorem schemePr₂_comp_structMap :
    schemePr₂ (R := R) (I := I) (A := A) (B := B) ≫ schemeStructMapᵣ =
      schemeStructMap (R := R) (I := I) (A := A) (B := B) := by
  apply FormalScheme.Hom.ext'
  exact fibrePr₂_comp_structMap

set_option linter.unusedSectionVars false in
/-- **The fibre-product square commutes**: the two projections agree over `Spf R`, as morphisms of
formal schemes. -/
theorem scheme_cone_comm :
    schemePr₁ (R := R) (I := I) (A := A) (B := B) ≫ schemeStructMapₗ =
      schemePr₂ (R := R) (I := I) (A := A) (B := B) ≫ schemeStructMapᵣ := by
  rw [schemePr₁_comp_structMap, schemePr₂_comp_structMap]

section Lift

variable {S : Type u} [CommRing S] [Algebra R S] [TopologicalSpace S] {L : Ideal S} [IsAdicRing L]
variable (hIL : I.map (algebraMap R S) ≤ L) (f : A →ₐ[R] S) (g : B →ₐ[R] S)

/-- The **mediating morphism** `Spf S ⟶ Spf (A ⊗̂_R B)` of the fibre-product universal property,
induced by a pair of `R`-algebra maps `f : A →ₐ[R] S`, `g : B →ₐ[R] S` into a complete adic
`R`-algebra `S`, as a morphism of formal schemes. -/
def schemeFibreLift (hI : I.FG) :
    FormalScheme.Spf L ⟶ schemeFibreProduct R I A B :=
  FormalScheme.Hom.mk (fibreLift hIL f g hI)

set_option linter.unusedSectionVars false in
/-- The mediating morphism recovers `f` after the first projection. -/
theorem schemeFibreLift_comp_pr₁ (hI : I.FG) :
    schemeFibreLift hIL f g hI ≫ schemePr₁ =
      FormalScheme.Hom.mk
        (locallyRingedSpaceMap (I.map (algebraMap R A)) L f.toRingHom (algHom_le_comap f hIL)) := by
  apply FormalScheme.Hom.ext'
  exact fibreLift_comp_pr₁ hIL f g hI

set_option linter.unusedSectionVars false in
/-- The mediating morphism recovers `g` after the second projection. -/
theorem schemeFibreLift_comp_pr₂ (hI : I.FG) :
    schemeFibreLift hIL f g hI ≫ schemePr₂ =
      FormalScheme.Hom.mk
        (locallyRingedSpaceMap (I.map (algebraMap R B)) L g.toRingHom (algHom_le_comap g hIL)) := by
  apply FormalScheme.Hom.ext'
  exact fibreLift_comp_pr₂ hIL f g hI

end Lift

/-- `Spf φ : Spf S ⟶ Spf (A ⊗̂_R B)` as a morphism of formal schemes, for an adic ring homomorphism
`φ : A ⊗̂_R B →+* S` carrying the ideal of definition into `L`. -/
def schemeSpfMap {S : Type u} [CommRing S] [TopologicalSpace S] {L : Ideal S} [IsAdicRing L]
    (φ : CompletedTensorProduct R I A B →+* S) (h : idealOfDefinition R I A B ≤ L.comap φ) :
    FormalScheme.Spf L ⟶ schemeFibreProduct R I A B :=
  FormalScheme.Hom.mk (locallyRingedSpaceMap (idealOfDefinition R I A B) L φ h)

set_option linter.unusedSectionVars false in
/-- **Uniqueness of the mediating morphism, among `Spf`-of-ring-map morphisms of formal schemes**
(the uniqueness half of the affine fibre-product universal property, EGA I 10.7, in the category of
formal schemes). Two morphisms `Spf φ₁`, `Spf φ₂ : Spf S ⟶ Spf (A ⊗̂_R B)` induced by adic ring
homomorphisms `φ₁, φ₂` that agree after both projections `schemePr₁`, `schemePr₂` are equal. Full
uniqueness among arbitrary morphisms additionally requires the Spf–Γ adjunction (issue 96), exactly
as at the locally-ringed-space level (`fibreLift_unique`). -/
theorem schemeFibreLift_unique {S : Type u} [CommRing S] [TopologicalSpace S] {L : Ideal S}
    [IsAdicRing L] (hI : I.FG) (φ₁ φ₂ : CompletedTensorProduct R I A B →+* S)
    (h₁ : idealOfDefinition R I A B ≤ L.comap φ₁) (h₂ : idealOfDefinition R I A B ≤ L.comap φ₂)
    (hpr₁ : schemeSpfMap φ₁ h₁ ≫ schemePr₁ = schemeSpfMap φ₂ h₂ ≫ schemePr₁)
    (hpr₂ : schemeSpfMap φ₁ h₁ ≫ schemePr₂ = schemeSpfMap φ₂ h₂ ≫ schemePr₂) :
    schemeSpfMap φ₁ h₁ = schemeSpfMap φ₂ h₂ := by
  apply FormalScheme.Hom.ext'
  refine fibreLift_unique hI φ₁ φ₂ h₁ h₂ ?_ ?_
  · exact congrArg FormalScheme.Hom.toLRSHom hpr₁
  · exact congrArg FormalScheme.Hom.toLRSHom hpr₂

end CompletedTensorProduct

/-!
### The diagonal and affine separatedness in the category of formal schemes
-/

namespace CompletedTensorProduct

variable {R : Type u} [CommRing R] {I : Ideal R}
variable {A : Type u} [CommRing A] [Algebra R A]
variable [TopologicalSpace R] [IsAdicRing I]
variable [TopologicalSpace A] [IsAdicRing (I.map (algebraMap R A))]
variable [TopologicalSpace (CompletedTensorProduct R I A A)]
  [IsAdicRing (idealOfDefinition R I A A)]

/-- The **diagonal morphism** `Δ_{A/R} : Spf A ⟶ Spf (A ⊗̂_R A)` of the affine fibre product
`Spf A ×_{Spf R} Spf A`, as a morphism of formal schemes: the mediating morphism for the pair of
identity `R`-algebra maps. -/
def schemeDiagonal (hI : I.FG) :
    FormalScheme.Spf (I.map (algebraMap R A)) ⟶ schemeFibreProduct R I A A :=
  FormalScheme.Hom.mk (diagonal hI)

set_option linter.unusedSectionVars false in
/-- The diagonal is a **section of the first projection** in `FormalScheme`. -/
theorem schemeDiagonal_comp_pr₁ (hI : I.FG) :
    schemeDiagonal (R := R) (I := I) (A := A) hI ≫ schemePr₁ (R := R) (I := I) (A := A) (B := A) =
      𝟙 (FormalScheme.Spf (I.map (algebraMap R A))) := by
  apply FormalScheme.Hom.ext'
  exact diagonal_comp_pr₁ hI

set_option linter.unusedSectionVars false in
/-- The diagonal is a **section of the second projection** in `FormalScheme`. -/
theorem schemeDiagonal_comp_pr₂ (hI : I.FG) :
    schemeDiagonal (R := R) (I := I) (A := A) hI ≫ schemePr₂ (R := R) (I := I) (A := A) (B := A) =
      𝟙 (FormalScheme.Spf (I.map (algebraMap R A))) := by
  apply FormalScheme.Hom.ext'
  exact diagonal_comp_pr₂ hI

set_option linter.unusedSectionVars false in
/-- **The affine diagonal is a split monomorphism** in the category of formal schemes: the first
projection is a retraction. -/
theorem isSplitMono_schemeDiagonal (hI : I.FG) :
    IsSplitMono (schemeDiagonal (R := R) (I := I) (A := A) hI) :=
  IsSplitMono.mk' ⟨schemePr₁ (R := R) (I := I) (A := A) (B := A), schemeDiagonal_comp_pr₁ hI⟩

set_option linter.unusedSectionVars false in
/-- **`Spf A` is separated over `Spf R`** (EGA I §10.15, affine case, categorical level): the
diagonal `Δ_{A/R}` is a monomorphism in the category of formal schemes. -/
theorem mono_schemeDiagonal (hI : I.FG) : Mono (schemeDiagonal (R := R) (I := I) (A := A) hI) :=
  haveI := isSplitMono_schemeDiagonal (R := R) (I := I) (A := A) hI
  inferInstance

end CompletedTensorProduct
