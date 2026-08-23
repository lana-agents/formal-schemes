import FormalSchemes.AffineDiagonal

set_option linter.style.header false

/-!
# Affine formal spectra are separated over the base

For a base adic ring `(R, I)` (with `I` finitely generated) and a complete adic `R`-algebra `A`
whose ideal of definition is the extension `I·A`, the diagonal morphism

```
Δ_{A/R} : Spf A ⟶ Spf (A ⊗̂_R A)
```

of the affine fibre product `Spf A ×_{Spf R} Spf A` (`FormalSchemes.AffineDiagonal`, EGA I 10.15)
is a **section of both projections**, so it is a *split monomorphism* and in particular a
**monomorphism**. This is the categorical statement that the affine formal spectrum `Spf A` is
**separated over `Spf R`**.

At the ring level the diagonal is `Spf` of the **codiagonal** (multiplication) map

```
∇ : A ⊗̂_R A →+* A,   a ⊗ b ↦ a · b,
```

which is **surjective** (it splits the canonical map `inl : A → A ⊗̂_R A`). Surjectivity of the
codiagonal is the ring-level input to the sharper statement that `Δ_{A/R}` is a *closed* immersion
(EGA I 10.15): a formal spectrum is separated over the base iff its diagonal is a closed immersion,
and the affine diagonal is cut out by the kernel of the surjection `∇`.

## Main definitions and results

* `CompletedTensorProduct.codiagonal`: the multiplication map `A ⊗̂_R A →+* A`.
* `CompletedTensorProduct.codiagonal_surjective`: the codiagonal is surjective.
* `CompletedTensorProduct.isSplitMono_diagonal`: the diagonal `Δ_{A/R}` is a split monomorphism.
* `CompletedTensorProduct.mono_diagonal`: the diagonal `Δ_{A/R}` is a monomorphism — the affine
  formal spectrum `Spf A` is separated over `Spf R`.

**Scope.** This delivers the categorical *separatedness* content (the diagonal is a monomorphism)
and the ring-level surjectivity of the codiagonal. The upgrade of `Δ_{A/R}` to a genuine *closed
immersion of locally ringed spaces* — the full EGA I 10.15 statement — is
`CompletedTensorProduct.diagonal_isClosedImmersion` (`FormalSchemes.ClosedImmersionSections`), and
its packaging through the `FormalScheme.IsClosedImmersion` predicate is
`CompletedTensorProduct.schemeDiagonal_isClosedImmersion` (`FormalSchemes.ClosedImmersionAffine`).
Separatedness of a non-affine `X` over `Spf R` — which needs the fibre product of general formal
schemes over the affine cover — is `BothChartedFibreDatumXY.IsSeparated`
(`FormalSchemes.GeneralSeparated`), stated of the formal scheme itself as
`FormalScheme.IsSeparatedOverSpf` (`FormalSchemes.GeneralSeparatedScheme`).

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
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

variable (R I A) in
/-- The **codiagonal** (multiplication) map `∇ : A ⊗̂_R A →+* A`, `a ⊗ b ↦ a · b`, obtained as the
lift of the pair of identity `R`-algebra maps `(id_A, id_A)`. It is the underlying ring map of the
diagonal `Δ_{A/R}` (`CompletedTensorProduct.diagonal`). -/
def codiagonal : CompletedTensorProduct R I A A →+* A :=
  lift (I.map (algebraMap R A)) (le_refl _) (AlgHom.id R A) (AlgHom.id R A)

set_option linter.unusedSectionVars false in
@[simp]
theorem codiagonal_inl (a : A) : codiagonal R I A (inl R I A A a) = a := by
  rw [codiagonal, lift_inl, AlgHom.id_apply]

set_option linter.unusedSectionVars false in
@[simp]
theorem codiagonal_inr (a : A) : codiagonal R I A (inr R I A A a) = a := by
  rw [codiagonal, lift_inr, AlgHom.id_apply]

/-- The codiagonal `∇ : A ⊗̂_R A →+* A` is **surjective**: it splits the canonical inclusion
`inl : A → A ⊗̂_R A`. This is the ring-level input to `Δ_{A/R}` being a closed immersion. -/
theorem codiagonal_surjective : Function.Surjective (codiagonal R I A) :=
  fun a => ⟨inl R I A A a, codiagonal_inl a⟩

/-- The diagonal `Δ_{A/R}` is a **split monomorphism**, split by the first projection
`fibrePr₁ : Spf (A ⊗̂_R A) ⟶ Spf A` (it is equally split by `fibrePr₂`). -/
instance isSplitMono_diagonal (hI : I.FG) :
    IsSplitMono (diagonal (A := A) hI) :=
  IsSplitMono.mk' ⟨fibrePr₁, diagonal_comp_pr₁ hI⟩

/-- The diagonal `Δ_{A/R} : Spf A ⟶ Spf (A ⊗̂_R A)` is a **monomorphism** — the affine formal
spectrum `Spf A` is separated over `Spf R` (EGA I 10.15). -/
instance mono_diagonal (hI : I.FG) : Mono (diagonal (A := A) hI) :=
  inferInstance

end CompletedTensorProduct
