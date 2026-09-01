import FormalSchemes.ChartedCompletionToScheme
import FormalSchemes.CompletionCompact
import Mathlib.Algebra.Polynomial.Laurent

set_option linter.style.header false

/-!
# The projective line completed at a closed point (EGA I, 10.8)

`FormalSchemes/ChartedSchemeDatum.lean` and `FormalSchemes/ChartedCompletionDatum.lean` introduce a
datum of affine charts carrying an **independent ideal `K i` in each chart ring `C i`**, rather than
one ideal `I` in one base ring pulled back to every chart the way
`AlgebraicGeometry.AffineChartedFibreDatumX` does. Both files name the same example as the reason
for that shape and both say it is not formalised: the projective line completed at a closed point,
whose two charts want `K₀ = (x)` and `K₁ = ⊤`, since the point is not in the second chart at all.

This file is that example.

## The construction, and the one simplification the motivating passages do not take

They ask for `C₀ = k[x]`, `C₁ = k[y]` and an isomorphism `k[x]_x ≃+* k[y]_y` carrying `x` to `y⁻¹`.
The two chart rings are the *same* ring with the indeterminate renamed, so the datum is stated here
over one `R[X]`, for an arbitrary `[CommRing R]` — no field is needed — with `g 0 1 = g 1 0 = X`
and the transition the **inversion automorphism** `awayXInv` of `R[X]_X`.

That the transition is inversion and not the identity is the whole geometric content: gluing two
affine lines along `D(X) ≅ D(X)` by `RingEquiv.refl` gives the line with a doubled origin, and by
inversion gives `ℙ¹`. `awayXInv_algebraMap_X_mul` and `awayXInv_ne_refl` pin that down, and they
are needed for exactly that reason — the datum's own ideal-compatibility field `hθ` does **not**
see it. `projectiveLine_hθ` is the equation `⊤ = ⊤`: `X` is already a unit in `R[X]_X`, so
`K₀ · R[X]_X` is the unit ideal before the transition is applied, and so is `K₁ · R[X]_X`. That is
the algebraic shadow of "the point being completed at is not on the overlap", and it is why one
chart may carry a proper ideal while the other carries `⊤`. **A green `hθ` is therefore no evidence
that the gluing is the right one.**

The inversion itself is Mathlib's, through `LaurentPolynomial.isLocalization` — which identifies
`Localization.Away (X : R[X])` with `R[T;T⁻¹]` — and `LaurentPolynomial.invert`, whose involutivity
(`LaurentPolynomial.invert_symm`) is what makes the datum's `θ_symm` field free.

## Non-vacuity

A datum shape that *admits* independent ideals is worth nothing until something instantiates it
with ideals that are actually independent, and this tree has shipped degenerate witnesses before.
Three statements say this one is not degenerate:

* `projectiveLineDatum_K_false_ne_top`: the first ideal is proper (for `[Nontrivial R]`), while
  `projectiveLineDatum_K_true` is `⊤` on the nose. Neither is the image of the other under any map
  of chart rings, which is precisely what `AffineChartedFibreDatumX` cannot express.
* `isEmpty_projectiveLine_chart_true` and `nonempty_projectiveLine_chart_false`: the second
  completion chart is **empty** and the first is not. The glued completion is supported in the
  first chart, as the geometry demands.
* `awayXInv_ne_refl`: the gluing is not the doubled-origin one.

## Main definitions and results

* `AlgebraicGeometry.awayXEquivLaurent`: `Localization.Away (X : R[X]) ≃ₐ[R[X]] R[T;T⁻¹]`.
* `AlgebraicGeometry.awayXInv` with `..awayXInv_symm`, `..awayXInv_algebraMap_X_mul` and
  `..awayXInv_ne_refl`: inversion on `R[X]_X`, its involutivity, the computation `X ↦ X⁻¹`, and
  that it is not the identity.
* `AlgebraicGeometry.map_span_X_away_eq_top`, `AlgebraicGeometry.projectiveLine_hθ`: the ideal
  compatibility, and the unit-ideal computation behind it.
* `AlgebraicGeometry.projectiveLineDatum`: the datum, with `..projectiveLineDatum_K_false`,
  `..projectiveLineDatum_K_true` and `..projectiveLineDatum_θ`.
* `AlgebraicGeometry.projectiveLine`, `..projectiveLineCompletion`,
  `..projectiveLineCompletionToScheme`: the ambient scheme, its completion, and `X_{/Y} ⟶ X`.
* `AlgebraicGeometry.span_X_ne_top`: the one small ideal fact the non-degeneracy needs. The
  datum's other finite-generation witness is Mathlib's `Ideal.fg_top`.

## What is *not* proved

* **Nothing says `projectiveLine` is `ℙ¹` in any pre-existing sense, or that it is not affine.**
  There is no `Proj` on this tree to compare against, and no global-sections computation is made
  here. What is established is a statement about the *datum*: it is a `ChartedCompletionDatum`
  whose two chart ideals are independent and one of which is `⊤`.
* Nothing **here** promotes `projectiveLine` to `AlgebraicGeometry.Scheme`, but
  `FormalSchemes.ChartedSchemeDatumScheme` does it for every datum, so
  `(projectiveLineDatum R).specScheme` is already a scheme on this carrier by `rfl` and only the
  abbreviation at this name is missing.
* The triple-overlap fields are vacuous, as they are for every two-chart datum. The instance that
  exercises them is `AlgebraicGeometry.SpecThreeChartCover.completionDatum`
  (`FormalSchemes.SpecThreeChartCompletion`), whose chart ideals all come from one `(A, I)` — so
  the two witnesses are complementary and neither replaces the other.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial LaurentPolynomial

universe u

namespace AlgebraicGeometry

section Inversion

variable (R : Type u) [CommRing R]

/-- The away localization of `R[X]` at `X` is the Laurent polynomial ring. -/
def awayXEquivLaurent : Localization.Away (X : R[X]) ≃ₐ[R[X]] R[T;T⁻¹] :=
  IsLocalization.algEquiv (Submonoid.powers (X : R[X])) _ _

/-- **Inversion `X ↦ X⁻¹` on `R[X]_X`.** -/
def awayXInv : Localization.Away (X : R[X]) ≃+* Localization.Away (X : R[X]) :=
  ((awayXEquivLaurent R).toRingEquiv.trans (LaurentPolynomial.invert (R := R)).toRingEquiv).trans
    (awayXEquivLaurent R).symm.toRingEquiv

/-- **Inversion is an involution.** -/
theorem awayXInv_symm : (awayXInv R).symm = awayXInv R := by
  ext x
  simp [awayXInv, RingEquiv.symm_trans_apply]

/-- **Inversion sends `X` to its inverse**: this is what pins the gluing down to `ℙ¹`. -/
theorem awayXInv_algebraMap_X_mul :
    awayXInv R (algebraMap R[X] (Localization.Away (X : R[X])) X) *
      algebraMap R[X] (Localization.Away (X : R[X])) X = 1 := by
  have he : (awayXEquivLaurent R) (algebraMap R[X] (Localization.Away (X : R[X])) X) = T 1 := by
    rw [AlgEquiv.commutes, LaurentPolynomial.algebraMap_eq_toLaurent, toLaurent_X]
  have hx : algebraMap R[X] (Localization.Away (X : R[X])) X
      = (awayXEquivLaurent R).symm (T 1) := by
    rw [← he, AlgEquiv.symm_apply_apply]
  have hinv : awayXInv R (algebraMap R[X] (Localization.Away (X : R[X])) X) =
      (awayXEquivLaurent R).symm (T (-1)) := by
    simp only [awayXInv, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv, he, invert_T]
  rw [hinv, hx, ← map_mul, ← T_add]
  simp

/-- **Inversion is not the identity.** Gluing the two affine lines along `RingEquiv.refl` would
give the line with a doubled origin; it is this lemma that makes the datum below `ℙ¹`. -/
theorem awayXInv_ne_refl [Nontrivial R] :
    awayXInv R ≠ RingEquiv.refl (Localization.Away (X : R[X])) := by
  intro h
  have hx : awayXInv R ((awayXEquivLaurent R).symm (T 1)) =
      (awayXEquivLaurent R).symm (T 1) := by rw [h]; rfl
  simp only [awayXInv, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv,
    AlgEquiv.apply_symm_apply, invert_T] at hx
  have h2 : (T (-1) : R[T;T⁻¹]) = T 1 := (awayXEquivLaurent R).symm.injective hx
  have h3 := congrArg (fun f : R[T;T⁻¹] => f.coeff (1 : ℤ)) h2
  simp at h3

/-- The ideal generated by `X` in `R[X]_X` is everything, since `X` is a unit there. -/
theorem map_span_X_away_eq_top :
    (Ideal.span {(X : R[X])}).map (algebraMap R[X] (Localization.Away (X : R[X]))) = ⊤ := by
  rw [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_eq_top]
  exact IsLocalization.map_units _ (⟨X, 1, pow_one X⟩ : Submonoid.powers (X : R[X]))

end Inversion

section ProjectiveLine

variable (R : Type u) [CommRing R]

/-- **The ideal compatibility of the two charts is `⊤ = ⊤`.** -/
theorem projectiveLine_hθ :
    ((Ideal.span {(X : R[X])}).map (algebraMap R[X] (Localization.Away (X : R[X])))).map
        (awayXInv R).toRingHom =
      (⊤ : Ideal R[X]).map (algebraMap R[X] (Localization.Away (X : R[X]))) := by
  rw [map_span_X_away_eq_top, Ideal.map_top, Ideal.map_top]

/-- **The projective line over `R`, completed at the origin of its first chart.** -/
def projectiveLineDatum : ChartedCompletionDatum.{u} :=
  ChartedCompletionDatum.ofTwoPatch (Ideal.span {(X : R[X])}) (Submodule.fg_span_singleton X) X
    (⊤ : Ideal R[X]) (Ideal.fg_top R[X]) X (awayXInv R) (projectiveLine_hθ R)

/-- The first chart is completed along the origin. -/
theorem projectiveLineDatum_K_false :
    (projectiveLineDatum R).K ⟨false⟩ = Ideal.span {(X : R[X])} := rfl

/-- The second chart is completed along the empty closed subset. -/
theorem projectiveLineDatum_K_true : (projectiveLineDatum R).K ⟨true⟩ = ⊤ := rfl

/-- **The ambient scheme**: the projective line over `R`. -/
def projectiveLine : LocallyRingedSpace.{u} := (projectiveLineDatum R).specGlued

/-- **The completion of the projective line at the origin of its first chart.** -/
def projectiveLineCompletion : FormalScheme.{u} := (projectiveLineDatum R).completionGlued

/-- **The canonical morphism `X_{/Y} ⟶ X`.** -/
def projectiveLineCompletionToScheme :
    (projectiveLineCompletion R).toLocallyRingedSpace ⟶ projectiveLine R :=
  (projectiveLineDatum R).toScheme

end ProjectiveLine

section NonDegeneracy

variable (R : Type u) [CommRing R]

/-- `(X)` is a proper ideal of `R[X]` as soon as `R` is nontrivial. -/
theorem span_X_ne_top [Nontrivial R] : (Ideal.span {(X : R[X])}) ≠ ⊤ := by
  rw [Ne, Ideal.span_singleton_eq_top]
  exact Polynomial.not_isUnit_X

/-- **The two chart ideals are genuinely different.** -/
theorem projectiveLineDatum_K_false_ne_top [Nontrivial R] :
    (projectiveLineDatum R).K ⟨false⟩ ≠ ⊤ :=
  span_X_ne_top R

/-- **The second completion chart is empty.** -/
instance isEmpty_projectiveLine_chart_true :
    IsEmpty ((projectiveLineDatum R).chart ⟨true⟩) := by
  haveI : Subsingleton ((projectiveLineDatum R).C ⟨true⟩ ⧸ (projectiveLineDatum R).K ⟨true⟩) :=
    Ideal.Quotient.subsingleton_iff.2 rfl
  exact formalCompletion_isEmpty _ _

/-- **The first completion chart has points**, so the completion is not empty either. -/
instance nonempty_projectiveLine_chart_false [Nontrivial R] :
    Nonempty ((projectiveLineDatum R).chart ⟨false⟩) :=
  haveI : Nontrivial ((projectiveLineDatum R).C ⟨false⟩ ⧸ (projectiveLineDatum R).K ⟨false⟩) :=
    Ideal.Quotient.nontrivial_iff.mpr (projectiveLineDatum_K_false_ne_top R)
  formalCompletion_nonempty _ _

/-- The datum's transition is the inversion. -/
theorem projectiveLineDatum_θ (h : (⟨false⟩ : ULift.{u} Bool) ≠ ⟨true⟩) :
    (projectiveLineDatum R).θ ⟨false⟩ ⟨true⟩ h = awayXInv R := rfl

end NonDegeneracy

end AlgebraicGeometry

end
