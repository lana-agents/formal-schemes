import FormalSchemes.TateSelfProductOverlap
import FormalSchemes.TateSelfProductRightOverlap
import FormalSchemes.CompletedTensorAwayInterchangeBoth

set_option linter.style.header false
-- The completed-tensor interchange morphisms range over the nested localization/completion
-- towers of the completed tensor product, which are slow for the elaborator and the kernel;
-- raise the budgets (matching `CompletedTensorAwayInterchangeBoth.lean`).
set_option linter.style.setOption false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The both-factors-differing four-fold overlap chart of the Tate self-fibre-product

Fix an adic base `(R, I)` with `q ∈ I` (the Tate parameter is topologically nilpotent) and finitely
generated `I`, and let `A = annulusAlgebra R I q = R{x, y}/(x·y − q)` be the coordinate ring of the
formal Tate annulus. This file assembles the **both-factors-differing** overlap chart of the self
fibre-product `𝔈_q ×_{Spf R} 𝔈_q`: the piece of the eventual four-chart glue datum where *both*
factors' charts differ (`D(x)` vs `D(y)` in each factor).

Concretely, with `C = A ⊗̂_R A` the completed tensor product of the annulus algebra with itself
(coordinate ring of `Spf A ×_{Spf R} Spf A`), the two coordinates `x, y ∈ A` give rise, via the
**both-factor** completed-tensor / away-localization interchange
(`CompletedTensorAwayInterchange.bothInterchangeOpenImmersion`), to four open immersions

* `bothInterchangeOpenImmersion I x x hI : Spf((A{1/x}) ⊗̂_R (A{1/x})) ⟶ Spf C`, image
  `D(x⊗1) ⊓ D(1⊗x)`, and the three analogues for `(x, y)`, `(y, x)`, `(y, y)`,

all landing in the *same* target `Spf C`, with underlying-space ranges `D(inl a) ⊓ D(inr b)` for
`a, b ∈ {x, y}` (`range_bothInterchangeOpenImmersion_base`). The four ranges are **pairwise
disjoint**: for `(a, b) ≠ (a', b')` either `a ≠ a'` — forcing `D(inl x) ⊓ D(inl y) = ⊥`
(`selfProductOverlap_basicOpen_disjoint`, since `x·y = q ∈ I` is topologically nilpotent) — or
`b ≠ b'` — forcing `D(inr x) ⊓ D(inr y) = ⊥` (`selfProductRightOverlap_basicOpen_disjoint`). Hence
the nested coproduct chart

`coprod.desc (coprod.desc (bothⁱⁿ x x) (bothⁱⁿ x y)) (coprod.desc (bothⁱⁿ y x) (bothⁱⁿ y y))`

is an open immersion onto `⋃_{a,b} D(inl a) ⊓ D(inr b) ⊆ Spf C`. This is the `V`/`f` overlap datum
(for the both-factors-differing chart shape) that the eventual four-chart glue of
`𝔈_q ×_{Spf R} 𝔈_q` consumes.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.range_coprodDesc_base`: the underlying-space
  range of `coprod.desc f g` is the union of the ranges of `f` and `g` (a reusable general fact).
* `AlgebraicGeometry.tateSelfProductBothOverlapChart`: the nested four-fold coproduct chart into
  `Spf C`.
* `AlgebraicGeometry.isOpenImmersion_tateSelfProductBothOverlapChart`: it is a
  `LocallyRingedSpace.IsOpenImmersion`.

Its underlying-space range is the union of the four basic-open intersections `D(inl a) ⊓ D(inr b)`,
`a, b ∈ {x, y}`, which the downstream glue can recover from `range_coprodDesc_base` and
`range_bothInterchangeOpenImmersion_base`.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7, §9.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7, §10.13.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum TopologicalSpace

universe u

namespace AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion

variable {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)

/-- **The underlying-space range of `coprod.desc f g` is the union of the two ranges.** Every point
of the coproduct comes from one of the two inclusions (`coprod_base_mem_range`), on which
`coprod.desc f g` restricts to `f` resp. `g` (`coprodDesc_base_comp_inl`/`inr`); conversely each of
`f.base`, `g.base` factors through `coprod.desc f g`. -/
theorem range_coprodDesc_base :
    Set.range (coprod.desc f g).base = Set.range f.base ∪ Set.range g.base := by
  have hcl : ∀ a, (coprod.desc f g).base ((coprod.inl : X ⟶ X ⨿ Y).base a) = f.base a :=
    fun a => congrArg (fun m => m a) (coprodDesc_base_comp_inl f g)
  have hcr : ∀ b, (coprod.desc f g).base ((coprod.inr : Y ⟶ X ⨿ Y).base b) = g.base b :=
    fun b => congrArg (fun m => m b) (coprodDesc_base_comp_inr f g)
  apply Set.Subset.antisymm
  · rintro _ ⟨w, rfl⟩
    rcases LocallyRingedSpace.coprod_base_mem_range w with ⟨a, ha⟩ | ⟨b, hb⟩
    · exact Or.inl ⟨a, by rw [← ha]; exact (hcl a).symm⟩
    · exact Or.inr ⟨b, by rw [← hb]; exact (hcr b).symm⟩
  · rintro x (⟨a, rfl⟩ | ⟨b, rfl⟩)
    · exact ⟨(coprod.inl : X ⟶ X ⨿ Y).base a, hcl a⟩
    · exact ⟨(coprod.inr : Y ⟶ X ⨿ Y).base b, hcr b⟩

end AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion

namespace AlgebraicGeometry

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- The coordinate ring of the formal Tate annulus, base for the self fibre-product. -/
private abbrev A : Type u := annulusAlgebra R I q

/-- The completed tensor product `A ⊗̂_R A`, coordinate ring of `Spf A ×_{Spf R} Spf A`. -/
private abbrev C : Type u := CompletedTensorProduct R I (A R I q) (A R I q)

section Disjoint

variable {X : Type*} [TopologicalSpace X]

/-- Two opens with `⊥` intersection have disjoint underlying sets. -/
private theorem coe_disjoint_of_inf_eq_bot {P Q : Opens X} (h : P ⊓ Q = ⊥) :
    Disjoint (↑P : Set X) (↑Q : Set X) := by
  rw [Set.disjoint_iff_inter_eq_empty, ← Opens.coe_inf, h, Opens.coe_bot]

/-- If the *first* meetands are disjoint (`P₁ ⊓ P₂ = ⊥`) then the two products `P₁ ⊓ Q₁` and
`P₂ ⊓ Q₂` have disjoint underlying sets. -/
private theorem disjoint_coe_inf_left {P₁ P₂ : Opens X} (Q₁ Q₂ : Opens X) (h : P₁ ⊓ P₂ = ⊥) :
    Disjoint (↑(P₁ ⊓ Q₁) : Set X) (↑(P₂ ⊓ Q₂) : Set X) :=
  coe_disjoint_of_inf_eq_bot
    (le_bot_iff.mp ((inf_le_inf inf_le_left inf_le_left).trans h.le))

/-- If the *second* meetands are disjoint (`Q₁ ⊓ Q₂ = ⊥`) then the two products `P₁ ⊓ Q₁` and
`P₂ ⊓ Q₂` have disjoint underlying sets. -/
private theorem disjoint_coe_inf_right (P₁ P₂ : Opens X) {Q₁ Q₂ : Opens X} (h : Q₁ ⊓ Q₂ = ⊥) :
    Disjoint (↑(P₁ ⊓ Q₁) : Set X) (↑(P₂ ⊓ Q₂) : Set X) :=
  coe_disjoint_of_inf_eq_bot
    (le_bot_iff.mp ((inf_le_inf inf_le_right inf_le_right).trans h.le))

end Disjoint

/-- Abbreviation for the both-factor interchange open immersion
`Spf((A{1/a}) ⊗̂_R (A{1/b})) ⟶ Spf C` of the two annulus coordinates `a, b`. -/
private abbrev bothChart (a b : A R I q) (hI : I.FG) :=
  CompletedTensorAwayInterchange.bothInterchangeOpenImmersion
    (A := A R I q) (B := A R I q) I a b hI

/-- **The both-factors-differing four-fold overlap chart of `𝔈_q ×_{Spf R} 𝔈_q`.** The nested
coproduct `coprod.desc` of the four both-factor interchange charts
`bothInterchangeOpenImmersion I a b hI` for `a, b ∈ {overlapX, overlapY}`, all into `Spf C`
(`C = A ⊗̂_R A`). This is the `V`/`f` overlap datum (for the both-factors-differing chart shape)
feeding the eventual four-chart glue of the self fibre-product. -/
def tateSelfProductBothOverlapChart (hI : I.FG) :=
  coprod.desc
    (coprod.desc (bothChart R I q (overlapX R I q) (overlapX R I q) hI)
      (bothChart R I q (overlapX R I q) (overlapY R I q) hI))
    (coprod.desc (bothChart R I q (overlapY R I q) (overlapX R I q) hI)
      (bothChart R I q (overlapY R I q) (overlapY R I q) hI))

/-- **The four both-factor interchange overlap charts are an open immersion out of their
coproduct.** The four underlying-space ranges `D(inl a) ⊓ D(inr b)`, `a, b ∈ {x, y}`
(`range_bothInterchangeOpenImmersion_base`), are pairwise disjoint: charts differing in the first
factor are separated by `D(inl x) ⊓ D(inl y) = ⊥` (`selfProductOverlap_basicOpen_disjoint`), charts
differing only in the second factor by `D(inr x) ⊓ D(inr y) = ⊥`
(`selfProductRightOverlap_basicOpen_disjoint`). Nesting `IsOpenImmersion.coprodDesc` twice then
yields the open immersion. -/
theorem isOpenImmersion_tateSelfProductBothOverlapChart (hq : q ∈ I) (hI : I.FG) :
    LocallyRingedSpace.IsOpenImmersion (tateSelfProductBothOverlapChart R I q hI) := by
  -- open-immersion instances for the four charts
  haveI hxx := CompletedTensorAwayInterchange.isOpenImmersion_bothInterchangeOpenImmersion
    (A := A R I q) (B := A R I q) I (overlapX R I q) (overlapX R I q) hI
  haveI hxy := CompletedTensorAwayInterchange.isOpenImmersion_bothInterchangeOpenImmersion
    (A := A R I q) (B := A R I q) I (overlapX R I q) (overlapY R I q) hI
  haveI hyx := CompletedTensorAwayInterchange.isOpenImmersion_bothInterchangeOpenImmersion
    (A := A R I q) (B := A R I q) I (overlapY R I q) (overlapX R I q) hI
  haveI hyy := CompletedTensorAwayInterchange.isOpenImmersion_bothInterchangeOpenImmersion
    (A := A R I q) (B := A R I q) I (overlapY R I q) (overlapY R I q) hI
  -- the two inner coproducts (fixed first factor, second factor `x` vs `y`) are open immersions
  haveI hIL : LocallyRingedSpace.IsOpenImmersion
      (coprod.desc (bothChart R I q (overlapX R I q) (overlapX R I q) hI)
        (bothChart R I q (overlapX R I q) (overlapY R I q) hI)) := by
    refine LocallyRingedSpace.IsOpenImmersion.coprodDesc _ _ ?_
    rw [CompletedTensorAwayInterchange.range_bothInterchangeOpenImmersion_base,
      CompletedTensorAwayInterchange.range_bothInterchangeOpenImmersion_base]
    exact disjoint_coe_inf_right _ _ (selfProductRightOverlap_basicOpen_disjoint R I q hq)
  haveI hIR : LocallyRingedSpace.IsOpenImmersion
      (coprod.desc (bothChart R I q (overlapY R I q) (overlapX R I q) hI)
        (bothChart R I q (overlapY R I q) (overlapY R I q) hI)) := by
    refine LocallyRingedSpace.IsOpenImmersion.coprodDesc _ _ ?_
    rw [CompletedTensorAwayInterchange.range_bothInterchangeOpenImmersion_base,
      CompletedTensorAwayInterchange.range_bothInterchangeOpenImmersion_base]
    exact disjoint_coe_inf_right _ _ (selfProductRightOverlap_basicOpen_disjoint R I q hq)
  -- the outer coproduct (first factor `x` vs `y`) is an open immersion
  refine LocallyRingedSpace.IsOpenImmersion.coprodDesc _ _ ?_
  rw [LocallyRingedSpace.IsOpenImmersion.range_coprodDesc_base,
    LocallyRingedSpace.IsOpenImmersion.range_coprodDesc_base,
    CompletedTensorAwayInterchange.range_bothInterchangeOpenImmersion_base,
    CompletedTensorAwayInterchange.range_bothInterchangeOpenImmersion_base,
    CompletedTensorAwayInterchange.range_bothInterchangeOpenImmersion_base,
    CompletedTensorAwayInterchange.range_bothInterchangeOpenImmersion_base]
  -- both inner coproducts sit in `D(inl x)` resp. `D(inl y)`, separated by
  -- `D(inl x) ⊓ D(inl y) = ⊥`. Assembled term-mode (via `Disjoint.union_left`/`union_right`) to
  -- elaborate at default transparency, sidestepping the LRS-carrier/`FormalSpectrum` defeq wall
  -- that `rw`-matching against `Set.disjoint_union_left` hits.
  exact Disjoint.union_left
    (Disjoint.union_right
      (disjoint_coe_inf_left _ _ (selfProductOverlap_basicOpen_disjoint R I q hq))
      (disjoint_coe_inf_left _ _ (selfProductOverlap_basicOpen_disjoint R I q hq)))
    (Disjoint.union_right
      (disjoint_coe_inf_left _ _ (selfProductOverlap_basicOpen_disjoint R I q hq))
      (disjoint_coe_inf_left _ _ (selfProductOverlap_basicOpen_disjoint R I q hq)))

end AlgebraicGeometry
