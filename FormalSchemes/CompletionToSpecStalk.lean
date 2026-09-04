import FormalSchemes.CompletionToSpec

set_option linter.style.header false

/-!
# The stalk maps of `X_{/Y} ⟶ X`, and the closed-immersion question posed

`formalCompletion.toSpec` is a **closed embedding on underlying spaces**
(`formalCompletion.isClosedEmbedding_toSpec_base`, EGA I 10.8), and the two files that carry that
statement to a glued index — `FormalSchemes.CompletionTwoPatchEmbedding` and
`FormalSchemes.ChartedCompletionEmbedding` — both stop there, correctly and by scope: both are
about underlying topological spaces throughout.

What made the *scheme-theoretic* closed immersion look unaskable at any index is a fact about a
**predicate**, not about the question. `AlgebraicGeometry.FormalScheme.IsClosedImmersion` is a
predicate on morphisms of formal schemes and the target here is an honest scheme, so it does not
apply. But `formalCompletion.toSpec` is a morphism of `AlgebraicGeometry.LocallyRingedSpace` — its
target is `AlgebraicGeometry.Spec.locallyRingedSpaceObj` of `R` — and
`AlgebraicGeometry.LocallyRingedSpace.Hom.stalkMap` is defined for any such morphism. So the
conjunction *closed embedding on the base, and surjective on stalks* can be written down as it
stands, and `formalCompletion.IsClosedImmersionToSpec` below writes it.

This is the same raw-conjunction idiom as
`FormalSpectrum.isClosedEmbedding_base_and_surjective_stalkMap_of_surjective`
(`FormalSchemes.ClosedImmersionSections`), which states exactly this pair unpackaged. The reason
differs, and conflating the two would misread the precedent: there the packaging does not exist yet
at that point in the import order — `FormalSchemes.ClosedImmersion` imports that file and not the
other way round, and `FormalSchemes.ClosedImmersionSections` never mentions
`AlgebraicGeometry.FormalScheme.IsClosedImmersion` — whereas here it exists and cannot apply. What
carries over is the idiom, not a choice made with the packaged alternative in scope.

## Main results

* `formalCompletion.toStalk_comp_stalkMap_toSpec`: **the stalk map, computed on the image of
  `AlgebraicGeometry.StructureSheaf.toStalk`.** Precomposed with that map, the stalk map of
  `formalCompletion.toSpec` at `x` is the completion map `R →+* R^` followed by the germ at `x`.
  Since `AlgebraicGeometry.StructureSheaf.toStalk` presents the stalk of `Spec R` as a localization
  of `R`, this determines the stalk map completely.
* `formalCompletion.stalkMap_toSpec_toStalk`: the same, read on an element of `R`.
* `formalCompletion.IsClosedImmersionToSpec` and
  `formalCompletion.isClosedImmersionToSpec_iff_surjective_stalkMap`: **the question, posed**, and
  the observation that its topological half is already a theorem, so all of its content is the
  stalk half.
* `formalCompletion.nonempty_formalSpectrum_of_ne_top`: for `I ≠ ⊤` the stalk half quantifies over
  a nonempty set, so it is not a condition with nothing to check.

## What is *not* proved here

**Whether the stalk maps are surjective.** Nothing in this file decides
`formalCompletion.IsClosedImmersionToSpec`, and it should not be assumed to hold: the stalk map runs
`O_{Spec R, f x} ⟶ O_{Spf R^, x}`, i.e. *along* the completion, in the direction that adds elements,
and `formalCompletion.toStalk_comp_stalkMap_toSpec` says precisely that everything in its image
comes from `R` — through `algebraMap R (AdicCompletion I R)` — after inverting what is invertible
at `x`. Whether that exhausts the stalk is a question about the completion map, and the expected
answer is no whenever the relevant local ring of `R` is not already adically complete.

Also not here: the *positive* stalk half of EGA I 10.8 — that the stalk of the completion is the
completion of the stalk — and the universal property of the completion. Neither is touched, and a
reader who learns that `formalCompletion.toSpec` is not a closed immersion should not conclude that
10.8 has no stalk-level content.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Topology TopologicalSpace Opposite

universe u

namespace formalCompletion

section ToSpecStalk

variable (R : Type u) [CommRing R] (I : Ideal R)

/-! ### The stalk map on the image of `AlgebraicGeometry.StructureSheaf.toStalk` -/

/-- **The stalk map of `X_{/Y} ⟶ X`, computed on the image of
`AlgebraicGeometry.StructureSheaf.toStalk`.**

`formalCompletion.toSpec` is `FormalSpectrum.specHomEquiv`'s inverse applied to the completion map,
so by `FormalSpectrum.specHomEquiv_symm_apply` it is the unit of `Γ ⊣ Spec` followed by `Spec` of
that map. `AlgebraicGeometry.stalkMap_toStalk` computes the second factor's stalk map after
`AlgebraicGeometry.StructureSheaf.toStalk`, and
`AlgebraicGeometry.LocallyRingedSpace.toStalk_stalkMap_toΓSpec` computes the first factor's;
composing them leaves the completion map followed by the germ at `x`.

Since `AlgebraicGeometry.StructureSheaf.toStalk` exhibits the stalk of `Spec R` at a point as the
localization of `R` there, this determines the stalk map, and it is the statement
`formalCompletion.IsClosedImmersionToSpec` has to be decided against. -/
theorem toStalk_comp_stalkMap_toSpec (hI : I.FG)
    (x : FormalSpectrum (AdicCompletion.idealOfDefinition I)) :
    haveI := AdicCompletion.isAdicRing_map I hI
    StructureSheaf.toStalk R ((toSpec R I hI).base x) ≫ (toSpec R I hI).stalkMap x =
      CommRingCat.ofHom ((FormalSpectrum.globalSectionsEquiv
          (AdicCompletion.idealOfDefinition I)).symm.toRingHom.comp
          (algebraMap R (AdicCompletion I R))) ≫
        (formalCompletion R I hI).toLocallyRingedSpace.presheaf.Γgerm x := by
  haveI := AdicCompletion.isAdicRing_map I hI
  set X := FormalSpectrum.locallyRingedSpaceObj (AdicCompletion.idealOfDefinition I) with hX
  set ψ : CommRingCat.of R ⟶ LocallyRingedSpace.Γ.obj (op X) :=
    CommRingCat.ofHom ((FormalSpectrum.globalSectionsEquiv
      (AdicCompletion.idealOfDefinition I)).symm.toRingHom.comp
      (algebraMap R (AdicCompletion I R))) with hψ
  have hdef : toSpec R I hI = identityToΓSpec.app X ≫ Spec.locallyRingedSpaceMap ψ :=
    FormalSpectrum.specHomEquiv_symm_apply _ R _
  rw [hdef]
  refine Eq.trans (congrArg (fun m => StructureSheaf.toStalk R _ ≫ m)
    (LocallyRingedSpace.stalkMap_comp (identityToΓSpec.app X)
      (Spec.locallyRingedSpaceMap ψ) x)) ?_
  have h1 : StructureSheaf.toStalk R
        ((identityToΓSpec.app X ≫ Spec.locallyRingedSpaceMap ψ).base x) ≫
      (Spec.locallyRingedSpaceMap ψ).stalkMap ((identityToΓSpec.app X).base x) =
      ψ ≫ StructureSheaf.toStalk _ ((identityToΓSpec.app X).base x) :=
    AlgebraicGeometry.stalkMap_toStalk ψ _
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  refine Eq.trans (congrArg
    (fun m => m ≫ LocallyRingedSpace.Hom.stalkMap (identityToΓSpec.app X) x) h1) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact congrArg (fun m => ψ ≫ m) (LocallyRingedSpace.toStalk_stalkMap_toΓSpec X x)

/-- **`formalCompletion.toStalk_comp_stalkMap_toSpec` read on an element of `R`**: the stalk map
sends the germ at `f x` of a global section of `Spec R` coming from `a : R` to the germ at `x` of
the image of `a` under the completion map. -/
theorem stalkMap_toSpec_toStalk (hI : I.FG)
    (x : FormalSpectrum (AdicCompletion.idealOfDefinition I)) (a : R) :
    haveI := AdicCompletion.isAdicRing_map I hI
    ((toSpec R I hI).stalkMap x).hom ((StructureSheaf.toStalk R ((toSpec R I hI).base x)).hom a) =
      ((formalCompletion R I hI).toLocallyRingedSpace.presheaf.Γgerm x).hom
        ((FormalSpectrum.globalSectionsEquiv (AdicCompletion.idealOfDefinition I)).symm
          (algebraMap R (AdicCompletion I R) a)) := by
  haveI := AdicCompletion.isAdicRing_map I hI
  have h := toStalk_comp_stalkMap_toSpec R I hI x
  exact congrArg (fun m : CommRingCat.of R ⟶ _ => m.hom a) h

/-! ### The question -/

/-- **Is `X_{/Y} ⟶ X` a closed immersion?** The Stacks-Project condition for locally ringed spaces
(Tag 01HJ) — a closed topological embedding of the base, and surjective stalk maps — written out for
`formalCompletion.toSpec`.

It is written as the raw conjunction rather than through
`AlgebraicGeometry.FormalScheme.IsClosedImmersion` because that predicate is about morphisms of
formal schemes and this morphism's target is not one. That is a fact about the predicate, not about
the question: both conjuncts are statements about a morphism of
`AlgebraicGeometry.LocallyRingedSpace` and neither needs anything the target does not have.

`formalCompletion.isClosedImmersionToSpec_iff_surjective_stalkMap` says the first conjunct is free,
so this is the stalk half and nothing else. **It is not proved here, and it is not expected to hold
in general** — see this file's module docstring. -/
def IsClosedImmersionToSpec (hI : I.FG) : Prop :=
  IsClosedEmbedding ⇑(toSpec R I hI).base ∧
    ∀ x, Function.Surjective ⇑((toSpec R I hI).stalkMap x).hom

/-- **The topological half of the closed-immersion condition is already a theorem**
(`formalCompletion.isClosedEmbedding_toSpec_base`), so all of the content of
`formalCompletion.IsClosedImmersionToSpec` is the surjectivity of the stalk maps. -/
theorem isClosedImmersionToSpec_iff_surjective_stalkMap (hI : I.FG) :
    IsClosedImmersionToSpec R I hI ↔
      ∀ x, Function.Surjective ⇑((toSpec R I hI).stalkMap x).hom :=
  ⟨And.right, fun h => ⟨isClosedEmbedding_toSpec_base R I hI, h⟩⟩

/-! ### Non-vacuity -/

/-- **For `I ≠ ⊤` the stalk half of `formalCompletion.IsClosedImmersionToSpec` quantifies over a
nonempty set**, so it is not a condition that holds because there is nothing to check. The image of
`formalCompletion.toSpec` is `V(I)` (`formalCompletion.range_toSpec_base`), which is nonempty
exactly when `I ≠ ⊤`.

The general statement is `FormalSpectrum.nonempty_iff_ne_top`
(`FormalSchemes.TateInvNodeChartSpfNonempty`) and this is one more of its instances:
`annulus_formalSpectrum_nonempty` and `FormalSpectrum.nonempty_twoAdic` predate it, while
`AlgebraicGeometry.nonempty_formalSpectrum_tateInvNodeChartAwayIdeal`,
`AlgebraicGeometry.nonempty_thickening_tateInvNodeChart` and
`AlgebraicGeometry.nonempty_formalSpectrum_tateInvNodeChartQuotientIdeal` apply it. It duplicates
none of them: the content here is the *transport*, from `I ≠ ⊤` in `R` to nonemptiness of the
formal spectrum of `AdicCompletion.idealOfDefinition I` in the completion. Going through the
general statement instead lands on `AdicCompletion.idealOfDefinition I ≠ ⊤`, which is not on the
tree; the route through `formalCompletion.range_toSpec_base` avoids needing it. -/
theorem nonempty_formalSpectrum_of_ne_top (hI : I.FG) (hItop : I ≠ ⊤) :
    Nonempty (FormalSpectrum (AdicCompletion.idealOfDefinition I)) := by
  have hne : (PrimeSpectrum.zeroLocus (I : Set R)).Nonempty := by
    rwa [Set.nonempty_iff_ne_empty, ne_eq, PrimeSpectrum.zeroLocus_empty_iff_eq_top]
  rw [← range_toSpec_base R I hI] at hne
  exact ⟨hne.choose_spec.choose⟩

end ToSpecStalk

end formalCompletion
