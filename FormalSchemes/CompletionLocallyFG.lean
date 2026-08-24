import FormalSchemes.LocallyFG
import FormalSchemes.CompletionCompact

set_option linter.style.header false

/-!
# The formal completion is locally finitely generated (EGA I, 10.8)

`FormalScheme.LocallyFG` (`FormalSchemes/LocallyFG.lean`) is the class of formal schemes that are
locally `Spf` of an adic ring with a **finitely generated** ideal of definition. It is the class on
which basic-open charts are available, hence on which affine opens form a neighbourhood basis, and
it is a standing hypothesis of the non-affine universal property of `Spf`
(`existsUnique_globalSectionsHom_eq_of_locallyFG`, `FormalSchemes/GlobalSectionsHomGlue.lean`), of
`OpenCover.glueHomOfGlobalSectionsHom`, and of the target-local criteria for closed immersions
(`FormalSchemes/ClosedImmersionTargetLocal.lean`).

This file discharges it for the formal completion, affine and glued. Neither was known before: the
general lemma `FormalScheme.GlueData.gluedFormalScheme_locallyFG` had a single consumer
(`FormalSchemes/BothDatumFibreAdicOverBase.lean`), and the completion of `Spec R` along `V(I)` was
not recorded as `LocallyFG` anywhere. Both proofs are one application each — the content is the
join, not the argument.

The affine case is short because `AdicCompletion.idealOfDefinition I` is an `abbrev` for
`I.map (algebraMap R (AdicCompletion I R))` (`FormalSchemes/Completion.lean`), so its finite
generation is `hI.map _` with no intervening lemma. The glued case is short because the
`isFormalScheme` field of `completionTwoPatchFormalGlueData` already presents each patch as an
`Iso.refl` away from `formalCompletion`, so the `Nonempty (Y.toLocallyRingedSpace ≅ U i)` half of
the hypothesis needs no transport.

## Why this is not vacuous

`LocallyFG` is a `∀ x, ∃ …` statement, so it holds vacuously on an empty space — the same trap that
`FormalSchemes/CompletionCompact.lean` answers for `CompactSpace`. The closing `example` therefore
instantiates `Nonempty` **and** `LocallyFG` together at `R = ℤ`, `I = J = (2)`, `a = b = 2`, reusing
`completionTwoPatch_nonempty` from that file.

## Main results

* `AlgebraicGeometry.formalCompletion_locallyFG`: `Spf R^` is `LocallyFG`.
* `AlgebraicGeometry.completionTwoPatch_locallyFG`: the glued two-patch formal completion is
  `LocallyFG`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4, §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **The affine formal completion `Spf R^` is locally finitely generated.** It *is* a `Spf`, and
its ideal of definition `I·R^` is `I.map _` by definition, so finitely generated as soon as `I`
is. -/
theorem formalCompletion_locallyFG {R : Type u} [CommRing R] (I : Ideal R) (hI : I.FG) :
    (formalCompletion R I hI).LocallyFG :=
  haveI := AdicCompletion.isAdicRing_map I hI
  FormalScheme.locallyFG_Spf (hI.map _)

section TwoPatch

variable {A B : Type u} [CommRing A] [CommRing B] (I : Ideal A) (hI : I.FG) (a : A)
  (J : Ideal B) (hJ : J.FG) (b : B)
  (θ : Localization.Away a ≃+* Localization.Away b)
  (hθ : (I.map (algebraMap A (Localization.Away a))).map θ.toRingHom =
    J.map (algebraMap B (Localization.Away b)))

/-- **The glued two-patch formal completion is locally finitely generated**: it is glued from two
affine formal completions, each `LocallyFG` by `formalCompletion_locallyFG`. The two patches are
completions of *different* rings, so the index is split on. -/
theorem completionTwoPatch_locallyFG :
    (completionTwoPatch I hI a J hJ b θ hθ).LocallyFG :=
  FormalScheme.GlueData.gluedFormalScheme_locallyFG _ (by
    rintro ⟨_ | _⟩
    · exact ⟨formalCompletion A I hI, formalCompletion_locallyFG I hI, ⟨Iso.refl _⟩⟩
    · exact ⟨formalCompletion B J hJ, formalCompletion_locallyFG J hJ, ⟨Iso.refl _⟩⟩)

end TwoPatch

/-- **`LocallyFG` is not vacuous here.** At `R = ℤ`, `I = J = (2)`, `a = b = 2` and `θ` the
identity, the glued two-patch formal completion is nonempty *and* locally finitely generated. -/
example : Nonempty (completionTwoPatch (Ideal.span {(2 : ℤ)})
      (Submodule.fg_span (Set.finite_singleton _)) (2 : ℤ) (Ideal.span {(2 : ℤ)})
      (Submodule.fg_span (Set.finite_singleton _)) (2 : ℤ)
      (RingEquiv.refl _) (Ideal.map_id _)).toLocallyRingedSpace ∧
    (completionTwoPatch (Ideal.span {(2 : ℤ)})
      (Submodule.fg_span (Set.finite_singleton _)) (2 : ℤ) (Ideal.span {(2 : ℤ)})
      (Submodule.fg_span (Set.finite_singleton _)) (2 : ℤ)
      (RingEquiv.refl _) (Ideal.map_id _)).LocallyFG := by
  haveI : Nontrivial (ℤ ⧸ Ideal.span {(2 : ℤ)}) :=
    Ideal.Quotient.nontrivial_iff.mpr (by
      rw [Ne, Ideal.eq_top_iff_one, Ideal.mem_span_singleton]
      decide)
  exact ⟨completionTwoPatch_nonempty _ _ _ _ _ _ _ _, completionTwoPatch_locallyFG _ _ _ _ _ _ _ _⟩

end AlgebraicGeometry
