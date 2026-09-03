/-
The subsumption claims of `docs/signature-census-concl.md`, as elaborated terms.

Run from the repository root, after a full `lake build`:

    lake env lean scripts/census_concl_checks.lean

Silence is the result: every `example` below restates one declaration's statement verbatim and
closes it with a *different* declaration of this tree applied to its own arguments.  An asserted
subsumption is not a finding, so the census that produced these pairs asserts none — this file is
where each claim is checked.

The pairs come from the `--key concl` half of `scripts/signature_scan.py`'s census: the 91
cross-module theorem buckets on master at e0fd2e8.  Each section names the bucket it came
from, in the numbering of `docs/signature-census-concl.md`.  That numbering is the tool's own
ordering and renumbers when master grows a bucket, so re-derive it rather than trusting a
`B`-number from an older revision.  A bucket is a *question*; what survives reading it is here.

This file is not part of the library and nothing imports it.  It is kept next to the probe that
found the pairs so that a successor can re-check the claims after the tree moves, rather than
re-reading the census to find out whether they still hold.

One trap, walked into once and recorded here so that it is not walked into twice.  Inside a
`variable` block an `example` silently acquires whatever section binders its *proof term* needs,
so "restates the declaration's type verbatim" is not visible in the source: a binder the target
does **not** have can be added without the source showing it, and no linter reports an added
binder — only a dropped one.  An earlier revision of this file claimed
`FormalSpectrum.hasAffineThickenings_opensRange_of_range_eq_basicOpenChart` was subsumed on the
strength of such an `example`; the target is `omit`-ted of four instances the subsuming form
needs, so the claim was false and the check could not see it.  Verbatim-ness has to be checked
against the type Lean stores for the target, printed from the environment, not against the source
of the `example`.  Where the pairs are new and the risk is live — the #519 section below — every
binder is therefore spelled out and no `variable` block is in scope, so an added instance shows up
as a diff.
-/
import FormalSchemes

universe u

open CategoryTheory Topology AlgebraicGeometry

/-! ## Undeclared subsumptions

Nothing on the tree records these; each is a row's worth of work.  -/

/-- **B27.** `FormalSpectrum.isUnit_stalk_of_isUnit_zero` is
`FormalSpectrum.isUnit_of_isUnit_stalkProj` at `n = 0`. -/
example {R : Type u} [CommRing R] (I : Ideal R) (x : FormalSpectrum I)
    (a : (FormalSpectrum.structureSheaf I).presheaf.stalk x)
    (h : IsUnit ((FormalSpectrum.stalkProj I x 0).hom a)) : IsUnit a :=
  FormalSpectrum.isUnit_of_isUnit_stalkProj I x 0 a h

/-- **B62.** `IsPrecomplete.of_cofinal`'s two containments are a `Ideal.IsCofinal`, so it is
`IsPrecomplete.of_isCofinal`.  The general form is moreover polymorphic in the module's universe
and this one is not. -/
example {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M] {K I : Ideal R}
    (hle : K ≤ I) {c : ℕ} (hc : I ^ c ≤ K) [IsPrecomplete I M] : IsPrecomplete K M :=
  IsPrecomplete.of_isCofinal ⟨⟨1, by simpa using hle⟩, ⟨c, hc⟩⟩

/-- **B63.** `AlgebraicGeometry.IsTopologicallyFiniteType.fg` is
`IsTopologicallyFiniteType.fg_of_presentation` at the presentation the tf-type witness carries;
the latter does not use its surjectivity.

Row 1544 acted on this. When the bucket was read, the general form sat in the
RestrictedPowerSeries namespace in `FormalSchemes.TopFiniteTypeTrans`, which the special form
cannot see; it now lives beside its own only input,
`IsTopologicallyFiniteType.map_eq_of_presentation` (`FormalSchemes.TopFiniteType`), where the
special form can and does cite it. The bucket survives — two declarations in two modules still
conclude that the ideal is finitely generated — but it is now a *declared* pair. -/
example {R : Type u} [CommRing R] {I : Ideal R} {A : Type u} [CommRing A] [Algebra R A]
    {L : Ideal A} (h : IsTopologicallyFiniteType R I A L) (hI : I.FG) : L.FG := by
  obtain ⟨n, ψ, _, hψ⟩ := h
  exact IsTopologicallyFiniteType.fg_of_presentation hI hψ

/-- **B31.** `CompletedTensorProduct.idealOfDefinition_fg` and
`CompletedTensorAwayInterchange.idealOfDefinition_fg` are one statement; the first carries six
instance binders it does not use. -/
example {R : Type u} [CommRing R] {I : Ideal R} {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace A]
    [IsAdicRing (Ideal.map (algebraMap R A) I)] [TopologicalSpace B]
    [IsAdicRing (Ideal.map (algebraMap R B) I)]
    [TopologicalSpace (CompletedTensorProduct R I A B)]
    [IsAdicRing (CompletedTensorProduct.idealOfDefinition R I A B)] (hI : I.FG) :
    (CompletedTensorProduct.idealOfDefinition R I A B).FG :=
  CompletedTensorAwayInterchange.idealOfDefinition_fg I hI

/-- **B06.** A closed embedding has closed range, so
`AlgebraicGeometry.FormalScheme.isClosedImmersion_of_isSplitMono` is
`AlgebraicGeometry.FormalScheme.isClosedImmersion_of_isClosed_range_of_isSplitMono`. -/
example {X Y : FormalScheme} (f : X ⟶ Y) [IsSplitMono f]
    (h : IsClosedEmbedding ⇑(ConcreteCategory.hom (FormalScheme.Hom.toLRSHom f).base)) :
    FormalScheme.IsClosedImmersion f :=
  FormalScheme.isClosedImmersion_of_isClosed_range_of_isSplitMono f h.isClosed_range

/-- **B06.** The same for the retraction form. -/
example {X Y : FormalScheme} (f : X ⟶ Y) (r : Y ⟶ X) (hr : f ≫ r = 𝟙 X)
    (h : IsClosedEmbedding ⇑(ConcreteCategory.hom (FormalScheme.Hom.toLRSHom f).base)) :
    FormalScheme.IsClosedImmersion f :=
  FormalScheme.isClosedImmersion_of_isClosed_range_of_retraction f r hr h.isClosed_range

/-! ## Declared subsumptions

A docstring on one of the two members already names the other.  Checked because a declared
subsumption is still an asserted one.  -/

/-- **B46.** `CompletedTensorProduct.codiagonal_le_comap'` needs four of the eight instance
binders `CompletedTensorProduct.codiagonal_le_comap` carries. -/
example {R : Type u} [CommRing R] {I : Ideal R} {A : Type u} [CommRing A] [Algebra R A]
    [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace A]
    [IsAdicRing (I.map (algebraMap R A))]
    [TopologicalSpace (CompletedTensorProduct R I A A)]
    [IsAdicRing (CompletedTensorProduct.idealOfDefinition R I A A)] (hI : I.FG) :
    CompletedTensorProduct.idealOfDefinition R I A A ≤
      (I.map (algebraMap R A)).comap (CompletedTensorProduct.codiagonal R I A) :=
  CompletedTensorProduct.codiagonal_le_comap' hI

/-- **B50.** `IsAdicRing` extends `IsAdicComplete`, so
`RestrictedLaurentSeries.algebraMap_injective` is
`RestrictedLaurentSeries.algebraMap_injective_of_isAdicComplete`. -/
example {R : Type u} [CommRing R] {I : Ideal R} [TopologicalSpace R] [IsAdicRing I] :
    Function.Injective (algebraMap R (RestrictedLaurentSeries R I)) :=
  haveI : IsAdicComplete I R := ‹IsAdicRing I›.toIsAdicComplete
  RestrictedLaurentSeries.algebraMap_injective_of_isAdicComplete I

/-- **B08.** Conservativity's extra hypothesis is redundant, as both docstrings say. -/
example {R : Type u} [CommRing R] [TopologicalSpace R] {I : Ideal R} [IsAdicRing I]
    {X : FormalScheme} {f : X ⟶ FormalScheme.Spf I} (hI : I.FG)
    (_ : FormalScheme.IsAdicOpenImmersionProperty I) (hf : FormalScheme.IsTopFiniteTypeHom f) :
    FormalScheme.IsRelativelyTopFiniteType R I f :=
  hf.isRelativelyTopFiniteType_of_fg hI

/-- **B34.** The same at the `Iff`. -/
example {R : Type u} [CommRing R] [TopologicalSpace R] {I : Ideal R} [IsAdicRing I]
    {X : FormalScheme} (hI : I.FG) (_ : FormalScheme.IsAdicOpenImmersionProperty I)
    (f : X ⟶ FormalScheme.Spf I) :
    FormalScheme.IsRelativelyTopFiniteType R I f ↔ FormalScheme.IsTopFiniteTypeHom f :=
  FormalScheme.isRelativelyTopFiniteType_iff_isTopFiniteTypeHom_of_fg hI f

/-- **B09.** Cofinal ideals have equal radicals, so the cofinality form of conservativity's affine
step is the containment form. -/
example {R : Type u} [CommRing R] {I : Ideal R} [TopologicalSpace R] [IsAdicRing I] {B : Type u}
    [CommRing B] [TopologicalSpace B] {J : Ideal B} [IsAdicRing J] [Algebra R B]
    (hI : I.FG) (hJ : J.FG) (m : FormalSpectrum.locallyRingedSpaceObj J ⟶
      FormalSpectrum.locallyRingedSpaceObj I) [LocallyRingedSpace.IsOpenImmersion m]
    (halg : algebraMap R B = FormalSpectrum.globalSectionsMap I J m)
    (hcof : J.IsCofinal (Ideal.map (algebraMap R B) I)) :
    IsTopologicallyFiniteType R I B (Ideal.map (algebraMap R B) I) :=
  IsTopologicallyFiniteType.of_openImmersion_of_le_radical hI hJ m halg
    (hcof.radical_eq ▸ Ideal.le_radical)

/-- **B39.** Large-period freeness is the `n ≠ 0` statement restricted. -/
example (R : Type u) [CommRing R] (I : Ideal R) (q : R) [TopologicalSpace R] [IsAdicRing I]
    [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG) {n : ℤ} (hItop : I ≠ ⊤) (h0 : n ≠ 0)
    (_ : n ≠ 1) (_ : n ≠ -1) : tateShiftAut R I q hq hI ^ n ≠ 1 :=
  tateShiftAut_zpow_ne_one_of_ne_zero R I q hq hI hItop h0

/-- **B29.** The primed form has the hypothesis discharged. -/
example (R : Type u) [CommRing R] (I : Ideal R) (q : R) [TopologicalSpace R] [IsAdicRing I]
    [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)
    (_ : IsTateInvNodeChartLegContinuous R I q hq hI) :
    (tateInvNodeChartAwaySubring R I q hq hI).IsAdicallyClosed
      (FormalSpectrum.awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q)) :=
  isAdicallyClosed_tateInvNodeChartAwaySubring' R I q hq hI

/-- **B30.** The same one rung up. -/
example (R : Type u) [CommRing R] (I : Ideal R) (q : R) [TopologicalSpace R] [IsAdicRing I]
    [IsNoetherianRing R] (hq : q ∈ I) (hI : I.FG)
    (_ : (tateInvNodeChartAwaySubring R I q hq hI).IsAdicallyClosed
      (FormalSpectrum.awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q))) :
    (tateInvNodeChartAwaySubring R I q hq hI).IsInducedPrecomplete
      (FormalSpectrum.awayCompletionIdeal (annulusIdealOfDefinition R I q)
        (annulusNodeChartCoord R I q)) :=
  isInducedPrecomplete_tateInvNodeChartAwaySubring' R I q hq hI

/-! ### B20 and B55: two subsumptions inside the class row 1538 nominated as noise

Both were filed **N** in this document's first draft and corrected in review.  Both relations are
declared in a docstring, so neither carries a row; they are here because the census claims them.
-/

/-- **B55.** `IsAdic.of_le_of_pow_le`'s `I ≤ J` and `J ^ n ≤ I` together are an
`Ideal.IsCofinal`, so it is `Ideal.IsCofinal.isAdic`. -/
example {R : Type u} [CommRing R] {I J : Ideal R} [TopologicalSpace R] [IsTopologicalRing R]
    (hI : IsAdic I) (hle : I ≤ J) {n : ℕ} (hn : J ^ n ≤ I) : IsAdic J :=
  Ideal.IsCofinal.isAdic ⟨⟨1, by simpa using hle⟩, ⟨n, hn⟩⟩ hI

/-- **B20.** `IsHausdorff.eq_of_mk_pow_eq` is `IsHausdorff.eq_of_mk_pow_succ_eq` reindexed. -/
example {S : Type u} [CommRing S] (I : Ideal S) [IsHausdorff I S] {x y : S}
    (h : ∀ n : ℕ, Ideal.Quotient.mk (I ^ n) x = Ideal.Quotient.mk (I ^ n) y) : x = y :=
  IsHausdorff.eq_of_mk_pow_succ_eq I fun n => h (n + 1)

/-! ### B09 / B13 / B17: the five declarations PR #519 subsumed

Each `example` restates an older declaration's type verbatim and closes it with the unconditional
form from `FormalSchemes.AffineThickeningsOpenImmersion`.  The dropped binders show up as
unused-variable warnings, and those warnings are the finding; the linter is switched off in this
section so that silence remains this file's result.  Row 1547 carries the repair.

No `variable` block is in scope here, deliberately: see the note in this file's header.  Every
binder is spelled out, so a binder the target does not have cannot be added without the source
saying so.  The fourth of #519's unconditional results, `hasAffineThickenings_opensRange`,
subsumes nothing and has no `example` here — its bucket B47 pairs it with a statement that is
`omit`-ted of `[TopologicalSpace R] [IsAdicRing I] [TopologicalSpace B] [IsAdicRing J]`, all four
of which it needs, so the two are incomparable and the bucket is F.
-/

section Subsumed519

set_option linter.unusedVariables false

open FormalSpectrum

/-- **B17.** `le_radical_map_of_range_eq_basicOpenChart` is `le_radical_map_of_openImmersion`
with `f` and the range condition deleted. -/
example {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
    {B : Type u} [CommRing B] [TopologicalSpace B] (J : Ideal B) [IsAdicRing J]
    (m : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    [LocallyRingedSpace.IsOpenImmersion m] [Algebra R B]
    (halg : algebraMap R B = globalSectionsMap I J m) (hI : I.FG) (f : R)
    (hrange : Set.range m.base = Set.range (basicOpenChart I f).base) :
    J ≤ (I.map (algebraMap R B)).radical :=
  le_radical_map_of_openImmersion I J m halg hI

/-- **B17.** So is `le_radical_map_of_range_eq_univ`. -/
example {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
    {B : Type u} [CommRing B] [TopologicalSpace B] (J : Ideal B) [IsAdicRing J]
    (m : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    [LocallyRingedSpace.IsOpenImmersion m] [Algebra R B]
    (halg : algebraMap R B = globalSectionsMap I J m) (hI : I.FG)
    (hrange : Set.range m.base = Set.univ) :
    J ≤ (I.map (algebraMap R B)).radical :=
  le_radical_map_of_openImmersion I J m halg hI

/-- **B13.** `isCofinal_map_of_range_eq_basicOpenChart` is
`isCofinal_map_of_openImmersion` with `f` and the range condition deleted. -/
example {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
    {B : Type u} [CommRing B] [TopologicalSpace B] (J : Ideal B) [IsAdicRing J] [Algebra R B]
    (hI : I.FG) (hJ : J.FG) (m : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    [LocallyRingedSpace.IsOpenImmersion m]
    (halg : algebraMap R B = globalSectionsMap I J m) (f : R)
    (hrange : Set.range m.base = Set.range (basicOpenChart I f).base) :
    Ideal.IsCofinal J (I.map (algebraMap R B)) :=
  isCofinal_map_of_openImmersion I J m halg hI hJ

/-- **B09.** `IsTopologicallyFiniteType.of_openImmersion_range_eq_univ` is
`IsTopologicallyFiniteType.of_openImmersion` with the range condition deleted. -/
example {R : Type u} [CommRing R] {I : Ideal R} [TopologicalSpace R] [IsAdicRing I]
    {B : Type u} [CommRing B] [TopologicalSpace B] {J : Ideal B} [IsAdicRing J] [Algebra R B]
    (hI : I.FG) (hJ : J.FG) (m : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    [LocallyRingedSpace.IsOpenImmersion m]
    (halg : algebraMap R B = globalSectionsMap I J m)
    (hrange : Set.range m.base = Set.univ) :
    IsTopologicallyFiniteType R I B (I.map (algebraMap R B)) :=
  IsTopologicallyFiniteType.of_openImmersion hI hJ m halg

/-- **B09.** So is `IsTopologicallyFiniteType.of_openImmersion_range_eq_basicOpen`. -/
example {R : Type u} [CommRing R] {I : Ideal R} [TopologicalSpace R] [IsAdicRing I]
    {B : Type u} [CommRing B] [TopologicalSpace B] {J : Ideal B} [IsAdicRing J] [Algebra R B]
    (hI : I.FG) (hJ : J.FG) (m : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    [LocallyRingedSpace.IsOpenImmersion m]
    (halg : algebraMap R B = globalSectionsMap I J m) (f : R)
    (hrange : Set.range m.base = Set.range (basicOpenChart I f).base) :
    IsTopologicallyFiniteType R I B (I.map (algebraMap R B)) :=
  IsTopologicallyFiniteType.of_openImmersion hI hJ m halg

end Subsumed519

/-! ### B02: the separatedness ladder over `AlgebraicGeometry.FormalScheme.affineCover` -/

namespace AlgebraicGeometry.BothChartedFibreDatumXY

open CompletedTensorAwayInterchange CompletedTensorProduct FormalSpectrum

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable [TopologicalSpace R] [IsAdicRing I]
variable {BX : Type u} [CommRing BX] [Algebra R BX]
variable (DX : AffineChartedFibreDatumX R I hI BX)
variable
  (σX : letI := DX.commRing; letI := DX.algebra;
    ∀ (i i' i'' : DX.J), i ≠ i' → i ≠ i'' → i' ≠ i'' →
    (awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i i' * DX.g i i'') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (DX.A i'))) (DX.g i' i'' * DX.g i' i)))
  (hστX : letI := DX.commRing; letI := DX.algebra;
    ∀ (i i' i'' : DX.J) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
    (σX i i' i'' h1 h2 h3).symm.toAlgHom.comp (furtherLocSnd I (DX.g i' i'') (DX.g i' i) hI) =
      (furtherLocFst I (DX.g i i') (DX.g i i'') hI).comp (DX.τ i i' h1).symm.toAlgHom)
  (hσcX : letI := DX.commRing; letI := DX.algebra;
    ∀ (i i' i'' : DX.J) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
    (σX i i' i'' h1 h2 h3).trans ((σX i' i'' i h3 h1.symm h2.symm).trans
      (σX i'' i i' h2.symm h3.symm h1)) =
      AlgEquiv.refl (R := R)
        (A₁ := awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i i' * DX.g i i'')))

/-- `AlgebraicGeometry.BothChartedFibreDatumXY.isSeparated_of_diagonal_cover` is
`AlgebraicGeometry.BothChartedFibreDatumXY.isSeparated_of_openCover` at
`AlgebraicGeometry.FormalScheme.affineCover`. -/
example
    (hbase : ∀ j, IsClosedEmbedding (Set.restrictPreimage
      (Set.range (((diagonalDatum DX σX hστX hσcX).generalFibreProduct.affineCover.map
        j).toLRSHom.base))
      ⇑(schemeDiagonal' DX σX hστX hσcX).toLRSHom.base))
    (hstalk : ∀ y,
      Function.Surjective ⇑((schemeDiagonal' DX σX hστX hσcX).toLRSHom.stalkMap y).hom) :
    IsSeparated DX σX hστX hσcX :=
  isSeparated_of_openCover DX σX hστX hσcX
    (diagonalDatum DX σX hστX hσcX).generalFibreProduct.affineCover hbase hstalk

/-- The same for the stalk-free form. -/
example
    (hbase : ∀ j, IsClosedEmbedding (Set.restrictPreimage
      (Set.range (((diagonalDatum DX σX hστX hσcX).generalFibreProduct.affineCover.map
        j).toLRSHom.base))
      ⇑(schemeDiagonal' DX σX hστX hσcX).toLRSHom.base)) :
    IsSeparated DX σX hστX hσcX :=
  isSeparated_of_openCover_base DX σX hστX hσcX
    (diagonalDatum DX σX hστX hσcX).generalFibreProduct.affineCover hbase

/-- The same for the closed-range form. -/
example
    (hrange : ∀ j, IsClosed (Set.range (Set.restrictPreimage
      (Set.range (((diagonalDatum DX σX hστX hσcX).generalFibreProduct.affineCover.map
        j).toLRSHom.base))
      ⇑(schemeDiagonal' DX σX hστX hσcX).toLRSHom.base))) :
    IsSeparated DX σX hστX hσcX :=
  isSeparated_of_openCover_isClosed_range DX σX hστX hσcX
    (diagonalDatum DX σX hστX hσcX).generalFibreProduct.affineCover hrange

end AlgebraicGeometry.BothChartedFibreDatumXY
