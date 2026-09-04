import FormalSchemes.AwayCompletionRestrictUnique

set_option linter.style.header false

/-!
# The restriction of `O_{Spf R}` between two basic opens *is* the canonical map `R{1/f} →+* R{1/g}`

For an inclusion of basic opens `D(g) ⊆ D(f)` of `Spf (R, I)` the tree carries two ring maps
`R{1/f} →+* R{1/g}` built in completely different ways:

* `FormalSpectrum.basicOpenRes` (`FormalSchemes.BasicOpenRestriction`), the structure-sheaf
  restriction `Γ(D(f)) ⟶ Γ(D(g))` conjugated by `FormalSpectrum.sectionsBasicOpenEquiv` on both
  sides — a sheaf-theoretic object, defined through the limit presentation of `O_{Spf R}`;
* `FormalSpectrum.awayCompletionRestrict` (`FormalSchemes.AwayCompletionRestrict`), built from the
  algebra of the localizations: `f` becomes a unit modulo `I · R_g`, hence in the complete ring
  `R{1/g}`, and the map is the completed localization lift.

**They are equal**, for `I` finitely generated. That is
`FormalSpectrum.basicOpenRes_eq_awayCompletionRestrict` below, and it settles the question five
files on this tree state as their open follow-up; all five are corrected by this file's pull
request.

## The proof, and why it is short

Everything rests on one observation, which is this file's first section and is not about either map:
**a ring map `R{1/f} →+* R{1/g}` under `R` automatically carries the ideal of definition across.**
The ideal of definition of `R{1/f}` is not extra data — `FormalSpectrum.map_awayCompletionHom`
(`FormalSchemes.BasicOpenChart`) says it *is* the extension of `I` along the structure map
`FormalSpectrum.awayCompletionHom I f` — so `Ideal.map_map` rewrites its extension along any `F`
into the extension of `I` along `F.comp (awayCompletionHom I f)`, and a map under `R` has that
composite equal to `awayCompletionHom I g` by hypothesis. Hence
`FormalSpectrum.map_eq_of_comp_awayCompletionHom`, an equality of ideals and not merely a bound.

Feeding that to `FormalSpectrum.awayCompletionRestrict_unique`
(`FormalSchemes.AwayCompletionRestrictUnique`) removes its ideal hypothesis:
`FormalSpectrum.eq_awayCompletionRestrict_of_comp_awayCompletionHom` says a map under `R` **is**
`awayCompletionRestrict`, with no further hypothesis. `basicOpenRes` is a map under `R`, by
`FormalSpectrum.basicOpenRes_comp_awayCompletionHom`, which `FormalSchemes.BasicOpenRestriction`
proved; so it is that map.

The continuity that `FormalSpectrum.awayCompletion_hom_ext` needs is therefore free for maps under
`R`, and no level-by-level comparison of the two maps is required.
`FormalSchemes.BasicOpenRestriction` predicted that the residue would be a level-by-level
computation of the kind `FormalSpectrum.chartComponent_eq_awayCompletionChartEquiv`
(`FormalSchemes.BasicOpenImmersionAssembly`) carries out for the chart's sheaf component; that
prediction, and the paragraphs in four other files that record the identification as open, are
corrected here. Note what the short proof does *not* dispense with:
`FormalSpectrum.awayCompletion_hom_ext` itself, whose hypotheses genuinely are two, because from
two maps merely *agreeing* after `awayCompletionHom I f` neither ideal bound follows.

## Main results

* `FormalSpectrum.map_eq_of_comp_awayCompletionHom` and
  `FormalSpectrum.le_comap_of_comp_awayCompletionHom`: a ring map `R{1/f} →+* R{1/g}` under `R`
  carries the ideal of definition of `R{1/f}` **onto** that of `R{1/g}`. No `Ideal.FG`, no
  topology.
* `FormalSpectrum.eq_awayCompletionRestrict_of_comp_awayCompletionHom`: for `I` finitely generated,
  such a map is `FormalSpectrum.awayCompletionRestrict`.
* `FormalSpectrum.map_basicOpenRes`, `FormalSpectrum.le_comap_basicOpenRes`: the structure-sheaf
  restriction is a morphism of adic rings — the form
  `FormalSpectrum.locallyRingedSpaceMap` (`FormalSchemes.SpfMap`) consumes.
* `FormalSpectrum.basicOpenRes_eq_awayCompletionRestrict`: **the identification.**
* `FormalSpectrum.eq_basicOpenRes_of_comp_awayCompletionHom`: consequently the restriction is the
  unique map under `R`.
* `FormalSpectrum.basicOpenResMul_eq_awayCompletionMulHomLeft`: the nested case, against the map the
  gluing layer already uses.
* `FormalSpectrum.basicOpenRes_eq_mapCompletion`: the restriction is the completion of any map of
  localizations under `R`, when one exists — and by `FormalSpectrum.awayLocHom_ext` there is at most
  one, so that `φ` is not a choice.

## What is *not* proved here

**`Ideal.FG` is not removed.** The identification is stated for `hI : I.FG`, and has to be: its
right-hand side `awayCompletionRestrict` does not exist without it, since
`AdicCompletion.mapCompletion` (`FormalSchemes.Completion`) asks for a finitely generated ideal on
the target. The first section is `Ideal.FG`-free, and `map_basicOpenRes` — the statement that the
restriction is a morphism of adic rings — is too.

**Nothing here is a statement about a stalk.** No germ, colimit or stalk comparison appears below;
in particular nothing here says anything about `FormalSpectrum.IsStalkLimit`, which is undecided in
both directions and is not touched. The separation statement
`FormalSpectrum.exists_basicOpen_res_eq` (`FormalSchemes.StructureSheafStalkBasicOpen`) can now be
restated in completion form, but that upgrade belongs in its own file and is not attempted here.

**No transitivity or identity law is restated.** `FormalSpectrum.basicOpenRes_self` and
`FormalSpectrum.basicOpenRes_comp` (`FormalSchemes.BasicOpenRestriction`) already have them for the
sheaf side, hypothesis-free, and `FormalSpectrum.awayCompletionRestrict_self` and
`FormalSpectrum.awayCompletionRestrict_comp` (`FormalSchemes.AwayCompletionRestrictUnique`) have
them for the other; the identification below transports either set to the other on demand.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1 and §10.3.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (I : Ideal R)

/-!
### Maps under `R` carry the ideal of definition, for free
-/

/-- **There is at most one map of localizations under `R`.** Two ring maps
`Localization.Away f →+* Localization.Away g` agreeing after `algebraMap R (Localization.Away f)`
are equal, since `Localization.Away f` is a localization of `R` at `Submonoid.powers f`. So the
`φ` in `FormalSpectrum.basicOpenRes_eq_mapCompletion` below is not a choice — when such a map
exists at all, it is the map. -/
theorem awayLocHom_ext {f g : R} {φ ψ : Localization.Away f →+* Localization.Away g}
    (h : φ.comp (algebraMap R (Localization.Away f)) =
      ψ.comp (algebraMap R (Localization.Away f))) : φ = ψ :=
  IsLocalization.ringHom_ext (M := Submonoid.powers f) (S := Localization.Away f) h

/-- **A ring map `R{1/f} →+* R{1/g}` under `R` carries the ideal of definition onto the ideal of
definition.** The ideal of definition of `R{1/f}` is the extension of `I` along the structure map
`FormalSpectrum.awayCompletionHom I f` (`FormalSpectrum.map_awayCompletionHom`), so extending it
further along `F` extends `I` along the composite, which the hypothesis names.

This is why the continuity condition that `FormalSpectrum.awayCompletion_hom_ext`
(`FormalSchemes.AwayCompletionRestrictUnique`) asks for is free for a map under `R`: it is not an
extra property of `F` at all, but a property of the ideal of definition. -/
theorem map_eq_of_comp_awayCompletionHom {f g : R}
    {F : awayCompletion I f →+* awayCompletion I g}
    (hF : F.comp (awayCompletionHom I f) = awayCompletionHom I g) :
    (awayCompletionIdeal I f).map F = awayCompletionIdeal I g := by
  rw [← map_awayCompletionHom I f, Ideal.map_map, hF, map_awayCompletionHom]

/-- The contracted form of `FormalSpectrum.map_eq_of_comp_awayCompletionHom`. -/
theorem le_comap_of_comp_awayCompletionHom {f g : R}
    {F : awayCompletion I f →+* awayCompletion I g}
    (hF : F.comp (awayCompletionHom I f) = awayCompletionHom I g) :
    awayCompletionIdeal I f ≤ (awayCompletionIdeal I g).comap F :=
  Ideal.map_le_iff_le_comap.mp (map_eq_of_comp_awayCompletionHom I hF).le

/-- **A ring map `R{1/f} →+* R{1/g}` under `R` is `FormalSpectrum.awayCompletionRestrict`**, with no
hypothesis beyond `Ideal.FG` and the square. This is
`FormalSpectrum.awayCompletionRestrict_unique` (`FormalSchemes.AwayCompletionRestrictUnique`) with
its ideal hypothesis discharged by `FormalSpectrum.le_comap_of_comp_awayCompletionHom`; that
hypothesis is therefore redundant there, and every statement of that file which supplies both may
supply only the square. -/
theorem eq_awayCompletionRestrict_of_comp_awayCompletionHom {f g : R} (hI : I.FG)
    (hle : basicOpen I g ≤ basicOpen I f) {F : awayCompletion I f →+* awayCompletion I g}
    (hF : F.comp (awayCompletionHom I f) = awayCompletionHom I g) :
    F = awayCompletionRestrict I f g hI hle :=
  awayCompletionRestrict_unique I f g hI hle (le_comap_of_comp_awayCompletionHom I hF) hF

/-!
### The identification
-/

section Sheaf

variable [TopologicalSpace R] [IsAdicRing I]

/-- **The structure-sheaf restriction is a morphism of adic rings, on the nose**: it carries the
ideal of definition of `R{1/f}` onto that of `R{1/g}`, not merely into it. This is
`FormalSpectrum.map_eq_of_comp_awayCompletionHom` at the locality-free square
`FormalSpectrum.basicOpenRes_comp_awayCompletionHom` (`FormalSchemes.BasicOpenRestriction`); it
needs no `Ideal.FG`. -/
theorem map_basicOpenRes {f g : R} (hle : basicOpen I g ≤ basicOpen I f) :
    (awayCompletionIdeal I f).map (basicOpenRes I hle) = awayCompletionIdeal I g :=
  map_eq_of_comp_awayCompletionHom I (basicOpenRes_comp_awayCompletionHom I hle)

/-- The contracted form of `FormalSpectrum.map_basicOpenRes`, i.e. the continuity obligation that
`FormalSpectrum.locallyRingedSpaceMap` (`FormalSchemes.SpfMap`) consumes. -/
theorem le_comap_basicOpenRes {f g : R} (hle : basicOpen I g ≤ basicOpen I f) :
    awayCompletionIdeal I f ≤ (awayCompletionIdeal I g).comap (basicOpenRes I hle) :=
  le_comap_of_comp_awayCompletionHom I (basicOpenRes_comp_awayCompletionHom I hle)

/-- **The restriction `Γ(D(f)) ⟶ Γ(D(g))` of `O_{Spf R}` is the canonical map of completed
localizations.** For `I` finitely generated and `D(g) ⊆ D(f)`, the sheaf-theoretic
`FormalSpectrum.basicOpenRes` (`FormalSchemes.BasicOpenRestriction`) and the algebraically
constructed `FormalSpectrum.awayCompletionRestrict` (`FormalSchemes.AwayCompletionRestrict`) are
the same ring homomorphism.

Both are maps under `R` — `FormalSpectrum.basicOpenRes_comp_awayCompletionHom` and
`FormalSpectrum.awayCompletionRestrict_comp_awayCompletionHom` — and by
`FormalSpectrum.eq_awayCompletionRestrict_of_comp_awayCompletionHom` there is only one such map. -/
theorem basicOpenRes_eq_awayCompletionRestrict {f g : R} (hI : I.FG)
    (hle : basicOpen I g ≤ basicOpen I f) :
    basicOpenRes I hle = awayCompletionRestrict I f g hI hle :=
  eq_awayCompletionRestrict_of_comp_awayCompletionHom I hI hle
    (basicOpenRes_comp_awayCompletionHom I hle)

/-- **The restriction is the unique map under `R`**, stated on the sheaf side: any ring map
`R{1/f} →+* R{1/g}` restricting to `FormalSpectrum.awayCompletionHom I g` on the image of `R` is the
structure-sheaf restriction. -/
theorem eq_basicOpenRes_of_comp_awayCompletionHom {f g : R} (hI : I.FG)
    (hle : basicOpen I g ≤ basicOpen I f) {F : awayCompletion I f →+* awayCompletion I g}
    (hF : F.comp (awayCompletionHom I f) = awayCompletionHom I g) :
    F = basicOpenRes I hle :=
  (eq_awayCompletionRestrict_of_comp_awayCompletionHom I hI hle hF).trans
    (basicOpenRes_eq_awayCompletionRestrict I hI hle).symm

/-- **The nested case**: the restriction to `D(f * g)` is the completed further-localization map
`FormalSpectrum.awayCompletionMulHomLeft` (`FormalSchemes.BasicOpenChartOverlapLegs`), which the
gluing layer already consumes — `FormalSchemes.ChartSpfHomOverlap` and
`FormalSchemes.GeneralFibreProductExposeXAlgebraData` both use it. So this equation is what
connects the sheaf layer to the charts.

`FormalSpectrum.basicOpenResMul` needs no hypothesis on `I`, since `FormalSpectrum.basicOpen_mul`
supplies the inclusion; the equation needs `Ideal.FG` because its right-hand side does. -/
theorem basicOpenResMul_eq_awayCompletionMulHomLeft (f g : R) (hI : I.FG) :
    basicOpenResMul I f g = awayCompletionMulHomLeft I f g hI :=
  (eq_basicOpenRes_of_comp_awayCompletionHom I hI _
    (awayCompletionMulHomLeft_comp_awayCompletionHom I f g hI)).symm

/-- **The restriction is the completion of a map of localizations under `R`, whenever one exists.**
For a general basic inclusion of `Spf (R, I)` no such `φ` exists — the inclusion is a condition on
residues modulo `I` and does not put `g` in the radical of `f` — which is exactly why
`FormalSpectrum.awayCompletionRestrict` has to be built through
`RingSplit.adicAwayUnitEquiv'` (`FormalSchemes.AdicCompletionCongrLevel`). When one does exist it is
unique, by `FormalSpectrum.awayLocHom_ext`, and its completion is the restriction. -/
theorem basicOpenRes_eq_mapCompletion {f g : R} (hI : I.FG)
    (hle : basicOpen I g ≤ basicOpen I f) (φ : Localization.Away f →+* Localization.Away g)
    (hφ : (I.map (algebraMap R (Localization.Away f))).map φ ≤
      I.map (algebraMap R (Localization.Away g)))
    (hcomp : φ.comp (algebraMap R (Localization.Away f)) = algebraMap R (Localization.Away g)) :
    basicOpenRes I hle = AdicCompletion.mapCompletion φ hφ (hI.map _) :=
  (basicOpenRes_eq_awayCompletionRestrict I hI hle).trans
    (awayCompletionRestrict_eq_mapCompletion I f g hI hle φ hφ hcomp).symm

end Sheaf

end FormalSpectrum
