import FormalSchemes.ThreeChartCoverOpenSubscheme
import FormalSchemes.GeneralSeparatedHom

set_option linter.style.header false

/-!
# Every open formal subscheme of `Spf A` is separated over `Spf R` (EGA I §10.15)

`FormalSchemes.ThreeChartCoverOpenSubscheme` proves that the open formal subscheme of `Spf A` cut
out by `⨆ i, D(f_i)`, for a family `f : J → A`, is separated over `Spf R` — at an arbitrary index
type `J`, since issues 1988 and 1989 lifted the whole basic-open cover tower off `ULift (Fin 3)`.
This file takes the family to be **all of** the basic opens contained in a given open `U`, and the
supremum is then `U` itself, so *every* open of `Spf A` is separated.

`AlgebraicGeometry.FormalScheme.IsSeparatedOverSpf` is existential over an
`AffineChartedFibreDatumX` presentation, so a statement of this shape is only as inhabited as the
presentations that can be built. That is why this was out of reach until the tower became
index-general and not because the geometry is hard: an arbitrary open of `Spf A` needs one chart per
basic open inside it, and until issue 1989 the only basic-open presentation on the tree was indexed
by three.

## The route

The index type is `{g : A // D(g) ≤ U}`, a subtype of `A` and so in `Type u`, which is what
`AffineChartedFibreDatumX` asks of its index — that was measured before anything else was written
and it holds on the nose. The family is `Subtype.val`, and the three remaining steps are assembly:

* the supremum of the basic opens inside `U` is `U`, because the basic opens are a basis
  (`FormalSpectrum.exists_basicOpen_le`) — `FormalSpectrum.iSup_basicOpen_le_eq` below;
* so `ThreeChartCover.coverSubscheme` at that family is `Spf A` restricted to `U` — the two are
  the same term once the equality of opens is substituted, with no comparison isomorphism in the
  way;
* and `ThreeChartCover.coverSubscheme_isSeparatedOverSpf` is then the statement itself.

No new geometry is proved here and no chart data appears in either headline statement: they name
`A`, `I`, `U` and nothing else.

## What this does **not** close

`FormalSchemes.GeneralSeparatedHom`'s "What is *not* proved here" names three gaps — the
**refinement direction** of `AlgebraicGeometry.FormalScheme.IsSeparatedHom`, the **composition
law**, and **conservativity's hard direction**. **This file closes none of them.** What it supplies
is the per-chart input all three were missing: restricting a witness cover of the target along an
open `W` produces pieces that are opens of an affine rather than affines, and the per-chart clause
of `AlgebraicGeometry.FormalScheme.IsSeparatedHom` asks each piece to be separated over an affine.
Each of the three still needs its own assembly — the refinement direction has to build the
restricted cover and check its overlaps, not merely know that its pieces are separated — and each is
its own issue.

It is also only the **affine** case of the source-restriction principle that issue 1987 inventories
as statement (A): the presentation here is *constructed*, from basic opens of `Spf A`, rather than
obtained by restricting an arbitrary presentation. (A) at a general presented `X` needs a
basic-open refinement of an arbitrary chart family and is not attempted.

## Main definitions and results

* `FormalSpectrum.iSup_basicOpen_le_eq`: the basic opens contained in an open `U` of `Spf R` have
  supremum `U`.
* `AlgebraicGeometry.ThreeChartCover.isSeparatedOverSpf_restrictOpen_of_coverOpen_eq`: the transport
  that turns a covering identity `coverOpen I f = U` into separatedness of `Spf A` restricted
  to `U`.
* `AlgebraicGeometry.FormalScheme.isSeparatedOverSpf_restrictOpen_Spf`: **every open formal
  subscheme of `Spf A` is separated over `Spf R`.**
* `AlgebraicGeometry.FormalScheme.isSeparatedHom_restrictOpen_Spf`: the same in the
  `AlgebraicGeometry.FormalScheme.IsSeparatedHom` vocabulary, which is the form §10.15's open
  directions consume.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
* `FormalSchemes.ThreeChartCoverOpenSubscheme` — the same construction at a general family, and the
  three-index case it was written for.
-/

noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry FormalSpectrum

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The basic opens contained in `U` have supremum `U`.** One half is the defining property of
the index; the other is that the basic opens are a basis, in the neighbourhood form
`FormalSpectrum.exists_basicOpen_le`.

It is stated here rather than beside that lemma in `FormalSchemes.FormalSpectrum` because this file
is its only consumer, and that file is deep enough in the import graph that adding to it recompiles
most of the library. Move it there if a second consumer appears. -/
theorem iSup_basicOpen_le_eq (U : Opens (FormalSpectrum I)) :
    (⨆ g : {g : R // basicOpen I g ≤ U}, basicOpen I g.val) = U := by
  refine le_antisymm (iSup_le fun g => g.2) fun x hx => ?_
  obtain ⟨g, hxg, hgU⟩ := exists_basicOpen_le I U x hx
  exact Opens.mem_iSup.2 ⟨⟨g, hgU⟩, hxg⟩

end FormalSpectrum

namespace AlgebraicGeometry

namespace ThreeChartCover

variable {R : Type u} [CommRing R] (I : Ideal R) [TopologicalSpace R] [IsAdicRing I]
variable {A : Type u} [CommRing A] [Algebra R A]
variable [TopologicalSpace A] [IsAdicRing (I.map (algebraMap R A))]

/-- **A family whose basic opens cover `U` presents `U` as a separated open formal subscheme.**

`ThreeChartCover.coverSubscheme` is `Spf A` restricted to `ThreeChartCover.coverOpen I f`, so an
equality of opens is all that separates it from `Spf A` restricted to `U`; the hypothesis is
consumed by substitution and the conclusion is then
`ThreeChartCover.coverSubscheme_isSeparatedOverSpf`.

Stated with `f` and `U` independent, which is what makes the substitution legal: at the application
below the family is built *from* `U`, so the equality cannot be substituted there. -/
theorem isSeparatedOverSpf_restrictOpen_of_coverOpen_eq (hI : I.FG) {J : Type u} (f : J → A)
    (U : Opens (FormalScheme.Spf (I.map (algebraMap R A)))) (hU : coverOpen I f = U) :
    FormalScheme.IsSeparatedOverSpf hI
      ((FormalScheme.Spf (I.map (algebraMap R A))).restrictOpen (ambient_locallyFG I hI) U)
      ((FormalScheme.Spf (I.map (algebraMap R A))).restrictOpenι (ambient_locallyFG I hI) U ≫
        ambientStructMap I) := by
  subst hU
  exact coverSubscheme_isSeparatedOverSpf I f hI

end ThreeChartCover

namespace FormalScheme

variable {R : Type u} [CommRing R] (I : Ideal R) [TopologicalSpace R] [IsAdicRing I]
variable {A : Type u} [CommRing A] [Algebra R A]
variable [TopologicalSpace A] [IsAdicRing (I.map (algebraMap R A))]

/-- **Every open formal subscheme of `Spf A` is separated over `Spf R`** (EGA I §10.15), for an
arbitrary open `U` and with no presentation in the statement.

The presentation is built rather than restricted: the charts are the completed localizations
`A{1/g}` for **all** `g : A` with `D(g) ≤ U`, whose basic opens have supremum `U` by
`FormalSpectrum.iSup_basicOpen_le_eq`, so `ThreeChartCover.coverSubscheme` at that family is
`Spf A` restricted to `U`.

The structural morphism is the inclusion followed by the map of formal spectra induced by
`algebraMap R A`, which is `ThreeChartCover.ambientStructMap I` written out.

**This closes none of the three gaps** named under "What is *not* proved here" in
`FormalSchemes.GeneralSeparatedHom`; this file's own docstring says what it does supply them. -/
theorem isSeparatedOverSpf_restrictOpen_Spf (hI : I.FG)
    (U : Opens (FormalScheme.Spf (I.map (algebraMap R A)))) :
    FormalScheme.IsSeparatedOverSpf hI
      ((FormalScheme.Spf (I.map (algebraMap R A))).restrictOpen
        (locallyFG_Spf (hI.map (algebraMap R A))) U)
      ((FormalScheme.Spf (I.map (algebraMap R A))).restrictOpenι
          (locallyFG_Spf (hI.map (algebraMap R A))) U ≫
        locallyRingedSpaceMap I (I.map (algebraMap R A)) (algebraMap R A) Ideal.le_comap_map) :=
  ThreeChartCover.isSeparatedOverSpf_restrictOpen_of_coverOpen_eq I hI
    (Subtype.val : {g : A // basicOpen (I.map (algebraMap R A)) g ≤ U} → A) U
    (iSup_basicOpen_le_eq (I.map (algebraMap R A)) U)

/-- **The same statement in the `AlgebraicGeometry.FormalScheme.IsSeparatedHom` vocabulary**, which
is the form the open directions of §10.15 consume: the structural morphism of an arbitrary open
formal subscheme of `Spf A` is a separated morphism to `Spf R`.

Free from `FormalScheme.isSeparatedOverSpf_restrictOpen_Spf` through
`FormalScheme.isSeparatedHom_of_isSeparatedOverSpf`, which reads a separatedness-over-`Spf R`
statement as the one-chart case of the covered definition. -/
theorem isSeparatedHom_restrictOpen_Spf (hI : I.FG)
    (U : Opens (FormalScheme.Spf (I.map (algebraMap R A)))) :
    FormalScheme.IsSeparatedHom
      (FormalScheme.restrictOpen_locallyFG (FormalScheme.Spf (I.map (algebraMap R A)))
        (locallyFG_Spf (hI.map (algebraMap R A))) U)
      (locallyFG_Spf hI)
      (FormalScheme.Hom.mk
        ((FormalScheme.Spf (I.map (algebraMap R A))).restrictOpenι
            (locallyFG_Spf (hI.map (algebraMap R A))) U ≫
          locallyRingedSpaceMap I (I.map (algebraMap R A)) (algebraMap R A) Ideal.le_comap_map)) :=
  isSeparatedHom_of_isSeparatedOverSpf hI _ _
    (isSeparatedOverSpf_restrictOpen_Spf I hI U)

end FormalScheme

end AlgebraicGeometry

end
