import FormalSchemes.GlobalSectionsHom
import FormalSchemes.OpenCoverGlueMorphisms
import FormalSchemes.OpenImmersionSourceFormalScheme

set_option linter.style.header false

/-!
# Gluing a morphism into a formal spectrum out of a homomorphism on global sections

`FormalSchemes/GlobalSectionsHom.lean` (issue 920) takes the **faithfulness** half of
EGA I, 10.4.6 over a non-affine source: a morphism `X ⟶ Spf R` is determined by the induced
`FormalSpectrum.globalSectionsHom`, the ring homomorphism `R →+* Γ(X, 𝒪_X)`. This file takes the
first step of the **fullness** half, in the other direction: out of a homomorphism
`ψ : R →+* Γ(X, 𝒪_X)` it builds an actual morphism `X ⟶ Spf R`.

The construction is the expected one. On each affine chart, `ψ` restricts to a homomorphism into
the chart's ring, and `FormalSpectrum.locallyRingedSpaceMap` turns that into a morphism
`Spf A_x ⟶ Spf R`. The chart morphisms are then glued by
`AlgebraicGeometry.FormalScheme.OpenCover.glueMorphisms`, whose hypothesis is agreement on the
pairwise overlaps `𝒰.obj i ×_X 𝒰.obj j`. Those overlaps are **not affine**, so the affine
uniqueness statement does not apply to them directly; what discharges the hypothesis is issue 920's
own `hom_ext_of_globalSectionsHom`, run one level down on an affine cover of the overlap. That the
overlap is again a formal scheme, and a locally finitely generated one, is
`AlgebraicGeometry.FormalScheme.OpenCover.overlapFormalScheme` and
`overlapFormalScheme_locallyFG` (`FormalSchemes.OpenImmersionSourceFormalScheme`).

## Scope: what is proved about the glued morphism, and what is not

The glued morphism is characterised **chart by chart**: `cmap_comp_glueHomOfGlobalSectionsHom`
says it restricts to the given family, and `comp_globalSectionsHom_glueHomOfGlobalSectionsHom`
says that after restricting to any chart it induces `ψ`.

It is **not** proved here that `globalSectionsHom I X f = ψ` on the nose. That is a genuinely
different step: passing from per-chart agreement to global agreement is injectivity of
`Γ(X, ⊤) → ∏ Γ(U_i, ⊤)`, i.e. the sheaf axiom for the cover, together with an identification of
`(𝒰.cmap i).c` at `⊤` with restriction to `U_i` followed by the open-immersion comparison
isomorphism. Neither ingredient is used anywhere below, and stating a per-chart result honestly is
better than packaging a bijection that is not proved.

The continuity hypotheses are inherited, not incidental. `FormalSpectrum.spfGammaEquiv` inverts
`Spf` only on the continuity-restricted subtype — continuity of the global-sections map is not
automatic for a morphism of locally ringed spaces between formal spectra — so both the
construction of the chart morphisms and the overlap comparison need it, chart by chart. See the
scope note of `FormalSchemes.GlobalSectionsHom` for the same point on the faithfulness side.

## Main definitions and results

* `AlgebraicGeometry.FormalScheme.chartHom`: the homomorphism `R →+* A_x` that restricting `ψ` to
  the chart at `x` amounts to.
* `AlgebraicGeometry.FormalScheme.chartMap`: the resulting morphism `Spf A_x ⟶ Spf R`, and
  `globalSectionsHom_chartMap`: its global-sections homomorphism is that restriction of `ψ`.
* `AlgebraicGeometry.FormalScheme.OpenCover.pullback_fst_comp_eq_snd_comp`: **the overlap
  agreement**, the hypothesis of `glueMorphisms`, for a family of morphisms that all restrict a
  common `ψ`.
* `AlgebraicGeometry.FormalScheme.OpenCover.glueHomOfGlobalSectionsHom`: the glued morphism, with
  `cmap_comp_glueHomOfGlobalSectionsHom` and
  `comp_globalSectionsHom_glueHomOfGlobalSectionsHom`.
* `AlgebraicGeometry.FormalScheme.OpenCover.overlapChart`: a chosen finitely generated affine chart
  on an overlap. The affine charts of the overlaps are *supplied* to the constructions above rather
  than chosen internally, for the reason `OpenCover.ofAffineCharts` exists at all: the continuity
  hypotheses have to be able to name them. `overlapChart` is available for a caller who has nothing
  better to supply.
* `AlgebraicGeometry.FormalScheme.ofAffineCharts_obj_locallyFG` and
  `AlgebraicGeometry.FormalScheme.chartOverlap`: the two pieces of vocabulary the assembly below
  needs — every piece of `OpenCover.ofAffineCharts` is locally finitely generated, and the overlap
  of two of them is a formal scheme.
* `AlgebraicGeometry.FormalScheme.homOfGlobalSectionsHom`: the whole construction over an arbitrary
  supplied family of affine charts, together with `chart_comp_homOfGlobalSectionsHom` and
  `comp_globalSectionsHom_homOfGlobalSectionsHom`.
* `AlgebraicGeometry.FormalScheme.overlapChartOf` and
  `AlgebraicGeometry.FormalScheme.SpfHomContinuity`: given a supplied family of affine charts, the
  charts on its overlaps are canonical — `AlgebraicGeometry.FormalScheme.OpenCover.overlapChart`
  at that cover — so the only arguments of
  `AlgebraicGeometry.FormalScheme.homOfGlobalSectionsHom` left carrying content are its three
  continuity families.
  `AlgebraicGeometry.FormalScheme.SpfHomContinuity` bundles those three, and
  `AlgebraicGeometry.FormalScheme.homOfSpfHomContinuity` is the construction over it, with
  `AlgebraicGeometry.FormalScheme.chart_comp_homOfSpfHomContinuity`. **The chart family stays
  supplied**: a caller who builds one
  to order — from a neighbourhood basis recording the bound, as
  `AlgebraicGeometry.FormalScheme.AdicOverBaseLocallyFG` (`FormalSchemes.AdicOverBaseChart`) does —
  states the three conditions at it with nothing restated.
* `AlgebraicGeometry.FormalScheme.LocallyFG.overlapChart` and
  `AlgebraicGeometry.FormalScheme.LocallyFG.SpfHomContinuity`: the specialisation to the charts
  `AlgebraicGeometry.FormalScheme.LocallyFG` chooses, with
  `AlgebraicGeometry.FormalScheme.homOfGlobalSectionsHomOfLocallyFG`. Offered, **not
  recommended** — `AlgebraicGeometry.FormalScheme.LocallyFG` is a `Prop` and its
  `AlgebraicGeometry.FormalScheme.LocallyFG.chart` is `Exists.choose`, so proof irrelevance makes
  that family
  the only one reachable through the specialisation, and continuity at it is the shape
  `FormalSchemes.GeneralFibreProductLiftAdic` records as unreachable (issues 460/468/472/487, 805).
  Its docstring carries the warning and names the reachable form.
* `AlgebraicGeometry.FormalScheme.hom_ext_of_chart_comp`: the matching uniqueness statement — a
  morphism into `Spf R` is determined by its restrictions to the charts. This is *not* a weakening
  of `hom_ext_of_globalSectionsHom`: that one compares global-sections homomorphisms and needs
  continuity, this one compares the restrictions themselves and needs none.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4 (10.4.6).
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry CategoryTheory.Limits
open FormalSpectrum

namespace AlgebraicGeometry.FormalScheme

section ChartMap

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable {X : FormalScheme.{u}} (charts : ∀ x : X, AffineChart X x)
variable (ψ : R →+* X.presheaf.obj (op (⊤ : Opens X)))

/-- **The chart-restriction of `ψ`, read as a homomorphism of rings.** Restricting
`ψ : R →+* Γ(X, 𝒪_X)` along the chart at `x` lands in `Γ(Spf A_x)`, which is `A_x` by
`FormalSpectrum.globalSectionsEquiv` (EGA I, 10.1.3).

This does not mention `I`: the ideal of definition involved is the chart's. -/
def chartHom (x : X) : R →+* (charts x).R :=
  (globalSectionsEquiv (charts x).I).toRingHom.comp
    (((charts x).map.c.app (op (⊤ : Opens X))).hom.comp ψ)

/-- **The morphism of formal spectra a chart-restriction of `ψ` induces**, given that the
restriction is continuous at that chart. -/
def chartMap (x : X) (h : I ≤ (charts x).I.comap (chartHom charts ψ x)) :
    (FormalScheme.Spf (charts x).I).toLocallyRingedSpace ⟶ locallyRingedSpaceObj I :=
  locallyRingedSpaceMap I (charts x).I (chartHom charts ψ x) h

/-- **`chartMap` induces the chart-restriction of `ψ` on global sections.** This is what makes the
family of chart morphisms a family of restrictions of one global object, which is in turn what
makes them agree on overlaps (`OpenCover.pullback_fst_comp_eq_snd_comp`). -/
theorem globalSectionsHom_chartMap (x : X)
    (h : I ≤ (charts x).I.comap (chartHom charts ψ x)) :
    globalSectionsHom I (FormalScheme.Spf (charts x).I).toLocallyRingedSpace
        (chartMap I charts ψ x h) =
      ((charts x).map.c.app (op (⊤ : Opens X))).hom.comp ψ := by
  have h1 : globalSectionsMap I (charts x).I (chartMap I charts ψ x h) = chartHom charts ψ x :=
    globalSectionsMap_locallyRingedSpaceMap I (charts x).I _ h
  -- On an affine source `globalSectionsMap` is `globalSectionsHom` read through `Γ(Spf A) ≃+* A`,
  -- so `h1` becomes an equation with a common `globalSectionsEquiv` factor on the left.
  rw [globalSectionsMap_eq_globalSectionsHom] at h1
  refine RingHom.ext fun r => (globalSectionsEquiv (charts x).I).injective ?_
  exact congrArg (fun φ : R →+* (charts x).R => φ r) h1

end ChartMap

namespace OpenCover

variable {X : FormalScheme.{u}} (𝒰 : X.OpenCover)

/-- **A chosen finitely generated affine chart on the `(i, j)` overlap** of a cover whose `i`-th
piece is locally finitely generated. The overlap is again a locally finitely generated formal
scheme (`overlapFormalScheme_locallyFG`), so `LocallyFG.chart` applies to it. -/
def overlapChart (i j : 𝒰.J) (hi : (𝒰.obj i).LocallyFG)
    (x : 𝒰.overlapFormalScheme i j hi) : AffineChart (𝒰.overlapFormalScheme i j hi) x :=
  (𝒰.overlapFormalScheme_locallyFG i j hi).chart x

/-- The ideal of definition of `overlapChart` is finitely generated. -/
theorem overlapChart_fg (i j : 𝒰.J) (hi : (𝒰.obj i).LocallyFG)
    (x : 𝒰.overlapFormalScheme i j hi) : (𝒰.overlapChart i j hi x).I.FG :=
  (𝒰.overlapFormalScheme_locallyFG i j hi).fg_chart x

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable (k : ∀ l, (𝒰.obj l).toLocallyRingedSpace ⟶ locallyRingedSpaceObj I)
variable (ψ : R →+* X.presheaf.obj (op (⊤ : Opens X)))

/-- **Agreement on an overlap.** Two members of a family of morphisms into `Spf R` that both
restrict the same `ψ : R →+* Γ(X, 𝒪_X)` agree on their overlap — the hypothesis
`OpenCover.glueMorphisms` asks for.

The overlap is not affine, so this is not the affine uniqueness statement; it is
`FormalSpectrum.hom_ext_of_globalSectionsHom` (issue 920) applied to the overlap, which is itself a
formal scheme, with a supplied affine cover of it. The continuity hypotheses `hf`/`hg` are on that
cover, and are the same genuine side condition as everywhere else on this line. -/
theorem pullback_fst_comp_eq_snd_comp (i j : 𝒰.J) (hi : (𝒰.obj i).LocallyFG)
    (charts : ∀ x : 𝒰.overlapFormalScheme i j hi,
      AffineChart (𝒰.overlapFormalScheme i j hi) x)
    (hcfg : ∀ x, (charts x).I.FG)
    (hki : globalSectionsHom I (𝒰.obj i).toLocallyRingedSpace (k i) =
      ((𝒰.cmap i).c.app (op (⊤ : Opens X))).hom.comp ψ)
    (hkj : globalSectionsHom I (𝒰.obj j).toLocallyRingedSpace (k j) =
      ((𝒰.cmap j).c.app (op (⊤ : Opens X))).hom.comp ψ)
    (hf : ∀ x, I ≤ (charts x).I.comap (globalSectionsMap I (charts x).I
      ((charts x).map ≫ pullback.fst (𝒰.cmap i) (𝒰.cmap j) ≫ k i)))
    (hg : ∀ x, I ≤ (charts x).I.comap (globalSectionsMap I (charts x).I
      ((charts x).map ≫ pullback.snd (𝒰.cmap i) (𝒰.cmap j) ≫ k j))) (hI : I.FG) :
    pullback.fst (𝒰.cmap i) (𝒰.cmap j) ≫ k i =
      pullback.snd (𝒰.cmap i) (𝒰.cmap j) ≫ k j := by
  -- The comparison has to be stated over the pullback, not over `overlapFormalScheme … `: the two
  -- are definitionally equal, but `rw` matches at `instances` transparency and will not unfold the
  -- latter, so rewriting inside the goal produced by `hom_ext_of_globalSectionsHom` fails.
  have key : globalSectionsHom I (pullback (𝒰.cmap i) (𝒰.cmap j))
        (pullback.fst (𝒰.cmap i) (𝒰.cmap j) ≫ k i) =
      globalSectionsHom I (pullback (𝒰.cmap i) (𝒰.cmap j))
        (pullback.snd (𝒰.cmap i) (𝒰.cmap j) ≫ k j) := by
    rw [globalSectionsHom_comp, globalSectionsHom_comp, hki, hkj]
    -- Both sides are `ψ` restricted along a leg of the pullback square followed by a cover map;
    -- the `c`-component of the composite is the composite of the components, definitionally.
    change (((pullback.fst (𝒰.cmap i) (𝒰.cmap j) ≫ 𝒰.cmap i).c.app
        (op (⊤ : Opens X))).hom).comp ψ =
      (((pullback.snd (𝒰.cmap i) (𝒰.cmap j) ≫ 𝒰.cmap j).c.app
        (op (⊤ : Opens X))).hom).comp ψ
    rw [pullback.condition]
  exact hom_ext_of_globalSectionsHom (X := 𝒰.overlapFormalScheme i j hi) I charts hcfg hI
    _ _ hf hg key

variable (hI : I.FG) (hlfg : ∀ l, (𝒰.obj l).LocallyFG)
variable (ocharts : ∀ i j, ∀ x : 𝒰.overlapFormalScheme i j (hlfg i),
    AffineChart (𝒰.overlapFormalScheme i j (hlfg i)) x)
variable (hofg : ∀ i j x, (ocharts i j x).I.FG)
variable (hk : ∀ l, globalSectionsHom I (𝒰.obj l).toLocallyRingedSpace (k l) =
    ((𝒰.cmap l).c.app (op (⊤ : Opens X))).hom.comp ψ)
variable (hf : ∀ i j, ∀ x : 𝒰.overlapFormalScheme i j (hlfg i),
    I ≤ (ocharts i j x).I.comap
      (globalSectionsMap I (ocharts i j x).I
        ((ocharts i j x).map ≫ pullback.fst (𝒰.cmap i) (𝒰.cmap j) ≫ k i)))
variable (hg : ∀ i j, ∀ x : 𝒰.overlapFormalScheme i j (hlfg i),
    I ≤ (ocharts i j x).I.comap
      (globalSectionsMap I (ocharts i j x).I
        ((ocharts i j x).map ≫ pullback.snd (𝒰.cmap i) (𝒰.cmap j) ≫ k j)))

/-- **The morphism `X ⟶ Spf R` glued from a family of chart morphisms restricting a common
`ψ : R →+* Γ(X, 𝒪_X)`.** The overlap agreement `glueMorphisms` requires is
`pullback_fst_comp_eq_snd_comp`. -/
def glueHomOfGlobalSectionsHom : X.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I :=
  𝒰.glueMorphisms k fun i j =>
    𝒰.pullback_fst_comp_eq_snd_comp I k ψ i j (hlfg i) (ocharts i j)
      (hofg i j) (hk i) (hk j) (hf i j) (hg i j) hI

/-- The glued morphism restricts to the family it was glued from. -/
theorem cmap_comp_glueHomOfGlobalSectionsHom (i : 𝒰.J) :
    𝒰.cmap i ≫ 𝒰.glueHomOfGlobalSectionsHom I k ψ hI hlfg ocharts hofg hk hf hg = k i :=
  𝒰.map_glueMorphisms k _ i

/-- **The glued morphism induces `ψ` on every chart.** This is the per-chart statement; whether it
upgrades to `globalSectionsHom I X (glueHomOfGlobalSectionsHom …) = ψ` is the sheaf-axiom step this
file deliberately does not take — see the scope note in the module docstring. -/
theorem comp_globalSectionsHom_glueHomOfGlobalSectionsHom (i : 𝒰.J) :
    ((𝒰.cmap i).c.app (op (⊤ : Opens X))).hom.comp
        (globalSectionsHom I X.toLocallyRingedSpace
          (𝒰.glueHomOfGlobalSectionsHom I k ψ hI hlfg ocharts hofg hk hf hg)) =
      ((𝒰.cmap i).c.app (op (⊤ : Opens X))).hom.comp ψ := by
  -- Writing the instance of `globalSectionsHom_comp` out by hand makes the backwards rewrite
  -- syntactic; the general lemma's `⊤` sits at `LocallyRingedSpace` and does not match the goal's.
  have h1 : globalSectionsHom I (𝒰.obj i).toLocallyRingedSpace
      (𝒰.cmap i ≫ 𝒰.glueHomOfGlobalSectionsHom I k ψ hI hlfg ocharts hofg hk hf hg) =
      ((𝒰.cmap i).c.app (op (⊤ : Opens X))).hom.comp
        (globalSectionsHom I X.toLocallyRingedSpace
          (𝒰.glueHomOfGlobalSectionsHom I k ψ hI hlfg ocharts hofg hk hf hg)) :=
    globalSectionsHom_comp I (𝒰.cmap i) _
  rw [← h1, 𝒰.cmap_comp_glueHomOfGlobalSectionsHom I k ψ hI hlfg ocharts hofg hk hf hg i, hk i]

end OpenCover

section OfAffineCharts

/-- **Every piece of `OpenCover.ofAffineCharts` is locally finitely generated** when the charts
have finitely generated ideals of definition: the piece is `Spf` of such a ring. This is what the
overlaps of that cover need in order to be formal schemes, so it appears in the type of every
hypothesis below and must not be `private`. -/
theorem ofAffineCharts_obj_locallyFG {X : FormalScheme.{u}} (charts : ∀ x : X, AffineChart X x)
    (hfg : ∀ x, (charts x).I.FG) (x : X) :
    ((OpenCover.ofAffineCharts charts).obj x).LocallyFG :=
  locallyFG_Spf (hfg x)

open OpenCover

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable {X : FormalScheme.{u}} (charts : ∀ x : X, AffineChart X x)
variable (hfg : ∀ x, (charts x).I.FG)
variable (ψ : R →+* X.presheaf.obj (op (⊤ : Opens X)))
variable (hcont : ∀ x, I ≤ (charts x).I.comap (chartHom charts ψ x))
variable (hI : I.FG)

/-- Shorthand for the `(i, j)` overlap of the cover by the supplied charts. Every hypothesis of
`homOfGlobalSectionsHom` quantifies over its points. -/
abbrev chartOverlap (i j : X) : FormalScheme.{u} :=
  (ofAffineCharts charts).overlapFormalScheme i j (ofAffineCharts_obj_locallyFG charts hfg i)

/-- **The morphism `X ⟶ Spf R` induced by `ψ : R →+* Γ(X, 𝒪_X)`**, over a supplied family of
affine charts with finitely generated ideals of definition, and a supplied family of affine charts
on their overlaps.

The continuity hypotheses are the honest content of the construction: `hcont` says each
chart-restriction of `ψ` is continuous, and `hf`/`hg` say the two restrictions being compared on
each overlap are continuous on the supplied cover of that overlap. None of them is automatic; see
the module docstring. -/
def homOfGlobalSectionsHom
    (ocharts : ∀ i j, ∀ x : chartOverlap charts hfg i j,
      AffineChart (chartOverlap charts hfg i j) x)
    (hofg : ∀ i j x, (ocharts i j x).I.FG)
    (hf : ∀ i j, ∀ x : chartOverlap charts hfg i j,
      I ≤ (ocharts i j x).I.comap (globalSectionsMap I (ocharts i j x).I
        ((ocharts i j x).map ≫
          pullback.fst ((ofAffineCharts charts).cmap i) ((ofAffineCharts charts).cmap j) ≫
            chartMap I charts ψ i (hcont i))))
    (hg : ∀ i j, ∀ x : chartOverlap charts hfg i j,
      I ≤ (ocharts i j x).I.comap (globalSectionsMap I (ocharts i j x).I
        ((ocharts i j x).map ≫
          pullback.snd ((ofAffineCharts charts).cmap i) ((ofAffineCharts charts).cmap j) ≫
            chartMap I charts ψ j (hcont j)))) :
    X.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I :=
  (ofAffineCharts charts).glueHomOfGlobalSectionsHom I
    (fun y => chartMap I charts ψ y (hcont y)) ψ hI (ofAffineCharts_obj_locallyFG charts hfg)
    ocharts hofg (fun y => globalSectionsHom_chartMap I charts ψ y (hcont y)) hf hg

/-- The induced morphism restricts, on the chart at `x`, to the morphism of formal spectra that the
chart-restriction of `ψ` induces. -/
theorem chart_comp_homOfGlobalSectionsHom (ocharts) (hofg) (hf) (hg) (x : X) :
    (charts x).map ≫ homOfGlobalSectionsHom I charts hfg ψ hcont hI ocharts hofg hf hg =
      chartMap I charts ψ x (hcont x) :=
  (ofAffineCharts charts).cmap_comp_glueHomOfGlobalSectionsHom I
    (fun y => chartMap I charts ψ y (hcont y)) ψ hI (ofAffineCharts_obj_locallyFG charts hfg)
    ocharts hofg (fun y => globalSectionsHom_chartMap I charts ψ y (hcont y)) hf hg x

/-- **The induced morphism induces `ψ` on every chart.** The global statement
`globalSectionsHom I X (homOfGlobalSectionsHom …) = ψ` is not proved here — see the module
docstring for what it would take. -/
theorem comp_globalSectionsHom_homOfGlobalSectionsHom (ocharts) (hofg) (hf) (hg) (x : X) :
    ((charts x).map.c.app (op (⊤ : Opens X))).hom.comp
        (globalSectionsHom I X.toLocallyRingedSpace
          (homOfGlobalSectionsHom I charts hfg ψ hcont hI ocharts hofg hf hg)) =
      ((charts x).map.c.app (op (⊤ : Opens X))).hom.comp ψ :=
  (ofAffineCharts charts).comp_globalSectionsHom_glueHomOfGlobalSectionsHom I
    (fun y => chartMap I charts ψ y (hcont y)) ψ hI (ofAffineCharts_obj_locallyFG charts hfg)
    ocharts hofg (fun y => globalSectionsHom_chartMap I charts ψ y (hcont y)) hf hg x

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **A morphism into a formal spectrum is determined by its restrictions to the charts.**

This is not a weakening of `FormalSpectrum.hom_ext_of_globalSectionsHom`: that compares the induced
homomorphisms `R →+* Γ(X, 𝒪_X)` and needs the per-chart continuity condition, while this compares
the restricted morphisms themselves and needs no side condition at all. It is the uniqueness
counterpart of `homOfGlobalSectionsHom`. -/
theorem hom_ext_of_chart_comp (f g : X.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I)
    (h : ∀ x : X, (charts x).map ≫ f = (charts x).map ≫ g) : f = g :=
  (OpenCover.ofAffineCharts charts).hom_ext f g h

end OfAffineCharts

section SuppliedCharts

open OpenCover

variable {X : FormalScheme.{u}}

/-- **A chosen finitely generated affine chart on the `(i, j)` overlap of a supplied chart
family**, which is what `AlgebraicGeometry.FormalScheme.homOfGlobalSectionsHom` asks of its
`ocharts` when the caller has nothing better to supply. This is
`AlgebraicGeometry.FormalScheme.OpenCover.overlapChart` at the cover
`AlgebraicGeometry.FormalScheme.OpenCover.ofAffineCharts charts`, whose pieces are locally
finitely generated by `AlgebraicGeometry.FormalScheme.ofAffineCharts_obj_locallyFG`.

`AlgebraicGeometry.FormalScheme.chartOverlap` is an abbreviation for that overlap taken at the
same witness, so this lands definitionally where the construction wants it: no transport is
needed and none is used. -/
def overlapChartOf (charts : ∀ x : X, AffineChart X x) (hfg : ∀ x, (charts x).I.FG)
    (i j : X) (x : chartOverlap charts hfg i j) :
    AffineChart (chartOverlap charts hfg i j) x :=
  (OpenCover.ofAffineCharts charts).overlapChart i j
    (ofAffineCharts_obj_locallyFG charts hfg i) x

/-- The ideal of definition of `AlgebraicGeometry.FormalScheme.overlapChartOf` is finitely
generated, which is the `hofg` argument of
`AlgebraicGeometry.FormalScheme.homOfGlobalSectionsHom`. -/
theorem fg_overlapChartOf (charts : ∀ x : X, AffineChart X x) (hfg : ∀ x, (charts x).I.FG)
    (i j : X) (x : chartOverlap charts hfg i j) : (overlapChartOf charts hfg i j x).I.FG :=
  (OpenCover.ofAffineCharts charts).overlapChart_fg i j
    (ofAffineCharts_obj_locallyFG charts hfg i) x

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable (charts : ∀ x : X, AffineChart X x) (hfg : ∀ x, (charts x).I.FG)
variable (ψ : R →+* X.presheaf.obj (op (⊤ : Opens X)))

/-- **The continuity conditions that gluing a morphism `X ⟶ Spf R` out of `ψ` requires**, over a
*supplied* family of affine charts and the overlap charts
`AlgebraicGeometry.FormalScheme.overlapChartOf` chooses for it. These are the three arguments of
`AlgebraicGeometry.FormalScheme.homOfGlobalSectionsHom` that carry content: given `charts` and
`hfg`, its `ocharts` and `hofg` are canonical and its `hI` is about `R` alone, and what is left is
`hcont`, `hf` and `hg`.

They are conditions and not data — the structure is a `Prop`, and every projection is used only in
a proof position, so by proof irrelevance the morphism built from it does not depend on which
proof is supplied.

**The chart family is supplied and not chosen, and that is the point.** A caller who obtains a
better family — one whose charts are drawn from a neighbourhood basis that already records the
bound, in the manner of `AlgebraicGeometry.FormalScheme.AdicOverBaseLocallyFG` — states these three
conditions at *that* family with nothing restated. See
`AlgebraicGeometry.FormalScheme.LocallyFG.SpfHomContinuity` for the specialisation to the charts
`AlgebraicGeometry.FormalScheme.LocallyFG` chooses, and for why it is offered rather than
recommended.

**None of the three is automatic.** `FormalSpectrum.spfGammaEquiv` inverts `Spf` only on the
continuity-restricted subtype, which is why the module docstring calls these hypotheses inherited
rather than incidental. -/
structure SpfHomContinuity : Prop where
  /-- Each chart-restriction of `ψ` is continuous. -/
  cont : ∀ x, I ≤ (charts x).I.comap (chartHom charts ψ x)
  /-- The first of the two restrictions being compared on an overlap is continuous, on the chosen
  affine cover of that overlap. -/
  fst : ∀ i j, ∀ x : chartOverlap charts hfg i j,
    I ≤ (overlapChartOf charts hfg i j x).I.comap
      (globalSectionsMap I (overlapChartOf charts hfg i j x).I
        ((overlapChartOf charts hfg i j x).map ≫
          pullback.fst ((ofAffineCharts charts).cmap i) ((ofAffineCharts charts).cmap j) ≫
            chartMap I charts ψ i (cont i)))
  /-- The second of the two restrictions being compared on an overlap is continuous, on the same
  cover. -/
  snd : ∀ i j, ∀ x : chartOverlap charts hfg i j,
    I ≤ (overlapChartOf charts hfg i j x).I.comap
      (globalSectionsMap I (overlapChartOf charts hfg i j x).I
        ((overlapChartOf charts hfg i j x).map ≫
          pullback.snd ((ofAffineCharts charts).cmap i) ((ofAffineCharts charts).cmap j) ≫
            chartMap I charts ψ j (cont j)))

variable (hI : I.FG) (d : SpfHomContinuity I charts hfg ψ)

/-- **The morphism `X ⟶ Spf R` induced by `ψ`, over a supplied family of affine charts.** This is
`AlgebraicGeometry.FormalScheme.homOfGlobalSectionsHom` with its `ocharts` and `hofg` taken
canonically from `AlgebraicGeometry.FormalScheme.overlapChartOf`, so that the only hypotheses left
are finite generation of the target's ideal and the three continuity families of
`AlgebraicGeometry.FormalScheme.SpfHomContinuity`. -/
def homOfSpfHomContinuity : X.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I :=
  homOfGlobalSectionsHom I charts hfg ψ d.cont hI
    (overlapChartOf charts hfg) (fg_overlapChartOf charts hfg) d.fst d.snd

/-- The bundled form of `AlgebraicGeometry.FormalScheme.chart_comp_homOfGlobalSectionsHom`: the
induced morphism restricts, on the chart at `x`, to the morphism of formal spectra that the
chart-restriction of `ψ` induces. -/
theorem chart_comp_homOfSpfHomContinuity (x : X) :
    (charts x).map ≫ homOfSpfHomContinuity I charts hfg ψ hI d =
      chartMap I charts ψ x (d.cont x) :=
  chart_comp_homOfGlobalSectionsHom I charts hfg ψ d.cont hI _ _ d.fst d.snd x

end SuppliedCharts

section LocallyFGCharts

open OpenCover

variable {X : FormalScheme.{u}}

/-- **The overlap chart of the family `AlgebraicGeometry.FormalScheme.LocallyFG` chooses.** This is
`AlgebraicGeometry.FormalScheme.overlapChartOf` at `AlgebraicGeometry.FormalScheme.LocallyFG.chart`
and `AlgebraicGeometry.FormalScheme.LocallyFG.fg_chart`, and
it is what `AlgebraicGeometry.FormalScheme.existsUnique_globalSectionsHom_eq_of_locallyFG` — which
is *already* stated at the chosen charts — needs for its `ocharts`. -/
def LocallyFG.overlapChart (hX : X.LocallyFG) (i j : X)
    (x : chartOverlap hX.chart hX.fg_chart i j) :
    AffineChart (chartOverlap hX.chart hX.fg_chart i j) x :=
  overlapChartOf hX.chart hX.fg_chart i j x

/-- The ideal of definition of `AlgebraicGeometry.FormalScheme.LocallyFG.overlapChart` is finitely
generated. -/
theorem LocallyFG.fg_overlapChart (hX : X.LocallyFG) (i j : X)
    (x : chartOverlap hX.chart hX.fg_chart i j) : (hX.overlapChart i j x).I.FG :=
  fg_overlapChartOf hX.chart hX.fg_chart i j x

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable (hX : X.LocallyFG) (ψ : R →+* X.presheaf.obj (op (⊤ : Opens X)))

/-- **`AlgebraicGeometry.FormalScheme.SpfHomContinuity` at the charts
`AlgebraicGeometry.FormalScheme.LocallyFG` chooses.** A specialisation of the supplied-family form
and not a separate notion, so that a caller who later obtains a better family moves to it without
restating anything.

**Offered, not recommended.** `AlgebraicGeometry.FormalScheme.LocallyFG` is a `Prop`
(`FormalSchemes.LocallyFG`) and `AlgebraicGeometry.FormalScheme.LocallyFG.chart`
(`FormalSchemes.GlobalSectionsHom`) is nested `Exists.choose` of it, so by proof irrelevance
*every* witness `hX` yields the same family and there is no other family reachable through this
abbreviation. Continuity at it is therefore a statement about charts nothing describes.
`FormalSchemes.GeneralFibreProductLiftAdic`'s module docstring records that a per-chart continuity
witness of exactly this shape was unreachable for a `Classical.choice` cover (issues
460/468/472/487), that the layer carrying it was deleted rather than proved (issue 805), and it
says in so many words: do not reintroduce such a hypothesis in a new construction.

**The reachable form is one door down**, and is not built here:
`AlgebraicGeometry.FormalScheme.AdicOverBaseLocallyFG` (`FormalSchemes.AdicOverBaseChart`) is
`AlgebraicGeometry.FormalScheme.LocallyFG` with the adic-over-base bound added to the chart it
produces,
`AlgebraicGeometry.FormalScheme.exists_affineChart_subset_adicOverBase` makes such a chart
available at every point, and
`AlgebraicGeometry.BothChartedFibreDatumXY.adicBothCharts`
(`FormalSchemes.GeneralFibreProductLiftAdic`) is the pattern in which one witness supplies the
family *and* discharges the bound. Prefer building the family you need and passing it to
`AlgebraicGeometry.FormalScheme.SpfHomContinuity` over instantiating this. -/
abbrev LocallyFG.SpfHomContinuity : Prop :=
  FormalScheme.SpfHomContinuity I hX.chart hX.fg_chart ψ

variable (hI : I.FG) (d : LocallyFG.SpfHomContinuity I hX ψ)

/-- **The morphism `X ⟶ Spf R` induced by `ψ` over a locally finitely generated source**, with
every chart chosen rather than supplied. This is
`AlgebraicGeometry.FormalScheme.homOfSpfHomContinuity` at
`AlgebraicGeometry.FormalScheme.LocallyFG.chart`; see
`AlgebraicGeometry.FormalScheme.LocallyFG.SpfHomContinuity` for why a caller with a better family
should not come through here. -/
def homOfGlobalSectionsHomOfLocallyFG : X.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I :=
  homOfSpfHomContinuity I hX.chart hX.fg_chart ψ hI d

/-- The chosen-chart form of
`AlgebraicGeometry.FormalScheme.chart_comp_homOfSpfHomContinuity`. -/
theorem chart_comp_homOfGlobalSectionsHomOfLocallyFG (x : X) :
    (hX.chart x).map ≫ homOfGlobalSectionsHomOfLocallyFG I hX ψ hI d =
      chartMap I hX.chart ψ x (d.cont x) :=
  chart_comp_homOfSpfHomContinuity I hX.chart hX.fg_chart ψ hI d x

end LocallyFGCharts

end AlgebraicGeometry.FormalScheme

end
