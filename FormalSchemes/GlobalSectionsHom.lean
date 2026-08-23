import FormalSchemes.LocallyFG
import FormalSchemes.OpenCoverHomExt
import FormalSchemes.SpfGammaRoundTrip

set_option linter.style.header false

/-!
# Global sections of a morphism into a formal spectrum, and faithfulness of `Spf` over a
non-affine source (EGA I, 10.4.6)

`FormalSchemes/SpfGamma.lean` records `FormalSpectrum.globalSectionsMap`, the ring homomorphism
`R →+* S` recovered from a morphism of formal spectra `Spf S ⟶ Spf R`, and
`FormalSchemes/SpfEquivalence.lean` (issue 915) assembles that into the categorical form of
EGA I, 10.4.6 for an **affine** source. Both are confined to affine sources: `globalSectionsMap`'s
argument is typed `locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I`.

This file takes the first step past that restriction. `FormalSpectrum.globalSectionsHom` reads the
global sections of a morphism into `Spf R` from an **arbitrary** locally ringed space, and
`FormalSpectrum.hom_ext_of_globalSectionsHom` shows that for a formal scheme source the resulting
homomorphism `R →+* Γ(X, 𝒪_X)` determines the morphism.

## Scope, and why the continuity hypotheses are not an artefact

The theorem is the **faithfulness half only** of EGA I, 10.4.6 over a non-affine source. The
fullness half — building a morphism `X ⟶ Spf R` out of a homomorphism `R →+* Γ(X, 𝒪_X)` — needs
`FormalScheme.OpenCover.glueMorphisms` (`FormalSchemes.OpenCoverGlueMorphisms`) and, with it, an
agreement condition on the locally-ringed-space pullbacks of the cover, which are not affine. It is
deliberately not attempted here.

Even the faithfulness half carries a genuine side condition, and it is not a weakness of the proof.
The affine input is `FormalSpectrum.spfGammaEquiv`, whose inverse is `globalSectionsMap` **only on
the continuity-restricted subtype**: continuity of the global-sections map is not automatic for a
morphism of locally ringed spaces between formal spectra (the counterexample of issue 156). So
`globalSectionsMap` is not known to be injective on all of `Spf S ⟶ Spf R`, and the general
statement inherits exactly that restriction, chart by chart. The hypotheses `hf`/`hg` below say the
restriction of each morphism to each chart of the cover is continuous on global sections; they
mention the chosen charts because the condition genuinely depends on the chart's ideal of
definition, which the formal scheme `X` does not carry.

## Main definitions and results

* `FormalSpectrum.globalSectionsHom`: the homomorphism `R →+* Γ(X, 𝒪_X)` induced by a morphism
  `X ⟶ Spf R` from an arbitrary locally ringed space.
* `FormalSpectrum.globalSectionsMap_eq_globalSectionsHom`: on an affine source it is
  `globalSectionsMap`, read through the identification `Γ(Spf S) ≃+* S`.
* `FormalSpectrum.globalSectionsHom_comp`: functoriality in the source.
* `AlgebraicGeometry.FormalScheme.OpenCover.ofAffineCharts`: the open cover assembled from a
  *supplied* family of affine charts — the variant of `FormalScheme.affineCover` in which the
  charts are an argument rather than an internal `Classical.choice`, so that a hypothesis can
  refer to them.
* `AlgebraicGeometry.FormalScheme.LocallyFG.chart`: a chosen affine chart with finitely generated
  ideal of definition around a point of a locally finitely generated formal scheme.
* `FormalSpectrum.hom_ext_of_globalSectionsHom` and its `LocallyFG` restatement
  `FormalSpectrum.hom_ext_of_globalSectionsHom_of_locallyFG`: **EGA I, 10.4.6**, faithfulness half,
  over a non-affine source.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4 (10.4.6).
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable {S : Type u} [CommRing S] [TopologicalSpace S] (J : Ideal S) [IsAdicRing J]

/-- **Global sections of a morphism into a formal spectrum.** The ring homomorphism
`R →+* Γ(X, 𝒪_X)` induced by a morphism `f : X ⟶ Spf R` out of an arbitrary locally ringed space:
take the component of `f.c` at `⊤` and precompose with the identification `R ≃+* Γ(Spf R)` of
`FormalSpectrum.globalSectionsEquiv` (EGA I, 10.1.3).

The target of `f.c.app (op ⊤)` is `Γ(X, f⁻¹ ⊤)`, which is `Γ(X, ⊤)` definitionally, so no
transport along `Opens.map_top` is needed. -/
def globalSectionsHom (X : LocallyRingedSpace.{u}) (f : X ⟶ locallyRingedSpaceObj I) :
    R →+* X.presheaf.obj (op (⊤ : Opens X)) :=
  (f.c.app (op (⊤ : Opens (FormalSpectrum I)))).hom.comp (globalSectionsEquiv I).symm.toRingHom

theorem globalSectionsHom_apply (X : LocallyRingedSpace.{u}) (f : X ⟶ locallyRingedSpaceObj I)
    (r : R) :
    globalSectionsHom I X f r =
      (f.c.app (op (⊤ : Opens (FormalSpectrum I)))).hom ((globalSectionsEquiv I).symm r) :=
  rfl

/-- **On an affine source, `globalSectionsHom` is `globalSectionsMap`**, read through the
identification `Γ(Spf S) ≃+* S`. The two definitions differ only in whether the target is
transported back along `globalSectionsEquiv`, which `globalSectionsHom` deliberately does not do:
for a general source there is nothing to transport to. -/
theorem globalSectionsMap_eq_globalSectionsHom
    (f : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I) :
    globalSectionsMap I J f =
      (globalSectionsEquiv J).toRingHom.comp (globalSectionsHom I (locallyRingedSpaceObj J) f) :=
  rfl

/-- **Functoriality in the source.** Restricting a morphism `f : X ⟶ Spf R` along `g : Z ⟶ X`
restricts its global-sections homomorphism along `g`.

Unlike its affine analogue `FormalSpectrum.globalSectionsMap_comp`, this is definitional: that one
re-wraps both ends through `globalSectionsEquiv`, whereas here only the source end is wrapped. -/
theorem globalSectionsHom_comp {Z X : LocallyRingedSpace.{u}} (g : Z ⟶ X)
    (f : X ⟶ locallyRingedSpaceObj I) :
    globalSectionsHom I Z (g ≫ f) =
      (g.c.app (op (⊤ : Opens X))).hom.comp (globalSectionsHom I X f) :=
  rfl

end FormalSpectrum

namespace AlgebraicGeometry.FormalScheme

/-- **The open cover assembled from a supplied family of affine charts**, indexed by the points of
`X`. This is `FormalScheme.affineCover` with the family as an argument rather than an internal
`AffineChart.choice`, so that a hypothesis can refer to the charts that were used; compare
`FormalScheme.OpenCover.ofTfTypeCharts` (`FormalSchemes.TopFiniteTypeBasis`). -/
def OpenCover.ofAffineCharts {X : FormalScheme.{u}} (charts : ∀ x : X, AffineChart X x) :
    OpenCover X where
  J := X
  obj x := FormalScheme.Spf (charts x).I
  map x := Hom.mk (charts x).map
  f x := x
  covers x := (charts x).mem
  isOpenImmersion x := (charts x).isOpenImmersion

/-- `FormalScheme.affineCover` is the cover of the chosen charts. -/
theorem affineCover_eq_ofAffineCharts (X : FormalScheme.{u}) :
    affineCover X = OpenCover.ofAffineCharts (AffineChart.choice X) :=
  rfl

/-- **A chosen finitely generated affine chart** around a point of a locally finitely generated
formal scheme. `FormalScheme.AffineChart.choice` makes no such guarantee: `LocallyFG` is exactly
the statement that a chart with finitely generated ideal of definition exists at every point, and
this records a choice of one. -/
def LocallyFG.chart {X : FormalScheme.{u}} (hX : X.LocallyFG) (x : X) : AffineChart X x :=
  { R := (hX x).choose
    commRing := (hX x).choose_spec.choose
    topR := (hX x).choose_spec.choose_spec.choose
    I := (hX x).choose_spec.choose_spec.choose_spec.choose
    adic := (hX x).choose_spec.choose_spec.choose_spec.choose_spec.choose
    map := (hX x).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose
    mem := (hX x).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.1
    isOpenImmersion :=
      (hX x).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2 }

/-- The ideal of definition of `LocallyFG.chart` is finitely generated — the whole point of
choosing the chart through `LocallyFG` rather than through `AffineChart.choice`. -/
theorem LocallyFG.fg_chart {X : FormalScheme.{u}} (hX : X.LocallyFG) (x : X) :
    (hX.chart x).I.FG :=
  (hX x).choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.1

end AlgebraicGeometry.FormalScheme

namespace FormalSpectrum

open AlgebraicGeometry.FormalScheme

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]

/-- **EGA I, 10.4.6, faithfulness half, over a non-affine source.** Two morphisms
`f g : X ⟶ Spf R` out of a formal scheme are equal as soon as they induce the same homomorphism
`R →+* Γ(X, 𝒪_X)` — provided `R` and the charts of a supplied affine cover have finitely generated
ideals of definition, and the restriction of each morphism to each chart is continuous on global
sections.

The continuity hypotheses cannot be dropped; see the module docstring. They are stated over the
supplied charts rather than over `X` because continuity mentions the chart's ideal of definition. -/
theorem hom_ext_of_globalSectionsHom {X : FormalScheme.{u}} (charts : ∀ x : X, AffineChart X x)
    (hfg : ∀ x, (charts x).I.FG) (hI : I.FG)
    (f g : X.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I)
    (hf : ∀ x : X, I ≤ (charts x).I.comap
      (globalSectionsMap I (charts x).I ((charts x).map ≫ f)))
    (hg : ∀ x : X, I ≤ (charts x).I.comap
      (globalSectionsMap I (charts x).I ((charts x).map ≫ g)))
    (h : globalSectionsHom I X.toLocallyRingedSpace f =
      globalSectionsHom I X.toLocallyRingedSpace g) :
    f = g := by
  refine (OpenCover.ofAffineCharts charts).hom_ext f g fun x => ?_
  -- The two restrictions to the chart at `x` have the same global-sections map: both are the
  -- common `globalSectionsHom` restricted along the chart, by functoriality in the source.
  have hmap : globalSectionsMap I (charts x).I ((charts x).map ≫ f) =
      globalSectionsMap I (charts x).I ((charts x).map ≫ g) := by
    rw [globalSectionsMap_eq_globalSectionsHom, globalSectionsMap_eq_globalSectionsHom,
      globalSectionsHom_comp, globalSectionsHom_comp, h]
  -- A continuous morphism of formal spectra is `Spf` of its global-sections map (`spfGammaEquiv`),
  -- so the two restrictions are `Spf` of the same homomorphism.
  have hf' := locallyRingedSpaceMap_globalSectionsMap I (charts x).I hI (hfg x)
    ((charts x).map ≫ f) (hf x)
  have hg' := locallyRingedSpaceMap_globalSectionsMap I (charts x).I hI (hfg x)
    ((charts x).map ≫ g) (hg x)
  -- `locallyRingedSpaceMap` takes a continuity proof, so equal homomorphisms give equal morphisms
  -- only after the proof arguments are matched; definitional proof irrelevance does that.
  have congrMap : ∀ (φ ψ : R →+* (charts x).R) (hφ : I ≤ (charts x).I.comap φ)
      (hψ : I ≤ (charts x).I.comap ψ), φ = ψ →
      locallyRingedSpaceMap I (charts x).I φ hφ = locallyRingedSpaceMap I (charts x).I ψ hψ := by
    rintro φ ψ hφ hψ rfl
    rfl
  change (charts x).map ≫ f = (charts x).map ≫ g
  rw [← hf', ← hg']
  exact congrMap _ _ _ _ hmap

/-- **EGA I, 10.4.6, faithfulness half**, over a locally finitely generated formal scheme, with the
affine cover supplied by `LocallyFG.chart`. The continuity hypotheses still name the chosen charts:
that dependence is genuine, not a packaging artefact. -/
theorem hom_ext_of_globalSectionsHom_of_locallyFG {X : FormalScheme.{u}} (hX : X.LocallyFG)
    (hI : I.FG) (f g : X.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I)
    (hf : ∀ x : X, I ≤ (hX.chart x).I.comap
      (globalSectionsMap I (hX.chart x).I ((hX.chart x).map ≫ f)))
    (hg : ∀ x : X, I ≤ (hX.chart x).I.comap
      (globalSectionsMap I (hX.chart x).I ((hX.chart x).map ≫ g)))
    (h : globalSectionsHom I X.toLocallyRingedSpace f =
      globalSectionsHom I X.toLocallyRingedSpace g) :
    f = g :=
  hom_ext_of_globalSectionsHom I hX.chart hX.fg_chart hI f g hf hg h

end FormalSpectrum

end
