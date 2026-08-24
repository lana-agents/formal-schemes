import FormalSchemes.GlueHomToSpf

set_option linter.style.header false

/-!
# The glued morphism into a formal spectrum induces the homomorphism it was built from

`FormalSchemes/GlueHomToSpf.lean` (issue 929) builds, out of a homomorphism
`ψ : R →+* Γ(X, 𝒪_X)` on a formal scheme `X`, a morphism `X ⟶ Spf R` — and characterises it
**chart by chart**: after restricting to any chart of the cover it induces `ψ`. That file's scope
note says plainly what was missing, namely the global statement
`FormalSpectrum.globalSectionsHom I X f = ψ`, and names the two ingredients it would need. This
file supplies them and takes that step, completing the fullness half of EGA I, 10.4.6 over a
non-affine source.

## The step

Per-chart agreement upgrades to global agreement because a section of `𝒪_X` is determined by its
restrictions to an open cover — the separation half of the sheaf axiom. Two facts turn that slogan
into `OpenCover.eq_of_chart_c_app_eq`:

* `TopCat.Presheaf.IsSheaf.section_ext` asks for its covering data **pointwise and existentially**:
  for each point of the open, *some* smaller open containing it on which the two sections agree.
  So the cover never has to be reshaped into a `iSup U = ⊤` statement; `OpenCover.exists_preimage`
  produces the chart through the point directly.
* For an open immersion `f`, the component `f.c.app (op ⊤)` sees exactly the restriction to the
  range of `f`. That is naturality of `f.c` along `range f ≤ ⊤` together with
  `PresheafedSpace.IsOpenImmersion.c_iso` at `⊤`, which says the component **over the range** is an
  isomorphism, hence injective. This is
  `AlgebraicGeometry.LocallyRingedSpace.restrict_eq_of_c_app_top_eq` below. Note it is *not*
  injectivity of `f.c.app (op ⊤)` itself, which is false — one chart does not see all of `X`.

## Scope: the `∃!` is over the continuous morphisms, and that is not a packaging artefact

`FormalSpectrum.hom_ext_of_globalSectionsHom` (issue 920) pins down a morphism by its
global-sections homomorphism only among morphisms whose restriction to each chart is continuous on
global sections, and `homOfGlobalSectionsHom` needs the same data to exist at all. So
`existsUnique_globalSectionsHom_eq` is stated over the subtype of chart-wise continuous morphisms
rather than over all morphisms of locally ringed spaces. The condition cannot be dropped:
`FormalSpectrum.spfGammaEquiv` inverts `Spf` only on the continuity-restricted subtype (issue 156's
counterexample), and issue 460 records that the general "open immersions are adic" statement is
false. What this file does contribute on that front is `continuous_homOfGlobalSectionsHom`: the
morphism the construction produces is itself chart-wise continuous, so the subtype is inhabited by
the thing one wants and the `∃!` is not vacuous.

No `Equiv`, `CategoryTheory.Functor.FullyFaithful` or equivalence of categories is packaged here.
Both sides of any such bijection would carry side conditions naming a *chosen* family of charts;
issue 920 declined that packaging, issue 929 declined it again, and an `∃!` with an honest scope
note is the right shape until a consumer says otherwise. The affine case, where no chart data is
needed, is packaged: see `AdicRingCat.spfHomEquiv` (`FormalSchemes.SpfFullyFaithful`) and
`spfEquivalence` (`FormalSchemes.SpfEquivalence`).

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.restrict_eq_of_c_app_top_eq`: sections of the target
  agreeing under `f.c.app (op ⊤)` agree after restriction to any open over which the `c`-component
  is invertible — for an open immersion, its range.
* `AlgebraicGeometry.FormalScheme.OpenCover.eq_of_chart_c_app_eq`: **sections of `𝒪_X` agreeing on
  every chart of an open cover are equal.** Stated about sections, over an arbitrary open cover,
  with no adic data and no continuity hypothesis anywhere in it.
* `AlgebraicGeometry.FormalScheme.OpenCover.globalSectionsHom_glueHomOfGlobalSectionsHom` and
  `AlgebraicGeometry.FormalScheme.globalSectionsHom_homOfGlobalSectionsHom`: **the glued morphism
  induces `ψ`**, over an arbitrary cover and over a supplied family of affine charts respectively.
* `AlgebraicGeometry.FormalScheme.continuous_homOfGlobalSectionsHom`: it is chart-wise continuous.
* `AlgebraicGeometry.FormalScheme.existsUnique_globalSectionsHom_eq`: **EGA I, 10.4.6 over a
  non-affine source** — a unique chart-wise continuous morphism `X ⟶ Spf R` induces `ψ`; and
  `existsUnique_globalSectionsHom_eq_of_locallyFG` over the charts `LocallyFG` supplies.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4 (10.4.6).
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry CategoryTheory.Limits
open FormalSpectrum

namespace AlgebraicGeometry.LocallyRingedSpace

/-- **A `c`-component at `⊤` that is invertible over an open `V` sees the restriction to `V`.** If
two sections of `𝒪_X` over `⊤` have the same image under `f.c.app (op ⊤)` for a morphism
`f : Y ⟶ X`, and the component `f.c.app (op V)` is an isomorphism, then the two sections already
agree after restriction to `V`.

This is naturality of `f.c` along `V ≤ ⊤` followed by cancelling the isomorphism. The case of
interest is `f` an open immersion and `V = range f`, where `hV` is
`PresheafedSpace.IsOpenImmersion.c_iso` at `⊤`; it is *not* injectivity of `f.c.app (op ⊤)` itself,
which is false — a single chart does not see all of `X`, and this is exactly the part that
survives. -/
theorem restrict_eq_of_c_app_top_eq {Y X : LocallyRingedSpace.{u}} (f : Y ⟶ X) (V : Opens X)
    (hV : IsIso (f.c.app (op V))) (s t : X.presheaf.obj (op (⊤ : Opens X)))
    (h : (f.c.app (op (⊤ : Opens X))).hom s = (f.c.app (op (⊤ : Opens X))).hom t) :
    (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom s =
      (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom t := by
  have hnat := f.c.naturality (homOfLE (le_top : V ≤ ⊤)).op
  -- Naturality of `f.c` along `V ≤ ⊤`, read on elements. Stated as a `have` with both sides
  -- written out: the composite-morphism spelling is definitional, but `simp` will not reach it.
  have key : ∀ u : X.presheaf.obj (op (⊤ : Opens X)),
      (f.c.app (op V)).hom ((X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom u) =
        ((f.base _* Y.presheaf).map (homOfLE (le_top : V ≤ ⊤)).op).hom
          ((f.c.app (op (⊤ : Opens X))).hom u) := fun u =>
    congrArg (fun φ : X.presheaf.obj (op (⊤ : Opens X)) ⟶ _ => φ.hom u) hnat
  have := hV
  apply ConcreteCategory.injective_of_mono_of_preservesPullback (f.c.app (op V))
  rw [key, key, h]

end AlgebraicGeometry.LocallyRingedSpace

namespace AlgebraicGeometry.FormalScheme

variable {X : FormalScheme.{u}}

open PresheafedSpace.IsOpenImmersion in
/-- **Sections of `𝒪_X` agreeing on every chart of an open cover are equal.**

This is the separation half of the sheaf axiom, phrased in the form the gluing constructions of
`FormalSchemes.GlueHomToSpf` leave their conclusions in: agreement of the images under the
`c`-components of the cover maps at `⊤`. Deliberately free of `I`, `ψ` and `Spf` — every future
"a global section is determined chart-wise" argument wants it in this generality.

The proof feeds `TopCat.Presheaf.IsSheaf.section_ext` the chart through the given point, which
`OpenCover.exists_preimage` produces; `section_ext`'s covering hypothesis is pointwise, so no
`iSup`-form restatement of `OpenCover.iUnion_range` is needed. -/
theorem OpenCover.eq_of_chart_c_app_eq (𝒰 : X.OpenCover)
    (s t : X.presheaf.obj (op (⊤ : Opens X)))
    (h : ∀ i, ((𝒰.cmap i).c.app (op (⊤ : Opens X))).hom s =
      ((𝒰.cmap i).c.app (op (⊤ : Opens X))).hom t) :
    s = t := by
  refine X.toSheafedSpace.IsSheaf.section_ext (U := op (⊤ : Opens X)) ?_
  intro x _
  obtain ⟨j, y, rfl⟩ := 𝒰.exists_preimage x
  exact ⟨(opensFunctor (𝒰.cmap j).toHom).obj ⊤, le_top, ⟨y, trivial, rfl⟩,
    LocallyRingedSpace.restrict_eq_of_c_app_top_eq (𝒰.cmap j) _ inferInstance s t (h j)⟩

namespace OpenCover

variable (𝒰 : X.OpenCover)
variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable (k : ∀ l, (𝒰.obj l).toLocallyRingedSpace ⟶ locallyRingedSpaceObj I)
variable (ψ : R →+* X.presheaf.obj (op (⊤ : Opens X)))
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

/-- **The glued morphism induces `ψ`**, over an arbitrary open cover. This is the global statement
that `OpenCover.comp_globalSectionsHom_glueHomOfGlobalSectionsHom` gives only chart-wise; the two
are separated exactly by `eq_of_chart_c_app_eq`. -/
theorem globalSectionsHom_glueHomOfGlobalSectionsHom :
    globalSectionsHom I X.toLocallyRingedSpace
        (𝒰.glueHomOfGlobalSectionsHom I k ψ hI hlfg ocharts hofg hk hf hg) = ψ :=
  RingHom.ext fun r =>
    𝒰.eq_of_chart_c_app_eq _ _ fun i =>
      congrArg (fun φ : R →+* (𝒰.obj i).presheaf.obj (op (⊤ : Opens (𝒰.obj i))) => φ r)
        (𝒰.comp_globalSectionsHom_glueHomOfGlobalSectionsHom I k ψ hI hlfg ocharts hofg hk hf hg i)

end OpenCover

section OfAffineCharts

open OpenCover

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable (charts : ∀ x : X, AffineChart X x) (hfg : ∀ x, (charts x).I.FG)
variable (ψ : R →+* X.presheaf.obj (op (⊤ : Opens X)))
variable (hcont : ∀ x, I ≤ (charts x).I.comap (chartHom charts ψ x))
variable (hI : I.FG)
variable (ocharts : ∀ i j, ∀ x : chartOverlap charts hfg i j,
    AffineChart (chartOverlap charts hfg i j) x)
variable (hofg : ∀ i j x, (ocharts i j x).I.FG)
variable (hf : ∀ i j, ∀ x : chartOverlap charts hfg i j,
    I ≤ (ocharts i j x).I.comap (globalSectionsMap I (ocharts i j x).I
      ((ocharts i j x).map ≫
        pullback.fst ((ofAffineCharts charts).cmap i) ((ofAffineCharts charts).cmap j) ≫
          chartMap I charts ψ i (hcont i))))
variable (hg : ∀ i j, ∀ x : chartOverlap charts hfg i j,
    I ≤ (ocharts i j x).I.comap (globalSectionsMap I (ocharts i j x).I
      ((ocharts i j x).map ≫
        pullback.snd ((ofAffineCharts charts).cmap i) ((ofAffineCharts charts).cmap j) ≫
          chartMap I charts ψ j (hcont j))))

/-- **The morphism built from `ψ` induces `ψ`.** The statement `FormalSchemes.GlueHomToSpf` records
as its scope gap, over the supplied family of affine charts. -/
theorem globalSectionsHom_homOfGlobalSectionsHom :
    globalSectionsHom I X.toLocallyRingedSpace
        (homOfGlobalSectionsHom I charts hfg ψ hcont hI ocharts hofg hf hg) = ψ :=
  (ofAffineCharts charts).globalSectionsHom_glueHomOfGlobalSectionsHom I
    (fun y => chartMap I charts ψ y (hcont y)) ψ hI (ofAffineCharts_obj_locallyFG charts hfg)
    ocharts hofg (fun y => globalSectionsHom_chartMap I charts ψ y (hcont y)) hf hg

/-- **The morphism built from `ψ` is itself chart-wise continuous**, with the same charts. Its
restriction to the chart at `x` is `Spf` of `chartHom charts ψ x`, whose global-sections map is
that homomorphism back again (`FormalSpectrum.globalSectionsMap_locallyRingedSpaceMap`), so the
continuity hypothesis `hcont` the construction consumed is also its conclusion. This is what makes
the uniqueness statement below non-vacuous. -/
theorem continuous_homOfGlobalSectionsHom (x : X) :
    I ≤ (charts x).I.comap (globalSectionsMap I (charts x).I
      ((charts x).map ≫ homOfGlobalSectionsHom I charts hfg ψ hcont hI ocharts hofg hf hg)) := by
  rw [chart_comp_homOfGlobalSectionsHom I charts hfg ψ hcont hI ocharts hofg hf hg x, chartMap,
    globalSectionsMap_locallyRingedSpaceMap]
  exact hcont x

include hI ocharts hofg hf hg in
/-- **EGA I, 10.4.6 over a non-affine source.** There is exactly one morphism `X ⟶ Spf R` inducing
`ψ : R →+* Γ(X, 𝒪_X)` on global sections, among those whose restriction to each of the supplied
charts is continuous on global sections.

Existence is `globalSectionsHom_homOfGlobalSectionsHom` together with
`continuous_homOfGlobalSectionsHom`, and uniqueness is
`FormalSpectrum.hom_ext_of_globalSectionsHom` (issue 920). The quantifier ranges over the
continuity-restricted subtype rather than over all morphisms of locally ringed spaces; see the
module docstring for why that restriction is genuine and not a packaging artefact. -/
theorem existsUnique_globalSectionsHom_eq :
    ∃! f : { f : X.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I //
        ∀ x : X, I ≤ (charts x).I.comap
          (globalSectionsMap I (charts x).I ((charts x).map ≫ f)) },
      globalSectionsHom I X.toLocallyRingedSpace f.1 = ψ := by
  refine ⟨⟨homOfGlobalSectionsHom I charts hfg ψ hcont hI ocharts hofg hf hg,
    continuous_homOfGlobalSectionsHom I charts hfg ψ hcont hI ocharts hofg hf hg⟩,
    globalSectionsHom_homOfGlobalSectionsHom I charts hfg ψ hcont hI ocharts hofg hf hg,
    fun f hf' => Subtype.ext ?_⟩
  refine hom_ext_of_globalSectionsHom I charts hfg hI _ _ f.2
    (continuous_homOfGlobalSectionsHom I charts hfg ψ hcont hI ocharts hofg hf hg) ?_
  rw [hf', globalSectionsHom_homOfGlobalSectionsHom I charts hfg ψ hcont hI ocharts hofg hf hg]

end OfAffineCharts

section LocallyFG

open OpenCover

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable (hX : X.LocallyFG) (ψ : R →+* X.presheaf.obj (op (⊤ : Opens X)))
variable (hcont : ∀ x, I ≤ (hX.chart x).I.comap (chartHom hX.chart ψ x))
variable (hI : I.FG)
variable (ocharts : ∀ i j, ∀ x : chartOverlap hX.chart hX.fg_chart i j,
    AffineChart (chartOverlap hX.chart hX.fg_chart i j) x)
variable (hofg : ∀ i j x, (ocharts i j x).I.FG)
variable (hf : ∀ i j, ∀ x : chartOverlap hX.chart hX.fg_chart i j,
    I ≤ (ocharts i j x).I.comap (globalSectionsMap I (ocharts i j x).I
      ((ocharts i j x).map ≫
        pullback.fst ((ofAffineCharts hX.chart).cmap i) ((ofAffineCharts hX.chart).cmap j) ≫
          chartMap I hX.chart ψ i (hcont i))))
variable (hg : ∀ i j, ∀ x : chartOverlap hX.chart hX.fg_chart i j,
    I ≤ (ocharts i j x).I.comap (globalSectionsMap I (ocharts i j x).I
      ((ocharts i j x).map ≫
        pullback.snd ((ofAffineCharts hX.chart).cmap i) ((ofAffineCharts hX.chart).cmap j) ≫
          chartMap I hX.chart ψ j (hcont j))))

include hI ocharts hofg hf hg in
/-- **EGA I, 10.4.6 over a locally finitely generated formal scheme**, with the charts supplied by
`LocallyFG.chart`, mirroring `FormalSpectrum.hom_ext_of_globalSectionsHom_of_locallyFG`. The
continuity hypotheses still name the chosen charts: that dependence is genuine, not a packaging
artefact. -/
theorem existsUnique_globalSectionsHom_eq_of_locallyFG :
    ∃! f : { f : X.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I //
        ∀ x : X, I ≤ (hX.chart x).I.comap
          (globalSectionsMap I (hX.chart x).I ((hX.chart x).map ≫ f)) },
      globalSectionsHom I X.toLocallyRingedSpace f.1 = ψ :=
  existsUnique_globalSectionsHom_eq I hX.chart hX.fg_chart ψ hcont hI ocharts hofg hf hg

end LocallyFG

end AlgebraicGeometry.FormalScheme

end
