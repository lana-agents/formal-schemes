import FormalSchemes.BasicOpenChartImage
import FormalSchemes.BasicOpenImmersionLRS
import FormalSchemes.OpenImmersionIsoOfRangeEq
import FormalSchemes.SpfGammaBase

set_option linter.style.header false

/-!
# Two affine charts have a common basic-open neighbourhood (EGA I, 10.13)

Let `X` be a locally ringed space and let `m : Spf A ⟶ X`, `m' : Spf A' ⟶ X` be two open
immersions from formal spectra — two *affine charts* of `X`. Given a point `x` in the range of
both, this file produces `g : A` and `g' : A'` such that the two refined charts

```
Spf A{1/g}^  ⟶ Spf A  ⟶ X        Spf A'{1/g'}^ ⟶ Spf A' ⟶ X
```

have **the same range**, and that range contains `x`. This is the formal-geometry analogue of
`AlgebraicGeometry.exists_basicOpen_le_affine_inter`, and it is the `Y`-side geometry EGA I
10.13's composition law at a non-affine target runs on: it is what lets a chart known to be
topologically of finite type over one chart of `Y` be re-read over another.

## The statement is an equality of ranges, not an identification of algebras

A composition law does not need `A{1/g}^` and `A'{1/g'}^` to be *the same algebra*; it needs one
formal scheme sitting over both charts. Equality of ranges produces that canonically and over `X`,
through `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq` and its two
`@[reassoc (attr := simp)]` factorisations — which is exactly what
`exists_basicOpenChart_inter_iso` below packages. So no away-of-away algebra isomorphism
(`FormalSchemes/AwayCompletionNested.lean`, `FormalSchemes/AwayCompletionAway.lean`) is used here,
and none is needed.

## How the argument runs, and where the formal-scheme content sits

Mathlib's proof for schemes shrinks twice and then converts once, and the same three steps work
here:

1. a basic open `D(g₀) ⊆ Spf A` through `x`'s preimage whose image lands in the range of `m`
   (`FormalSpectrum.isTopologicalBasis_basicOpen`);
2. a basic open `D(g') ⊆ Spf A'` through `x`'s other preimage, inside the preimage of
   `m '' D(g₀)` (the same basis, on the other chart);
3. the conversion: `D(g')` is *already* an open of the small chart `Spf A{1/g₀}^`, because that
   chart lifts through `m'` (`LocallyRingedSpace.IsOpenImmersion.lift`, whose range is computed by
   `lift_range`); the global section of `Spf A'` cutting out `D(g')` pulls back along that lift
   (`LocallyRingedSpace.preimage_basicOpen`) to a global section of `Spf A{1/g₀}^`, whose basic
   open is therefore basic in `Spf A{1/g₀}^`; and
   `FormalSpectrum.basicOpen_basicOpenChart_is_basicOpen`
   (`FormalSchemes/BasicOpenChartImage.lean`) carries it down to a basic open of `Spf A`.

Step 3 is where the formal-scheme input is spent, and it is spent twice: once through
`FormalSpectrum.isUnit_germ_top_iff` (`FormalSchemes/SpfGammaBase.lean`), which is what identifies
`FormalSpectrum.basicOpen` with the `RingedSpace.basicOpen` of a global section and so makes the
sheaf-theoretic transport available at all, and once through
`basicOpen_basicOpenChart_is_basicOpen`. Mathlib's corresponding inputs are
`IsAffineOpen.basicOpen_basicOpen_is_basicOpen` and the affine-scheme sections API.

## Main results

* `FormalSpectrum.mem_ringedSpaceBasicOpen_iff`, `FormalSpectrum.ringedSpaceBasicOpen_symm_eq`,
  `FormalSpectrum.ringedSpaceBasicOpen_eq`: `FormalSpectrum.basicOpen` *is* the
  `RingedSpace.basicOpen` of the corresponding global section. This is the bridge that lets
  Mathlib's `RingedSpace`/`LocallyRingedSpace` basic-open API act on `Spf`.
* `FormalSpectrum.range_basicOpenChart_comp`, `FormalSpectrum.range_basicOpenChart_one_comp`: the
  range of a refined chart is the image of the basic open, and refining at `1` changes nothing.
* `FormalSpectrum.exists_basicOpenChart_le_affine_inter`: **the main result**, the range equality.
* `FormalSpectrum.exists_basicOpenChart_inter_iso`: the same, packaged as an isomorphism *over*
  `X`, with both factorisations — the form a consumer wants.
* `FormalSpectrum.exists_basicOpenChart_le_affine_inter_self`,
  `FormalSpectrum.exists_basicOpenChart_le_affine_inter_two_charts`: non-vacuity, degenerate and
  genuinely two-chart.

## What is *not* proved

* **The composition law.** Wiring this lemma into a `trans` for
  `AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHom` is not done here. It has since been done
  elsewhere: `AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHom.trans`
  (`FormalSchemes.TopFiniteTypeHomTrans`), which consumes
  `FormalSpectrum.exists_basicOpenChart_inter_iso` below together with the transport of one
  witness onto the other's ring up to cofinality of the two ideals of definition
  (`FormalSchemes.CofinalTopFiniteType`, `FormalSchemes.CofinalStructMap`).
* **That an arbitrary affine open of `Spf I` is topologically of finite type over `(R, I)`.**
  Untouched here, and still open. It used to be called conservativity's hard direction and it is
  not: `AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHom.isRelativelyTopFiniteType_of_fg`
  (`FormalSchemes.TargetBasicRefinement`) proves conservativity without it, by refining the cover
  of the *target* — which it does with this file's
  `FormalSpectrum.exists_basicOpenChart_le_affine_inter`, read against the identity of `Spf I`.
  This file is what both of them run on:
  `IsTopologicallyFiniteType.of_openImmersion_of_isCofinal`
  (`FormalSchemes.AffineOpenTopFiniteType`, issue 1207) applies
  `FormalSpectrum.exists_basicOpenChart_inter_iso` below at every point of the affine open, and
  feeds the results to affine-locality (`IsTopologicallyFiniteType.of_span_awayCompletion`,
  `FormalSchemes.TopFiniteTypeAffineLocal`). What is missing is no longer the chart identification
  but a hypothesis of that theorem: that the open immersion is adic up to cofinality.
* **A `FormalScheme.Hom`-level restatement.** None is given, and none is needed: a consumer
  holding `m : FormalScheme.Spf L ⟶ X` applies the results below to `m.toLRSHom`, since
  `FormalScheme.Hom` is a one-field wrapper and `(f ≫ g).toLRSHom = f.toLRSHom ≫ g.toLRSHom`
  holds by `rfl`. Stating them for `LocallyRingedSpace` is strictly more general: `X` is not
  required to be a formal scheme, only to receive the two charts.
* **Anything about the *sections* of the common refinement.** The output is a range equality and
  the isomorphism it induces; `A{1/g}^` and `A'{1/g'}^` are not identified as algebras, and
  neither `FormalSpectrum.awayCompletionNestedAlgEquiv` nor
  `FormalSpectrum.awayCompletionAwayEquiv` is used. With
  `E=':!FormalSchemes/TwoChartBasicOpen.lean'`,
  `git grep -nE "NestedAlgEquiv|awayCompletionAwayEquiv" -- FormalSchemes/TwoChartBasicOpen.lean
  FormalSchemes/BasicOpenChartImage.lean "$E"` returns rc=1. The exclusion is needed because the
  two sentences above name both identifiers, so without it the grep returns rc=0 matching only
  this paragraph; it is there for no other reason, and in particular
  `FormalSchemes/BasicOpenChartImage.lean` is *not* excluded.

## One measurement that changed the route

Mathlib's argument spends `AlgebraicGeometry.RingedSpace.basicOpen_res` twice — once inside
`IsAffineOpen.basicOpen_basicOpen_is_basicOpen` and once in `exists_basicOpen_le_affine_inter`, to
say that restricting `g` to `D(f)` cuts out `D(f) ⊓ D(g) = D(g)`. It was expected to be a separate
cost here, since the tree had no analogue of it. **It is not needed.** The restrict-then-absorb
step is replaced by a preimage-then-image step: the section is pulled back along the lift `ℓ` at
`U = ⊤` (so `LocallyRingedSpace.preimage_basicOpen` applies with no restriction map at all), and
the containment `D(g') ⊆ Set.range ℓ.base` is spent at the very end, on
`Set.image_preimage_eq_inter_range`, instead of inside the presheaf.

With `E=':!FormalSchemes/TwoChartBasicOpen.lean'`,
`git grep -nE "basicOpen_res" -- FormalSchemes/ "$E"` returns rc=1: the lemma still has no
analogue on the tree and this development did not need one. Without the exclusion the same grep
returns rc=0, matching only this file's own prose — which is why the exclusion is there, and it is
there for no other reason.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.13.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
* `Mathlib/AlgebraicGeometry/AffineScheme.lean` — `exists_basicOpen_le_affine_inter`, the template.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FormalSpectrum

section Bridge

variable {A : Type u} [CommRing A] [TopologicalSpace A] (L : Ideal A) [IsAdicRing L]

/-!
### `FormalSpectrum.basicOpen` as a `RingedSpace.basicOpen`

`FormalSpectrum.basicOpen L r` is defined combinatorially, as `PrimeSpectrum.basicOpen` of the
residue of `r`. The three lemmas here identify it with the locus where the germ of the
corresponding global section is invertible, which is the form Mathlib's
`LocallyRingedSpace.preimage_basicOpen` and `RingedSpace.basicOpen_res` speak about. All three are
`FormalSpectrum.isUnit_germ_top_iff` (`FormalSchemes/SpfGammaBase.lean`) restated; that theorem is
the whole content.
-/

/-- A point lies in the `RingedSpace` basic open of the global section attached to `r : A`
exactly when it lies in `FormalSpectrum.basicOpen L r`. -/
theorem mem_ringedSpaceBasicOpen_iff (r : A) (x : FormalSpectrum L) :
    x ∈ (locallyRingedSpaceObj L).toRingedSpace.basicOpen ((globalSectionsEquiv L).symm r)
      ↔ x ∈ basicOpen L r :=
  (RingedSpace.mem_basicOpen (locallyRingedSpaceObj L).toRingedSpace
    (U := ⊤) ((globalSectionsEquiv L).symm r) x trivial).trans (isUnit_germ_top_iff L x r)

/-- **`FormalSpectrum.basicOpen` is a `RingedSpace.basicOpen`**: `D(r) ⊆ Spf A` is the locus where
the germ of the global section corresponding to `r : A` is invertible. -/
theorem ringedSpaceBasicOpen_symm_eq (r : A) :
    (locallyRingedSpaceObj L).toRingedSpace.basicOpen ((globalSectionsEquiv L).symm r)
      = basicOpen L r :=
  Opens.ext (Set.ext fun x => mem_ringedSpaceBasicOpen_iff L r x)

/-- The same identification read in the other direction: the `RingedSpace` basic open of *any*
global section of `O_{Spf A}` is a `FormalSpectrum.basicOpen`, namely that of the element of `A`
it corresponds to under `FormalSpectrum.globalSectionsEquiv`. This is the direction the main
result below uses: there the section arrives by pullback, and its `A`-avatar is read off
afterwards. -/
theorem ringedSpaceBasicOpen_eq
    (u : (structureSheaf L).presheaf.obj (op (⊤ : Opens (FormalSpectrum L)))) :
    (locallyRingedSpaceObj L).toRingedSpace.basicOpen u
      = basicOpen L (globalSectionsEquiv L u) := by
  rw [← ringedSpaceBasicOpen_symm_eq L (globalSectionsEquiv L u), RingEquiv.symm_apply_apply]

end Bridge

/-!
### The refined charts

From here on `A` carries no topology and `L` is not assumed adic: the statements below are about
the underlying spaces and the open immersions between them, and the adic hypotheses they do need
are the ones on the *second* chart, carried explicitly by the binders of each theorem.
-/

variable {A : Type u} [CommRing A] {L : Ideal A}

/-- The range of a refined chart `Spf A{1/g}^ ⟶ Spf A ⟶ X` is the image of `D(g)`. -/
theorem range_basicOpenChart_comp {X : LocallyRingedSpace.{u}} (hL : L.FG)
    (m : locallyRingedSpaceObj L ⟶ X) (g : A) :
    Set.range (basicOpenChart L g ≫ m).base
      = m.base '' (basicOpen L g : Set (FormalSpectrum L)) := by
  have h : Set.range (basicOpenChart L g ≫ m).base
      = m.base '' Set.range (basicOpenChart L g).base := by
    rw [← Set.range_comp]; rfl
  rw [h, range_basicOpenChart_base L g hL]

/-!
### The main result
-/

/-- **Two affine charts of a locally ringed space have a common basic-open neighbourhood.** Given
open immersions `m : Spf A ⟶ X` and `m' : Spf A' ⟶ X` and a point `x` in the range of both, there
are `g : A` and `g' : A'` whose refined charts `Spf A{1/g}^ ⟶ X` and `Spf A'{1/g'}^ ⟶ X` have the
same range, and `x` lies in it.

The formal-geometry analogue of `AlgebraicGeometry.exists_basicOpen_le_affine_inter`. Note that
the conclusion is an equality of *ranges*: the two completed localizations are not claimed to be
isomorphic as algebras, and the isomorphism over `X` that a consumer wants is obtained from the
range equality in `exists_basicOpenChart_inter_iso` below. -/
theorem exists_basicOpenChart_le_affine_inter {X : LocallyRingedSpace.{u}}
    (hL : L.FG)
    {A' : Type u} [CommRing A'] [TopologicalSpace A'] {L' : Ideal A'} [IsAdicRing L']
    (hL' : L'.FG)
    (m : locallyRingedSpaceObj L ⟶ X) [Hm : LocallyRingedSpace.IsOpenImmersion m]
    (m' : locallyRingedSpaceObj L' ⟶ X) [Hm' : LocallyRingedSpace.IsOpenImmersion m']
    (x : X) (hx : x ∈ Set.range m.base) (hx' : x ∈ Set.range m'.base) :
    ∃ (g : A) (g' : A'),
      Set.range (basicOpenChart L g ≫ m).base
          = Set.range (basicOpenChart L' g' ≫ m').base ∧
        x ∈ Set.range (basicOpenChart L g ≫ m).base := by
  obtain ⟨y, hy⟩ := hx
  obtain ⟨y', hy'⟩ := hx'
  -- (1) a basic open of `Spf A` through `y` whose image lands in the range of `m'`
  have hopen1 : IsOpen (m.base ⁻¹' Set.range m'.base) :=
    (Hm'.base_open.isOpen_range).preimage Hm.base_open.continuous
  have hmem1 : y ∈ m.base ⁻¹' Set.range m'.base := by
    rw [Set.mem_preimage, hy]; exact ⟨y', hy'⟩
  obtain ⟨v, ⟨g₀, hg₀⟩, hyv, hv⟩ :=
    (isTopologicalBasis_basicOpen L).exists_subset_of_mem_open hmem1 hopen1
  subst hg₀
  -- (2) its image `W`, an open of `X` inside the range of `m'`
  set W : Set X := m.base '' (basicOpen L g₀ : Set (FormalSpectrum L)) with hW
  have hWopen : IsOpen W := Hm.base_open.isOpenMap _ (basicOpen L g₀).isOpen
  have hxW : x ∈ W := ⟨y, hyv, hy⟩
  -- (3) a basic open of `Spf A'` through `y'` inside the preimage of `W`
  have hopen2 : IsOpen (m'.base ⁻¹' W) := hWopen.preimage Hm'.base_open.continuous
  have hmem2 : y' ∈ m'.base ⁻¹' W := by rw [Set.mem_preimage, hy']; exact hxW
  obtain ⟨v', ⟨g', hg'⟩, hy'v, hv'⟩ :=
    (isTopologicalBasis_basicOpen L').exists_subset_of_mem_open hmem2 hopen2
  subst hg'
  -- (4) the chart over `W`, and its lift through `m'`; the lift has range `m'⁻¹(W)`
  haveI : LocallyRingedSpace.IsOpenImmersion (basicOpenChart L g₀) :=
    isOpenImmersion_basicOpenChart L g₀ hL
  have hcrange : Set.range (basicOpenChart L g₀ ≫ m).base = W :=
    range_basicOpenChart_comp hL m g₀
  have hsub : Set.range (basicOpenChart L g₀ ≫ m).base ⊆ Set.range m'.base := by
    rw [hcrange]
    rintro _ ⟨z, hz, rfl⟩
    exact hv hz
  set ℓ := LocallyRingedSpace.IsOpenImmersion.lift m' (basicOpenChart L g₀ ≫ m) hsub with hℓdef
  have hfac : ℓ ≫ m' = basicOpenChart L g₀ ≫ m :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac m' (basicOpenChart L g₀ ≫ m) hsub
  have hℓrange : Set.range ℓ.base = m'.base ⁻¹' W := by
    rw [hℓdef, LocallyRingedSpace.IsOpenImmersion.lift_range, hcrange]
  -- (5) pull the global section cutting out `D(g')` back along the lift
  haveI : IsAdicRing (awayCompletionIdeal L g₀) := isAdicRing_awayCompletionIdeal L g₀ hL
  have hpre := LocallyRingedSpace.preimage_basicOpen ℓ
    (U := (⊤ : Opens (FormalSpectrum L'))) ((globalSectionsEquiv L').symm g')
  rw [ringedSpaceBasicOpen_symm_eq L' g'] at hpre
  set u := (ConcreteCategory.hom (ℓ.c.app (op (⊤ : Opens (FormalSpectrum L')))))
    ((globalSectionsEquiv L').symm g') with hu
  have hpre2 : (Opens.map ℓ.base).obj (basicOpen L' g')
      = basicOpen (awayCompletionIdeal L g₀)
        (globalSectionsEquiv (awayCompletionIdeal L g₀) u) :=
    hpre.trans (ringedSpaceBasicOpen_eq (awayCompletionIdeal L g₀) u)
  -- (6) and carry it down to a basic open of `Spf A`
  obtain ⟨g, hg⟩ := basicOpen_basicOpenChart_is_basicOpen L g₀ hL
    (globalSectionsEquiv (awayCompletionIdeal L g₀) u)
  have hS : (basicOpen (awayCompletionIdeal L g₀)
        (globalSectionsEquiv (awayCompletionIdeal L g₀) u) :
        Set (FormalSpectrum (awayCompletionIdeal L g₀)))
      = ℓ.base ⁻¹' (basicOpen L' g' : Set (FormalSpectrum L')) := by
    rw [← hpre2]; rfl
  have himg : ∀ T : Set (FormalSpectrum (awayCompletionIdeal L g₀)),
      m.base '' (basicOpenChartBase L g₀ '' T) = m'.base '' (ℓ.base '' T) := by
    intro T
    rw [← Set.image_comp, ← Set.image_comp]
    exact show (basicOpenChart L g₀ ≫ m).base '' T = (ℓ ≫ m').base '' T by rw [hfac]
  have hEq : Set.range (basicOpenChart L g ≫ m).base
      = Set.range (basicOpenChart L' g' ≫ m').base := by
    rw [range_basicOpenChart_comp hL m g, range_basicOpenChart_comp hL' m' g', ← hg]
    refine (himg _).trans ?_
    congr 1
    rw [hS, Set.image_preimage_eq_inter_range, hℓrange]
    exact Set.inter_eq_self_of_subset_left hv'
  refine ⟨g, g', hEq, ?_⟩
  rw [hEq, range_basicOpenChart_comp hL' m' g']
  exact ⟨y', hy'v, hy'⟩

/-- **The common refinement, as a formal spectrum over `X`.** The range equality of
`exists_basicOpenChart_le_affine_inter` upgrades, through
`LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq`, to an isomorphism of the two refined charts
*commuting with their inclusions into `X`* — which is the datum a factorisation obligation
consumes, and the reason the main theorem is stated as an equality of ranges. -/
theorem exists_basicOpenChart_inter_iso {X : LocallyRingedSpace.{u}}
    (hL : L.FG)
    {A' : Type u} [CommRing A'] [TopologicalSpace A'] {L' : Ideal A'} [IsAdicRing L']
    (hL' : L'.FG)
    (m : locallyRingedSpaceObj L ⟶ X) [LocallyRingedSpace.IsOpenImmersion m]
    (m' : locallyRingedSpaceObj L' ⟶ X) [LocallyRingedSpace.IsOpenImmersion m']
    (x : X) (hx : x ∈ Set.range m.base) (hx' : x ∈ Set.range m'.base) :
    ∃ (g : A) (g' : A')
      (e : locallyRingedSpaceObj (awayCompletionIdeal L g)
            ≅ locallyRingedSpaceObj (awayCompletionIdeal L' g')),
      e.hom ≫ (basicOpenChart L' g' ≫ m') = basicOpenChart L g ≫ m ∧
        e.inv ≫ (basicOpenChart L g ≫ m) = basicOpenChart L' g' ≫ m' ∧
          x ∈ Set.range (basicOpenChart L g ≫ m).base := by
  obtain ⟨g, g', hEq, hxg⟩ := exists_basicOpenChart_le_affine_inter hL hL' m m' x hx hx'
  haveI : LocallyRingedSpace.IsOpenImmersion (basicOpenChart L g) :=
    isOpenImmersion_basicOpenChart L g hL
  haveI : LocallyRingedSpace.IsOpenImmersion (basicOpenChart L' g') :=
    isOpenImmersion_basicOpenChart L' g' hL'
  exact ⟨g, g',
    LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq _ _ hEq,
    LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hEq,
    LocallyRingedSpace.IsOpenImmersion.isoOfRangeEq_inv_fac _ _ hEq, hxg⟩

/-!
### Non-vacuity

The hypotheses of the main theorem are satisfiable, in a degenerate and in a genuinely two-chart
way. Both are theorems rather than probes, and both are *applications* of
`exists_basicOpenChart_le_affine_inter` rather than restatements of it — a non-vacuity witness
whose own conclusion is closed by `rfl` would establish nothing. The second is the situation of a
two-chart cover such as `FormalSchemes/FormalLineTwoChartCover.lean`, whose two charts are
basic-open charts of one `Spf` with *different* source rings.
-/

/-- The refinement of a chart at `1` is the chart itself: `D(1) = ⊤`, so `Spf A{1/1}^ ⟶ Spf A ⟶ X`
has the same range as `m`. This is what makes the degenerate case below degenerate. -/
theorem range_basicOpenChart_one_comp {X : LocallyRingedSpace.{u}} (hL : L.FG)
    (m : locallyRingedSpaceObj L ⟶ X) :
    Set.range (basicOpenChart L 1 ≫ m).base = Set.range m.base := by
  rw [range_basicOpenChart_comp hL m 1, basicOpen_one]
  exact Set.image_univ

/-- **Non-vacuity, degenerate case.** The main theorem applied to a chart and *itself*: all of its
hypotheses are simultaneously satisfiable, at `m' = m`, and what it returns there is a genuine
range equality between two refinements of the one chart. Note that this is an *instance* of
`exists_basicOpenChart_le_affine_inter` rather than a restatement — the equality asserted has two
distinct sides, `g` and `g'`, and is not closed by `rfl`.

Nothing forces `g = g' = 1` here: the theorem chooses its own witnesses, and by
`range_basicOpenChart_one_comp` the choice `g = g' = 1` would also do. -/
theorem exists_basicOpenChart_le_affine_inter_self {X : LocallyRingedSpace.{u}}
    [TopologicalSpace A] [IsAdicRing L] (hL : L.FG)
    (m : locallyRingedSpaceObj L ⟶ X) [LocallyRingedSpace.IsOpenImmersion m]
    (x : X) (hx : x ∈ Set.range m.base) :
    ∃ g g' : A, Set.range (basicOpenChart L g ≫ m).base
        = Set.range (basicOpenChart L g' ≫ m).base ∧
      x ∈ Set.range (basicOpenChart L g ≫ m).base :=
  exists_basicOpenChart_le_affine_inter hL hL m m x hx hx

/-- **Non-vacuity, two genuinely different charts.** Two basic-open charts `Spf A{1/t}^ ⟶ Spf A`
and `Spf A{1/t'}^ ⟶ Spf A` of one formal spectrum are open immersions from formal spectra of
*different* rings with *different* ranges `D(t)` and `D(t')`; at a point of `D(t) ∩ D(t')` the
main theorem applies and produces a common basic-open refinement.

This is the shape of every two-chart cover on the tree: the two charts of
`FormalSchemes/FormalLineTwoChartCover.lean` are `basicOpenChart formalLineIdeal 2` and
`basicOpenChart formalLineIdeal 3`, and that file exhibits a point of both basic opens — so the
main result is not vacuous on the covers it was written for. -/
theorem exists_basicOpenChart_le_affine_inter_two_charts (hL : L.FG) (t t' : A)
    (x : FormalSpectrum L) (hx : x ∈ basicOpen L t) (hx' : x ∈ basicOpen L t') :
    ∃ (g : awayCompletion L t) (g' : awayCompletion L t'),
      Set.range (basicOpenChart (awayCompletionIdeal L t) g ≫ basicOpenChart L t).base
          = Set.range (basicOpenChart (awayCompletionIdeal L t') g' ≫ basicOpenChart L t').base ∧
        x ∈ Set.range (basicOpenChart (awayCompletionIdeal L t) g
          ≫ basicOpenChart L t).base := by
  haveI : IsAdicRing (awayCompletionIdeal L t) := isAdicRing_awayCompletionIdeal L t hL
  haveI : IsAdicRing (awayCompletionIdeal L t') := isAdicRing_awayCompletionIdeal L t' hL
  haveI : LocallyRingedSpace.IsOpenImmersion (basicOpenChart L t) :=
    isOpenImmersion_basicOpenChart L t hL
  haveI : LocallyRingedSpace.IsOpenImmersion (basicOpenChart L t') :=
    isOpenImmersion_basicOpenChart L t' hL
  have hfg : ∀ s : A, (awayCompletionIdeal L s).FG := fun s => awayCompletionIdeal_fg L s hL
  refine exists_basicOpenChart_le_affine_inter (hfg t) (hfg t')
    (basicOpenChart L t) (basicOpenChart L t') x ?_ ?_
  · rw [range_basicOpenChart_base L t hL]; exact hx
  · rw [range_basicOpenChart_base L t' hL]; exact hx'

end FormalSpectrum
