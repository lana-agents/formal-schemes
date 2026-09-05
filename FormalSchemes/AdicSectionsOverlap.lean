import FormalSchemes.AdicSectionsChart

set_option linter.style.header false

/-!
# The overlap condition is free: one adic-sections witness supplies both

`AlgebraicGeometry.FormalScheme.homOfGlobalSectionsHomOfAdicSections`
(`FormalSchemes.AdicSectionsChart`) builds a morphism `X ⟶ Spf R` out of `ψ : R →+* Γ(X, 𝒪_X)` from
**two** witnesses: `AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG`, which supplies the charts
and the continuity of `ψ` at each of them, and
`AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.OverlapAdic`, which supplies a chart on every
pairwise overlap that is adic over **both** of the two morphisms into `Spf R` that the gluing
compares there.

**The second witness is not a hypothesis. It follows from the first**, on every formal scheme, with
no finiteness assumption beyond the one the first already carries:
`AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.overlapAdic`.

## Why the pair condition is not the merge problem

`FormalSchemes.AdicSectionsChart` records, correctly, that merging two *unrelated*
`AlgebraicGeometry.FormalScheme.AdicOverBaseLocallyFG` witnesses into one
`AlgebraicGeometry.FormalScheme.AdicOverBasePairLocallyFG` witness is open, and that the obvious
route needs an open immersion to be adic on sections, which issues 460/468/472/487 record as false
in general. **Nothing below merges two witnesses**, and that question stays exactly as open as it
was.

What is used instead is that the pair condition's two bounds are bounds on the *same* chart `c`,
and that

```
globalSectionsMap I c.I (c.map ≫ s)
  = (globalSectionsEquiv c.I).toRingHom.comp
      ((c.map.c.app ⊤).hom.comp (globalSectionsHom I Y s))
```

by `FormalSpectrum.globalSectionsMap_eq_globalSectionsHom` and
`FormalSpectrum.globalSectionsHom_comp`, both of which are `rfl`. So the bound at `c` depends on the
base morphism **only through its global-sections homomorphism**, and a single
`AlgebraicGeometry.FormalScheme.AdicOverBaseLocallyFG` witness for `s` is already a pair witness for
`(s, t)` as soon as `globalSectionsHom I Y s = globalSectionsHom I Y t`
(`AlgebraicGeometry.FormalScheme.pair_of_globalSectionsHom_eq`).

`AlgebraicGeometry.FormalScheme.AdicOverBaseLocallyFG.pair_of_eq` is the `s = t` case of that, and
`FormalSchemes.AdicSectionsChart` says of it that it "records where the joint condition would become
free if the agreement were ever proved independently". **The agreement of the global-sections
homomorphisms is proved independently** — it is `CategoryTheory.Limits.pullback.condition` and
`AlgebraicGeometry.FormalScheme.globalSectionsHom_chartMap`, and neither consumes a bound. It is the
agreement of the *morphisms* that does not have an independent proof, and the pair condition does
not need it.

## The other half: the overlap has enough charts

`AlgebraicGeometry.FormalScheme.adicOverBaseLocallyFG_ofOpenImmersion` transports adicity over a
base along an open immersion into the source. There is no open-immersion-adic-on-sections statement
hiding in it: the chart it produces is
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift` of a chart of the *ambient*, so
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_fac` makes the composite into `Spf R`
equal — on the nose — to the ambient chart's, and the bound transports because it is literally the
same ring homomorphism. The ambient chart is cut down into the range of the open immersion first, by
`AlgebraicGeometry.FormalScheme.exists_affineChart_subset_adicOverBase`.

Applied at `AlgebraicGeometry.FormalScheme.chartOverlap`, whose first projection is an open
immersion into `Spf` of the `i`-th chart's ring, that is all the first leg needs; the second leg
then comes from `AlgebraicGeometry.FormalScheme.pair_of_globalSectionsHom_eq` with no second
computation.

## Main definitions and results

* `AlgebraicGeometry.FormalScheme.pair_of_globalSectionsHom_eq`: **the crux.** A pair witness needs
  only one adic-over-base witness and the agreement of the two base morphisms *on global sections*.
* `AlgebraicGeometry.FormalScheme.adicOverBaseLocallyFG_Spf`: on `Spf J` the identity chart carries
  the bound, so the condition there is exactly continuity of the base morphism's global-sections
  map.
* `AlgebraicGeometry.FormalScheme.adicOverBaseLocallyFG_ofOpenImmersion`: adicity over a base
  transports to the source of an open immersion.
* `AlgebraicGeometry.FormalScheme.globalSectionsHom_pullback_fst_chartMap_eq`: the two morphisms
  compared on an overlap induce the **same** homomorphism on global sections, unconditionally.
* `AlgebraicGeometry.FormalScheme.adicOverBaseLocallyFG_chartMap`: each piece of the chart cover is
  adic over its own chart morphism.
* `AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.overlapAdic`: **the overlap condition holds
  for every witness**, so `AlgebraicGeometry.FormalScheme.homOfGlobalSectionsHomOfAdicSections`
  takes one witness and not two.

## What is *not* proved here

**No witness of `AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG` is produced**, on any formal
scheme. Everything below is conditional on having one; whether any given `X` and `ψ` have one is
untouched, and a scheme admitting none is not excluded.

**The merge question is not settled.** Whether
`AlgebraicGeometry.FormalScheme.AdicOverBaseLocallyFG Y s` together with
`AlgebraicGeometry.FormalScheme.AdicOverBaseLocallyFG Y t` gives
`AlgebraicGeometry.FormalScheme.AdicOverBasePairLocallyFG I Y s t` for *unrelated* `s` and `t` is
still open, and nothing below bears on it —
`AlgebraicGeometry.FormalScheme.pair_of_globalSectionsHom_eq` assumes the two base morphisms have
the same global-sections homomorphism, which is a hypothesis and not a consequence of having two
witnesses.

**Nothing here says an open immersion is adic on sections.** That statement is recorded as false in
general and is not used, weakened or re-opened. The transport lemma above moves a bound *forward*
along `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift`, where the composite is equal to
the ambient chart by `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_fac`; the false
statement is about moving a bound between two *incomparable* charts at a point, which never happens
below.

**The bridge to `AlgebraicGeometry.FormalScheme.SpfHomContinuity` still runs one way only.**
`FormalSchemes.AdicSectionsChart`'s analysis of that is untouched: the bundle states its bounds at
`AlgebraicGeometry.FormalScheme.overlapChartOf`, a chart described by nothing, and nothing below
produces a bound at a chart it did not itself choose.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.4 (10.4.6), §10.6.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry CategoryTheory.Limits
open FormalSpectrum

namespace AlgebraicGeometry.FormalScheme

open OpenCover

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]

/-! ### The pair condition from one witness -/

variable {Y : FormalScheme.{u}} {s t : Y.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I}

/-- **The pair condition needs only the agreement of the two base morphisms on global sections.**
Both bounds of `AlgebraicGeometry.FormalScheme.AdicOverBasePairLocallyFG` are taken at the *same*
chart `c`, and `FormalSpectrum.globalSectionsMap I c.I (c.map ≫ s)` factors through
`FormalSpectrum.globalSectionsHom I Y s` by two `rfl`s
(`FormalSpectrum.globalSectionsMap_eq_globalSectionsHom` and
`FormalSpectrum.globalSectionsHom_comp`). So a bound over `s` at a chart *is* a bound over `t` at
that chart, as soon as the two global-sections homomorphisms agree.

This strictly weakens the hypothesis of
`AlgebraicGeometry.FormalScheme.AdicOverBaseLocallyFG.pair_of_eq`, which asks for `s = t`. The
weakening is what matters: on an overlap the two morphisms do agree, but the only proof of *that*
consumes the bounds this condition supplies, whereas the agreement of the two global-sections
homomorphisms is `CategoryTheory.Limits.pullback.condition` and needs nothing. -/
theorem pair_of_globalSectionsHom_eq (h : AdicOverBaseLocallyFG Y s)
    (hst : globalSectionsHom I Y.toLocallyRingedSpace s
      = globalSectionsHom I Y.toLocallyRingedSpace t) :
    AdicOverBasePairLocallyFG I Y s t := by
  intro y
  obtain ⟨S, _, _, J, _, f, hJfg, hmem, hoi, hadic⟩ := h y
  haveI := hoi
  refine ⟨{ R := S, I := J, map := f, mem := hmem }, hJfg, hadic, ?_⟩
  have key : globalSectionsMap I J (f ≫ t) = globalSectionsMap I J (f ≫ s) := by
    rw [globalSectionsMap_eq_globalSectionsHom, globalSectionsMap_eq_globalSectionsHom,
      globalSectionsHom_comp, globalSectionsHom_comp, hst]
  change I ≤ J.comap (globalSectionsMap I J (f ≫ t))
  rw [key]
  exact hadic

/-! ### Where the charts come from -/

set_option backward.isDefEq.respectTransparency false in
/-- **On `Spf J` the identity is a chart, so adicity over a base is continuity of its
global-sections map.** This is the adic-over-base counterpart of
`AlgebraicGeometry.FormalScheme.adicSectionsLocallyFG_Spf`, and it fills its open-immersion field
the same way — with an explicit `@`-application supplying `CategoryTheory.IsIso.id`, because
instance synthesis does not find `IsIso (𝟙 (FormalSpectrum.locallyRingedSpaceObj J))` at that
position inside a structure literal. -/
theorem adicOverBaseLocallyFG_Spf {S : Type u} [CommRing S] [TopologicalSpace S] {J : Ideal S}
    [IsAdicRing J] (hJ : J.FG)
    (g : (FormalScheme.Spf J).toLocallyRingedSpace ⟶ locallyRingedSpaceObj I)
    (hg : I ≤ J.comap (globalSectionsMap I J g)) :
    AdicOverBaseLocallyFG (FormalScheme.Spf J) g := fun x =>
  ⟨S, inferInstance, inferInstance, J, inferInstance, 𝟙 _, hJ, ⟨x, rfl⟩,
    @LocallyRingedSpace.IsOpenImmersion.of_isIso _ _ (𝟙 _) (CategoryTheory.IsIso.id _),
    by
      have hid : (𝟙 (locallyRingedSpaceObj J) ≫ g) = g := Category.id_comp g
      rw [hid]
      exact hg⟩

set_option backward.isDefEq.respectTransparency false in
/-- **Adicity over a base transports to the source of an open immersion.** The chart produced at a
point of `W` is `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift` of an adic-over-base
chart of the ambient that has first been cut down into the range of `j`
(`AlgebraicGeometry.FormalScheme.exists_affineChart_subset_adicOverBase`), so
`AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.lift_fac` makes its composite into `Spf R`
equal to the ambient chart's and the bound is carried over unchanged.

This is `AlgebraicGeometry.FormalScheme.exists_lifted_affineChart`
(`FormalSchemes.OpenImmersionSourceFormalScheme`) with the bound added and the factorisation used
rather than discarded; that lemma cannot be reused, because it does not record which chart of the
ambient its lift came from. -/
theorem adicOverBaseLocallyFG_ofOpenImmersion {W : LocallyRingedSpace.{u}}
    (j : W ⟶ Y.toLocallyRingedSpace) [H : LocallyRingedSpace.IsOpenImmersion j]
    (hlfg : Y.LocallyFG) (hY : AdicOverBaseLocallyFG Y s) :
    AdicOverBaseLocallyFG (ofOpenImmersion j hlfg) (j ≫ s) := by
  intro x
  have hjopen : IsOpen (Set.range j.base) := H.base_open.isOpen_range
  obtain ⟨K, _, _, KI, _, fc, hKfg, hxc, hsub, hoic, hadic⟩ :=
    exists_affineChart_subset_adicOverBase Y s hY (j.base x) (Set.range j.base) hjopen ⟨x, rfl⟩
  haveI := H
  letI := hoic
  refine ⟨K, ‹_›, ‹_›, KI, ‹_›, ?_, hKfg, ?_, ?_, ?_⟩
  · exact (LocallyRingedSpace.IsOpenImmersion.lift j fc hsub :
      locallyRingedSpaceObj KI ⟶ W)
  · rw [LocallyRingedSpace.IsOpenImmersion.lift_range]
    exact hxc
  · haveI := LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset j fc hsub
    have hlift : LocallyRingedSpace.IsOpenImmersion.lift j fc hsub
        = inv (pullback.snd j fc) ≫ pullback.fst j fc := rfl
    rw [hlift]
    infer_instance
  · rw [← Category.assoc, LocallyRingedSpace.IsOpenImmersion.lift_fac]
    exact hadic

/-! ### The overlap of two charts -/

variable {X : FormalScheme.{u}} (charts : ∀ x : X, AffineChart X x)
variable (ψ : R →+* X.presheaf.obj (op (⊤ : Opens X)))

set_option backward.isDefEq.respectTransparency false in
/-- **The two morphisms compared on an overlap induce the same homomorphism on global sections.**
Both are `ψ` restricted along a leg of the pullback square followed by a cover map, so this is
`CategoryTheory.Limits.pullback.condition` after
`AlgebraicGeometry.FormalScheme.globalSectionsHom_chartMap`.

It is the step of `AlgebraicGeometry.FormalScheme.OpenCover.pullback_fst_comp_eq_snd_comp`'s proof
that carries no continuity hypothesis — that theorem then upgrades it to an equality of *morphisms*
through `FormalSpectrum.hom_ext_of_globalSectionsHom`, which does need bounds. Only the
unconditional half is used below, and that is why nothing here is circular. It occurs inline in
that proof and is not named anywhere; naming it there would be a change to
`FormalSchemes.GlueHomToSpf`, whose reverse closure is larger, so it is restated here. -/
theorem globalSectionsHom_pullback_fst_chartMap_eq
    (hcont : ∀ x, I ≤ (charts x).I.comap (chartHom charts ψ x)) (i j : X) :
    globalSectionsHom I
        (pullback ((ofAffineCharts charts).cmap i) ((ofAffineCharts charts).cmap j))
        (pullback.fst ((ofAffineCharts charts).cmap i) ((ofAffineCharts charts).cmap j) ≫
          chartMap I charts ψ i (hcont i)) =
      globalSectionsHom I
        (pullback ((ofAffineCharts charts).cmap i) ((ofAffineCharts charts).cmap j))
        (pullback.snd ((ofAffineCharts charts).cmap i) ((ofAffineCharts charts).cmap j) ≫
          chartMap I charts ψ j (hcont j)) := by
  have hki : globalSectionsHom I ((ofAffineCharts charts).obj i).toLocallyRingedSpace
      (chartMap I charts ψ i (hcont i)) =
      (((ofAffineCharts charts).cmap i).c.app (op (⊤ : Opens X))).hom.comp ψ :=
    globalSectionsHom_chartMap I charts ψ i (hcont i)
  have hkj : globalSectionsHom I ((ofAffineCharts charts).obj j).toLocallyRingedSpace
      (chartMap I charts ψ j (hcont j)) =
      (((ofAffineCharts charts).cmap j).c.app (op (⊤ : Opens X))).hom.comp ψ :=
    globalSectionsHom_chartMap I charts ψ j (hcont j)
  rw [globalSectionsHom_comp, globalSectionsHom_comp, hki, hkj]
  change (((pullback.fst ((ofAffineCharts charts).cmap i) ((ofAffineCharts charts).cmap j) ≫
      (ofAffineCharts charts).cmap i).c.app (op (⊤ : Opens X))).hom).comp ψ =
    (((pullback.snd ((ofAffineCharts charts).cmap i) ((ofAffineCharts charts).cmap j) ≫
      (ofAffineCharts charts).cmap j).c.app (op (⊤ : Opens X))).hom).comp ψ
  rw [pullback.condition]

/-- `AlgebraicGeometry.FormalScheme.chartMap` induces the chart-restriction of `ψ` on global
sections, in the `FormalSpectrum.globalSectionsMap` spelling the adic-over-base condition is stated
with. -/
theorem globalSectionsMap_chartMap
    (hcont : ∀ x, I ≤ (charts x).I.comap (chartHom charts ψ x)) (x : X) :
    globalSectionsMap I (charts x).I (chartMap I charts ψ x (hcont x)) = chartHom charts ψ x :=
  globalSectionsMap_locallyRingedSpaceMap I (charts x).I _ (hcont x)

set_option backward.isDefEq.respectTransparency false in
/-- **Each piece of the chart cover is adic over its own chart morphism**, by
`AlgebraicGeometry.FormalScheme.adicOverBaseLocallyFG_Spf` at the identity chart: the bound asked
for there is `AlgebraicGeometry.FormalScheme.chartMap`'s own defining continuity hypothesis. -/
theorem adicOverBaseLocallyFG_chartMap (hfg : ∀ x, (charts x).I.FG)
    (hcont : ∀ x, I ≤ (charts x).I.comap (chartHom charts ψ x)) (x : X) :
    AdicOverBaseLocallyFG ((ofAffineCharts charts).obj x) (chartMap I charts ψ x (hcont x)) := by
  refine adicOverBaseLocallyFG_Spf I (hfg x) _ ?_
  rw [globalSectionsMap_chartMap]
  exact hcont x

set_option backward.isDefEq.respectTransparency false in
/-- **The overlap condition holds for every adic-sections witness.** So
`AlgebraicGeometry.FormalScheme.homOfGlobalSectionsHomOfAdicSections` is a construction over
**one** witness, not two, and `AlgebraicGeometry.FormalScheme.AdicSectionsLocallyFG.OverlapAdic` is
not an assumption a caller has to discharge.

Two steps, and neither merges witnesses. The first projection of the overlap is an open immersion
into `Spf` of the `i`-th chart's ring, which is adic over its chart morphism
(`AlgebraicGeometry.FormalScheme.adicOverBaseLocallyFG_chartMap`), so
`AlgebraicGeometry.FormalScheme.adicOverBaseLocallyFG_ofOpenImmersion` gives one chart per point of
the overlap carrying the bound over the **first** leg. The bound over the second leg is then the
same bound, because the two legs agree on global sections
(`AlgebraicGeometry.FormalScheme.globalSectionsHom_pullback_fst_chartMap_eq`) and
`AlgebraicGeometry.FormalScheme.pair_of_globalSectionsHom_eq` says that is all a pair witness
needs.

**This does not say the two legs are equal as morphisms**, and does not reprove
`AlgebraicGeometry.FormalScheme.OpenCover.pullback_fst_comp_eq_snd_comp` — only its
hypothesis-free half is used. -/
theorem AdicSectionsLocallyFG.overlapAdic (hX : AdicSectionsLocallyFG I ψ) : hX.OverlapAdic ψ := by
  intro i j
  refine pair_of_globalSectionsHom_eq I ?_
    (globalSectionsHom_pullback_fst_chartMap_eq I hX.chart ψ hX.cont i j)
  exact adicOverBaseLocallyFG_ofOpenImmersion I
    (pullback.fst ((ofAffineCharts hX.chart).cmap i) ((ofAffineCharts hX.chart).cmap j))
    (ofAffineCharts_obj_locallyFG hX.chart hX.fg_chart i)
    (adicOverBaseLocallyFG_chartMap I hX.chart ψ hX.fg_chart hX.cont i)

end AlgebraicGeometry.FormalScheme

end
