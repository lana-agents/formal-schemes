import FormalSchemes.AwayChartStructMap
import FormalSchemes.ClosedImmersion
import FormalSchemes.CofinalAdicRing
import FormalSchemes.CofinalStructMap
import FormalSchemes.CofinalTopFiniteType
import FormalSchemes.SpfGammaRoundTrip
import FormalSchemes.SpfIsoIdealRecovery
import FormalSchemes.TopFiniteTypeHomComp
import FormalSchemes.TwoChartBasicOpen

set_option linter.style.header false

/-!
# EGA I 10.13's composition law at a non-affine target

`AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHom` (`FormalSchemes.TopFiniteTypeHom`) is EGA I,
10.13's finite-type condition for a morphism of formal schemes at an arbitrary target.
`FormalSchemes.TopFiniteTypeHomComp` proved its composition law for a tower whose middle chart is
**shared** between the two factors, and recorded what separated that from the unconditional
statement. This file removes the hypothesis:

> `IsTopFiniteTypeHom f → IsTopFiniteTypeHom g → IsTopFiniteTypeHom (f ≫ g)`.

## The obstruction, and how it is met

`f : X ⟶ Y` is witnessed against some cover `𝒱` of `Y` and `g : Y ⟶ Z` against another cover
`𝒱'`; nothing relates them. Over a point `y` of the image the two witnesses present the *same*
neighbourhood of `y` as two different affine formal spectra, and a tower needs one middle chart,
not two. The route is the one `FormalSchemes.TopFiniteTypeHomComp` described:

1. **Refine both charts of `Y` to a common basic open.**
   `FormalSpectrum.exists_basicOpenChart_inter_iso` (`FormalSchemes.TwoChartBasicOpen`) produces
   `c`, `d` and an isomorphism `ε : Spf (I{1/c}^) ≅ Spf (M{1/d}^)` commuting with the two
   inclusions into `Y`.
2. **Move the `g`-side witness onto the `f`-side ring.**
   `FormalSpectrum.spfIsoRingEquiv` (`FormalSchemes.SpfIsoIdealRecovery`) turns `ε` into a ring
   isomorphism `σ`, `IsTopologicallyFiniteType.ofAlgEquiv` carries `g`'s witness across it, and
   the resulting ideal `K · (I{1/c}^)` is **cofinal** with `I{1/c}^` — not equal, and that is the
   whole difficulty: `L` against `L ^ 2` is the standing counterexample to equality.
3. **Align the two base ideals.** `IsTopologicallyFiniteType.ofCofinal`
   (`FormalSchemes.CofinalTopFiniteType`) moves the `f`-side witness to the cofinal ideal;
   `IsAdicRing.of_isCofinal` (`FormalSchemes.CofinalAdicRing`) says the result is still an ideal
   of definition, so the middle chart is a formal spectrum; and
   `FormalSpectrum.structMap_comp_generalCofinalSpfIso_inv` (`FormalSchemes.CofinalStructMap`)
   says the comparison isomorphism commutes with the structural morphisms, which is what makes
   the moved witness still factor `f`.
4. **Shrink the `X`-chart over the refined chart of `Y`.**
   `IsTopologicallyFiniteType.awayCompletion_baseChange`
   (`FormalSchemes.AwayBaseChangeTopFiniteType`) makes `A{1/(c·A)}^` tf-type over the shrunk base
   `(R{1/c}^, I{1/c}^)`, and
   `FormalSpectrum.basicOpenChart_comp_structMap_baseChange`
   (`FormalSchemes.AwayChartStructMap`) is the square that keeps the factorisation.
5. **Feed the shared-chart law.** The data assembled at each point of `X` is a
   `AlgebraicGeometry.FormalScheme.TfTypeCompChart`, the covers built from a family of those
   satisfy `AlgebraicGeometry.FormalScheme.IsTfTypeTower`, and
   `IsTfTypeTower.isTopFiniteTypeHom` concludes.

The `g`-side square needs one more ingredient, and it is the only place fullness of `Spf` is used:
the composite `Spf (K · I{1/c}^) ⟶ Spf (I{1/c}^) ⟶ Spf (M{1/d}^) ⟶ Spf K` has to be *the*
structural morphism of the transported witness. Both are morphisms of formal spectra with
continuous global-sections maps, so `FormalSpectrum.locallyRingedSpaceMap_globalSectionsMap`
identifies them once their global-sections maps agree — and they do, by
`FormalSpectrum.globalSectionsMap_generalCofinalSpfIso_hom` (the comparison is invisible on global
sections) together with the definition of `σ`.

## What is *not* proved

**Conservativity** — that at `Y = Spf I` the general notion implies the base-affine one — is
untouched. It needs an *arbitrary* affine open of `Spf I` to be tf-type over `(R, I)`, of which
the tree has only the basic-open case. Nothing here should be read as saying §10.13 is finished.

## Main definitions and results

* `AlgebraicGeometry.FormalScheme.TfTypeCompChart`: the per-point data a composite needs — one
  chart of `X`, one refined chart of `Y`, one chart of `Z`, and a tower of tf-type algebras.
* `AlgebraicGeometry.FormalScheme.nonempty_tfTypeCompChart`: **the construction** — such a chart
  exists at every point of `X`.
* `AlgebraicGeometry.FormalScheme.OpenCover.ofCompCharts`,
  `AlgebraicGeometry.FormalScheme.OpenCover.ofCompChartsTarget`: the two covers assembled from a
  family of composite charts, and `isTfTypeTower_ofCompCharts`, that they form a tower.
* `AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHom.trans`: **EGA I 10.13's composition law.**
* `AlgebraicGeometry.FormalScheme.IsTopFiniteTypeHom.comp_chartMap` and
  `AlgebraicGeometry.FormalScheme.isTopFiniteTypeHom_structHom_comp`: two applications.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.13.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
-/

noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FormalScheme

/-- **An isomorphism of formal spectra, as an isomorphism of formal schemes.** Formal schemes are
a full subcategory of locally ringed spaces, so this is only a repackaging; it is a `def` rather
than an application of `Functor.preimageIso` so that its `Iso.hom` and `Iso.inv` are
`FormalScheme.Hom.mk` on the nose, which is what the squares below are stated against. -/
def spfIsoOfLRS {R S : Type u} [CommRing R] [CommRing S] [TopologicalSpace R] [TopologicalSpace S]
    {I : Ideal R} {J : Ideal S} [IsAdicRing I] [IsAdicRing J]
    (e : FormalSpectrum.locallyRingedSpaceObj I ≅ FormalSpectrum.locallyRingedSpaceObj J) :
    FormalScheme.Spf I ≅ FormalScheme.Spf J where
  hom := Hom.mk e.hom
  inv := Hom.mk e.inv
  hom_inv_id := Hom.ext' (by rw [comp_toLRSHom, id_toLRSHom]; exact e.hom_inv_id)
  inv_hom_id := Hom.ext' (by rw [comp_toLRSHom, id_toLRSHom]; exact e.inv_hom_id)

variable {X Y Z : FormalScheme.{u}}

/-- Pre-composing with an isomorphism does not change what the range of a morphism of formal
schemes contains. Used to move a point of the source chart across the ideal comparison. -/
theorem mem_range_iso_comp {W V U : FormalScheme.{u}} (e : W ≅ V) (φ : V ⟶ U) {u : U}
    (h : u ∈ Set.range φ.toLRSHom.base) : u ∈ Set.range (e.hom ≫ φ).toLRSHom.base := by
  obtain ⟨v, rfl⟩ := h
  refine ⟨e.inv.toLRSHom.base v, ?_⟩
  have hid : e.inv ≫ e.hom ≫ φ = φ := by
    rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
  exact congrArg (fun ψ : V ⟶ U => ψ.toLRSHom.base v) hid

/-- **The per-point data a composite of two finite-type morphisms needs.** At a point `x` of `X`:
an affine chart `src` of `X` through `x`, an affine chart `mid` of `Y`, a chart `k` of `𝒲` with
its identification, and a tower of tf-type algebras `A` over `(B, M)` over `(S, K)` making both
`f` and `g` structural through those charts.

The middle chart is bound **once**, so a family of these is exactly what
`AlgebraicGeometry.FormalScheme.IsTfTypeTower` (`FormalSchemes.TopFiniteTypeHomComp`) consumes:
the shared-chart hypothesis is not weakened, it is *constructed*, which is the content of
`nonempty_tfTypeCompChart`.

The general-target analogue of `AlgebraicGeometry.FormalScheme.TfTypeHomChart`, with the chart of
`Y` carried as a morphism rather than as an index of a fixed cover — the refined charts are built
one point at a time and are not pieces of either given cover. -/
structure TfTypeCompChart (f : X ⟶ Y) (g : Y ⟶ Z) (𝒲 : OpenCover Z) (x : X) where
  S : Type u
  [commRingS : CommRing S]
  [topS : TopologicalSpace S]
  K : Ideal S
  [adicK : IsAdicRing K]
  fgK : K.FG
  k : 𝒲.J
  targetIso : 𝒲.obj k ≅ FormalScheme.Spf K
  B : Type u
  [commRingB : CommRing B]
  [topB : TopologicalSpace B]
  [algSB : Algebra S B]
  M : Ideal B
  [adicM : IsAdicRing M]
  hg : IsTopologicallyFiniteType S K B M
  A : Type u
  [commRingA : CommRing A]
  [topA : TopologicalSpace A]
  [algBA : Algebra B A]
  L : Ideal A
  [adicL : IsAdicRing L]
  hf : IsTopologicallyFiniteType B M A L
  mid : FormalScheme.Spf M ⟶ Y
  [isOpenImmersionMid : LocallyRingedSpace.IsOpenImmersion mid.toLRSHom]
  src : FormalScheme.Spf L ⟶ X
  [isOpenImmersionSrc : LocallyRingedSpace.IsOpenImmersion src.toLRSHom]
  mem : x ∈ Set.range src.toLRSHom.base
  srcCompat : src ≫ f = IsTopologicallyFiniteType.structHom hf ≫ mid
  midCompat : mid ≫ g =
    IsTopologicallyFiniteType.structHom hg ≫ targetIso.inv ≫ 𝒲.map k

attribute [instance] TfTypeCompChart.commRingS TfTypeCompChart.topS TfTypeCompChart.adicK
  TfTypeCompChart.commRingB TfTypeCompChart.topB TfTypeCompChart.algSB TfTypeCompChart.adicM
  TfTypeCompChart.commRingA TfTypeCompChart.topA TfTypeCompChart.algBA TfTypeCompChart.adicL
  TfTypeCompChart.isOpenImmersionSrc TfTypeCompChart.isOpenImmersionMid

set_option maxHeartbeats 1000000 in
-- The statement carries five rings, four ideals and three morphisms, and the proof builds the
-- transported witness on top of all of them, so elaboration needs room. Every chart is kept at a
-- *variable* (`m`, `t`, `t'`) for the reason `FormalScheme.basicOpenChartHom_comp_target` records
-- — instantiating first makes the `FormalScheme.Hom.mk`/`FormalScheme.Hom.toLRSHom` unfolding step
-- time out at
-- `isDefEq`.
set_option synthInstance.maxHeartbeats 1000000 in
-- Instance search runs in a context with five rings and their ideals of definition, and the
-- composite open-immersion instances chain three morphisms; the default budget is not enough.
/-- **The construction, at fixed data.** Given the two witnesses at one point, the common
refinement of the two charts of `Y` produced by `FormalSpectrum.exists_basicOpenChart_inter_iso`,
and the point of the source chart lying over it, this assembles the composite chart.

The three squares it has to check, and where each comes from:

* the source square is `FormalSpectrum.basicOpenChart_comp_structMap_baseChange`
  (`FormalSchemes.AwayChartStructMap`) followed by
  `FormalSpectrum.structMap_comp_generalCofinalSpfIso_inv` (`FormalSchemes.CofinalStructMap`) —
  the shrink of the `X`-chart, then the ideal alignment;
* the target square is `AlgebraicGeometry.basicOpenChart_comp_structMap`
  (`FormalSchemes.RelativeTopFiniteTypeBasis`, already on the tree) followed by the
  identification of the transported structural morphism, which is where `Spf`'s fullness onto
  continuous morphisms enters: `FormalSpectrum.locallyRingedSpaceMap_globalSectionsMap`
  identifies two morphisms of formal spectra whose global-sections maps agree, and they agree by
  `FormalSpectrum.globalSectionsMap_generalCofinalSpfIso_hom`;
* the containment of `x` in the shrunk chart is `FormalSpectrum.map_preimage_basicOpen`: the
  structural morphism pulls `D(c)` back to `D(c · A)`.

Stated at fixed data, separately from `nonempty_tfTypeCompChart`, because every chart has to stay
a *variable*: instantiating `m`, `t`, `t'` before the squares are proved makes the
`FormalScheme.Hom.mk`/`FormalScheme.Hom.toLRSHom` unfolding time out, exactly as
`AlgebraicGeometry.FormalScheme.basicOpenChartHom_comp_target` records. -/
theorem nonempty_tfTypeCompChart_aux {f : X ⟶ Y} {g : Y ⟶ Z} {𝒲 : OpenCover Z}
    {R : Type u} [CommRing R] [TopologicalSpace R] {I : Ideal R} [IsAdicRing I] (hIfg : I.FG)
    {A : Type u} [CommRing A] [TopologicalSpace A] [Algebra R A] {L : Ideal A} [IsAdicRing L]
    (hA : IsTopologicallyFiniteType R I A L)
    {S : Type u} [CommRing S] [TopologicalSpace S] {K : Ideal S} [IsAdicRing K] (hKfg : K.FG)
    {B : Type u} [CommRing B] [TopologicalSpace B] [Algebra S B] {M : Ideal B} [IsAdicRing M]
    (hB : IsTopologicallyFiniteType S K B M)
    (m : FormalScheme.Spf L ⟶ X) [him : LocallyRingedSpace.IsOpenImmersion m.toLRSHom]
    (t : FormalScheme.Spf I ⟶ Y) [hit : LocallyRingedSpace.IsOpenImmersion t.toLRSHom]
    (t' : FormalScheme.Spf M ⟶ Y)
    (k : 𝒲.J) (eZ : 𝒲.obj k ≅ FormalScheme.Spf K)
    (hmf : m ≫ f = IsTopologicallyFiniteType.structHom hA ≫ t)
    (ht'g : t' ≫ g = IsTopologicallyFiniteType.structHom hB ≫ eZ.inv ≫ 𝒲.map k)
    (c : R) (d : B)
    (ε : FormalSpectrum.locallyRingedSpaceObj (FormalSpectrum.awayCompletionIdeal I c) ≅
      FormalSpectrum.locallyRingedSpaceObj (FormalSpectrum.awayCompletionIdeal M d))
    (hεhom : ε.hom ≫ (FormalSpectrum.basicOpenChart M d ≫ t'.toLRSHom) =
      FormalSpectrum.basicOpenChart I c ≫ t.toLRSHom)
    (x : X) (x₀ : FormalSpectrum L) (hx₀ : m.toLRSHom.base x₀ = x)
    (hx₀mem : x₀ ∈ Set.range (FormalSpectrum.basicOpenChart L (algebraMap R A c)).base) :
    Nonempty (TfTypeCompChart f g 𝒲 x) := by
  set mL : FormalSpectrum.locallyRingedSpaceObj L ⟶ X.toLocallyRingedSpace := m.toLRSHom
    with hmL_def
  set tL : FormalSpectrum.locallyRingedSpaceObj I ⟶ Y.toLocallyRingedSpace := t.toLRSHom
    with htL_def
  haveI : LocallyRingedSpace.IsOpenImmersion mL := him
  haveI : LocallyRingedSpace.IsOpenImmersion tL := hit
  have hLfg : L.FG := IsTopologicallyFiniteType.fg hA hIfg
  have hMfg : M.FG := IsTopologicallyFiniteType.fg hB hKfg
  haveI : IsAdicRing (FormalSpectrum.awayCompletionIdeal I c) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal I c hIfg
  haveI : IsAdicRing (FormalSpectrum.awayCompletionIdeal M d) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal M d hMfg
  have hJ₁fg : (FormalSpectrum.awayCompletionIdeal I c).FG :=
    FormalSpectrum.awayCompletionIdeal_fg I c hIfg
  have hJ₂fg : (FormalSpectrum.awayCompletionIdeal M d).FG :=
    FormalSpectrum.awayCompletionIdeal_fg M d hMfg
  have hB₂ : IsTopologicallyFiniteType S K (FormalSpectrum.awayCompletion M d)
      (FormalSpectrum.awayCompletionIdeal M d) :=
    IsTopologicallyFiniteType.awayCompletion d hKfg hB
  letI : Algebra S (FormalSpectrum.awayCompletion I c) :=
    ((FormalSpectrum.spfIsoRingEquiv ε).toRingHom.comp
      (algebraMap S (FormalSpectrum.awayCompletion M d))).toAlgebra
  have hB₃ : IsTopologicallyFiniteType S K (FormalSpectrum.awayCompletion I c)
      (K.map (algebraMap S (FormalSpectrum.awayCompletion I c))) :=
    hB₂.ofAlgEquiv { FormalSpectrum.spfIsoRingEquiv ε with commutes' := fun _ => rfl }
  have hMmid : K.map (algebraMap S (FormalSpectrum.awayCompletion I c)) =
      (FormalSpectrum.awayCompletionIdeal M d).map
        (FormalSpectrum.spfIsoRingEquiv ε).toRingHom := by
    have h1 : (K.map (algebraMap S (FormalSpectrum.awayCompletion M d))).map
        (FormalSpectrum.spfIsoRingEquiv ε).toRingHom =
        K.map (algebraMap S (FormalSpectrum.awayCompletion I c)) := Ideal.map_map _ _
    have h2 : (K.map (algebraMap S (FormalSpectrum.awayCompletion M d))).map
        (FormalSpectrum.spfIsoRingEquiv ε).toRingHom =
        (FormalSpectrum.awayCompletionIdeal M d).map
          (FormalSpectrum.spfIsoRingEquiv ε).toRingHom :=
      congrArg (fun J => Ideal.map (FormalSpectrum.spfIsoRingEquiv ε).toRingHom J) hB₂.map_eq
    exact h1.symm.trans h2
  have hcof : (FormalSpectrum.awayCompletionIdeal I c).IsCofinal
      (K.map (algebraMap S (FormalSpectrum.awayCompletion I c))) := by
    rw [hMmid]
    exact (FormalSpectrum.isCofinal_map_spfIsoRingEquiv ε hJ₁fg hJ₂fg).symm
  haveI : IsAdicRing (K.map (algebraMap S (FormalSpectrum.awayCompletion I c))) :=
    IsAdicRing.of_isCofinal hcof
  have hMmidfg : (K.map (algebraMap S (FormalSpectrum.awayCompletion I c))).FG := by
    rw [hMmid]; exact hJ₂fg.map _
  haveI : IsAdicComplete (I.map (algebraMap R A)) A := by rw [hA.map_eq]; infer_instance
  haveI : IsAdicRing (FormalSpectrum.awayCompletionIdeal L (algebraMap R A c)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal L _ hLfg
  have hL'fg : (FormalSpectrum.awayCompletionIdeal L (algebraMap R A c)).FG :=
    FormalSpectrum.awayCompletionIdeal_fg L (algebraMap R A c) hLfg
  letI := FormalSpectrum.awayBaseAlgebra c hIfg hA.map_eq
  have hA₂ : IsTopologicallyFiniteType (FormalSpectrum.awayCompletion I c)
      (FormalSpectrum.awayCompletionIdeal I c)
      (FormalSpectrum.awayCompletion L (algebraMap R A c))
      (FormalSpectrum.awayCompletionIdeal L (algebraMap R A c)) :=
    IsTopologicallyFiniteType.awayCompletion_baseChange hIfg hA c
  have hA₃ := hA₂.ofCofinal hcof
  haveI : IsAdicRing ((K.map (algebraMap S (FormalSpectrum.awayCompletion I c))).map
      (algebraMap (FormalSpectrum.awayCompletion I c)
        (FormalSpectrum.awayCompletion L (algebraMap R A c)))) :=
    IsAdicRing.of_isCofinal (hA₂.isCofinal_map hcof)
  have hL₃fg : ((K.map (algebraMap S (FormalSpectrum.awayCompletion I c))).map
      (algebraMap (FormalSpectrum.awayCompletion I c)
        (FormalSpectrum.awayCompletion L (algebraMap R A c)))).FG := hMmidfg.map _
  haveI : LocallyRingedSpace.IsOpenImmersion (FormalSpectrum.basicOpenChart I c) :=
    FormalSpectrum.isOpenImmersion_basicOpenChart I c hIfg
  haveI : LocallyRingedSpace.IsOpenImmersion
      (FormalSpectrum.basicOpenChart L (algebraMap R A c)) :=
    FormalSpectrum.isOpenImmersion_basicOpenChart L _ hLfg
  set κN := spfIsoOfLRS (FormalSpectrum.generalCofinalSpfIso
    (K.map (algebraMap S (FormalSpectrum.awayCompletion I c)))
    (FormalSpectrum.awayCompletionIdeal I c) hMmidfg hJ₁fg) with hκN_def
  set κA := spfIsoOfLRS (FormalSpectrum.generalCofinalSpfIso
    ((K.map (algebraMap S (FormalSpectrum.awayCompletion I c))).map
      (algebraMap (FormalSpectrum.awayCompletion I c)
        (FormalSpectrum.awayCompletion L (algebraMap R A c))))
    (FormalSpectrum.awayCompletionIdeal L (algebraMap R A c)) hL₃fg hL'fg) with hκA_def
  set bcI : FormalScheme.Spf (FormalSpectrum.awayCompletionIdeal I c) ⟶ FormalScheme.Spf I :=
    Hom.mk (FormalSpectrum.basicOpenChart I c) with hbcI_def
  set bcL : FormalScheme.Spf (FormalSpectrum.awayCompletionIdeal L (algebraMap R A c)) ⟶
      FormalScheme.Spf L := Hom.mk (FormalSpectrum.basicOpenChart L (algebraMap R A c))
    with hbcL_def
  set bcM : FormalScheme.Spf (FormalSpectrum.awayCompletionIdeal M d) ⟶ FormalScheme.Spf M :=
    Hom.mk (FormalSpectrum.basicOpenChart M d) with hbcM_def
  set εF := spfIsoOfLRS ε with hεF_def
  haveI : IsIso κN.hom.toLRSHom :=
    inferInstanceAs (IsIso (forgetToLocallyRingedSpace.map κN.hom))
  haveI : IsIso κA.hom.toLRSHom :=
    inferInstanceAs (IsIso (forgetToLocallyRingedSpace.map κA.hom))
  have q1 : LocallyRingedSpace.IsOpenImmersion (FormalSpectrum.basicOpenChart I c) :=
    inferInstance
  have q2 : LocallyRingedSpace.IsOpenImmersion tL := inferInstance
  haveI qI : LocallyRingedSpace.IsOpenImmersion (FormalSpectrum.basicOpenChart I c ≫ tL) :=
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ (FormalSpectrum.basicOpenChart I c) q1 tL q2
  have q3 : LocallyRingedSpace.IsOpenImmersion
      (FormalSpectrum.basicOpenChart L (algebraMap R A c)) := inferInstance
  have q4 : LocallyRingedSpace.IsOpenImmersion mL := inferInstance
  haveI qL : LocallyRingedSpace.IsOpenImmersion
      (FormalSpectrum.basicOpenChart L (algebraMap R A c) ≫ mL) :=
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _
      (FormalSpectrum.basicOpenChart L (algebraMap R A c)) q3 mL q4
  have qκN : LocallyRingedSpace.IsOpenImmersion κN.hom.toLRSHom := inferInstance
  have qκA : LocallyRingedSpace.IsOpenImmersion κA.hom.toLRSHom := inferInstance
  haveI hmidoi : LocallyRingedSpace.IsOpenImmersion (κN.hom ≫ bcI ≫ t).toLRSHom :=
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ κN.hom.toLRSHom qκN
      (FormalSpectrum.basicOpenChart I c ≫ tL) qI
  haveI hsrcoi : LocallyRingedSpace.IsOpenImmersion (κA.hom ≫ bcL ≫ m).toLRSHom :=
    @LocallyRingedSpace.IsOpenImmersion.comp _ _ _ κA.hom.toLRSHom qκA
      (FormalSpectrum.basicOpenChart L (algebraMap R A c) ≫ mL) qL
  refine ⟨{ S := S, K := K, fgK := hKfg, k := k, targetIso := eZ
            B := FormalSpectrum.awayCompletion I c
            M := K.map (algebraMap S (FormalSpectrum.awayCompletion I c))
            hg := hB₃
            A := FormalSpectrum.awayCompletion L (algebraMap R A c)
            L := (K.map (algebraMap S (FormalSpectrum.awayCompletion I c))).map
              (algebraMap (FormalSpectrum.awayCompletion I c)
                (FormalSpectrum.awayCompletion L (algebraMap R A c)))
            hf := hA₃
            mid := κN.hom ≫ bcI ≫ t
            src := κA.hom ≫ bcL ≫ m
            mem := ?_
            srcCompat := ?_
            midCompat := ?_ }⟩
  · refine mem_range_iso_comp κA (bcL ≫ m) ?_
    obtain ⟨v, hv⟩ := hx₀mem
    exact ⟨v, (congrArg (fun z => m.toLRSHom.base z) hv).trans hx₀⟩
  · have hchart : bcL ≫ IsTopologicallyFiniteType.structHom hA =
        IsTopologicallyFiniteType.structHom hA₂ ≫ bcI :=
      congrArg Hom.mk (FormalSpectrum.basicOpenChart_comp_structMap_baseChange hIfg hA.map_eq c rfl
        hA₂.map_eq)
    have hsq : IsTopologicallyFiniteType.structHom hA₂ ≫ κN.inv =
        κA.inv ≫ IsTopologicallyFiniteType.structHom hA₃ :=
      congrArg Hom.mk (FormalSpectrum.structMap_comp_generalCofinalSpfIso_inv hMmidfg hJ₁fg
        hA₃.map_eq hA₂.map_eq hL₃fg hL'fg)
    have hkey : κA.hom ≫ IsTopologicallyFiniteType.structHom hA₂ =
        IsTopologicallyFiniteType.structHom hA₃ ≫ κN.hom := by
      calc κA.hom ≫ IsTopologicallyFiniteType.structHom hA₂
          = κA.hom ≫ (IsTopologicallyFiniteType.structHom hA₂ ≫ κN.inv) ≫ κN.hom := by
            rw [Category.assoc, κN.inv_hom_id, Category.comp_id]
        _ = κA.hom ≫ (κA.inv ≫ IsTopologicallyFiniteType.structHom hA₃) ≫ κN.hom := by
            rw [hsq]
        _ = IsTopologicallyFiniteType.structHom hA₃ ≫ κN.hom := by
            rw [← Category.assoc, ← Category.assoc, κA.hom_inv_id, Category.id_comp]
    calc (κA.hom ≫ bcL ≫ m) ≫ f
        = κA.hom ≫ bcL ≫ (m ≫ f) := by rw [Category.assoc, Category.assoc]
      _ = κA.hom ≫ bcL ≫ IsTopologicallyFiniteType.structHom hA ≫ t := by rw [hmf]
      _ = κA.hom ≫ (bcL ≫ IsTopologicallyFiniteType.structHom hA) ≫ t := by
          rw [Category.assoc]
      _ = κA.hom ≫ (IsTopologicallyFiniteType.structHom hA₂ ≫ bcI) ≫ t := by rw [hchart]
      _ = (κA.hom ≫ IsTopologicallyFiniteType.structHom hA₂) ≫ bcI ≫ t := by
          rw [Category.assoc, Category.assoc]
      _ = (IsTopologicallyFiniteType.structHom hA₃ ≫ κN.hom) ≫ bcI ≫ t := by rw [hkey]
      _ = IsTopologicallyFiniteType.structHom hA₃ ≫ κN.hom ≫ bcI ≫ t := by rw [Category.assoc]
  · have hεF : εF.hom ≫ (bcM ≫ t') = bcI ≫ t := congrArg Hom.mk hεhom
    have hchartM : bcM ≫ IsTopologicallyFiniteType.structHom hB =
        IsTopologicallyFiniteType.structHom hB₂ :=
      congrArg Hom.mk (basicOpenChart_comp_structMap d hB hB₂)
    have hΓLRS : (FormalSpectrum.generalCofinalSpfIso
          (K.map (algebraMap S (FormalSpectrum.awayCompletion I c)))
          (FormalSpectrum.awayCompletionIdeal I c) hMmidfg hJ₁fg).hom ≫
        ε.hom ≫ IsTopologicallyFiniteType.structMap hB₂.map_eq =
        IsTopologicallyFiniteType.structMap hB₃.map_eq := by
      have hgs : FormalSpectrum.globalSectionsMap K
          (K.map (algebraMap S (FormalSpectrum.awayCompletion I c)))
          ((FormalSpectrum.generalCofinalSpfIso
            (K.map (algebraMap S (FormalSpectrum.awayCompletion I c)))
            (FormalSpectrum.awayCompletionIdeal I c) hMmidfg hJ₁fg).hom ≫
              ε.hom ≫ IsTopologicallyFiniteType.structMap hB₂.map_eq) =
          algebraMap S (FormalSpectrum.awayCompletion I c) := by
        rw [FormalSpectrum.globalSectionsMap_comp, FormalSpectrum.globalSectionsMap_comp,
          FormalSpectrum.globalSectionsMap_generalCofinalSpfIso_hom,
          FormalSpectrum.globalSectionsMap_structMap, RingHom.id_comp,
          ← FormalSpectrum.spfIsoRingEquiv_toRingHom]
        rfl
      have hround := FormalSpectrum.locallyRingedSpaceMap_globalSectionsMap K
        (K.map (algebraMap S (FormalSpectrum.awayCompletion I c))) hKfg hMmidfg
        ((FormalSpectrum.generalCofinalSpfIso
          (K.map (algebraMap S (FormalSpectrum.awayCompletion I c)))
          (FormalSpectrum.awayCompletionIdeal I c) hMmidfg hJ₁fg).hom ≫
            ε.hom ≫ IsTopologicallyFiniteType.structMap hB₂.map_eq)
        (by rw [hgs]; exact Ideal.map_le_iff_le_comap.mp le_rfl)
      rw [← hround]
      exact FormalSpectrum.locallyRingedSpaceMap_congr _ _ _ _ _ _ hgs
    have hΓ : κN.hom ≫ εF.hom ≫ IsTopologicallyFiniteType.structHom hB₂ =
        IsTopologicallyFiniteType.structHom hB₃ := congrArg Hom.mk hΓLRS
    calc (κN.hom ≫ bcI ≫ t) ≫ g
        = κN.hom ≫ (bcI ≫ t) ≫ g := by rw [Category.assoc]
      _ = κN.hom ≫ (εF.hom ≫ bcM ≫ t') ≫ g := by rw [hεF]
      _ = κN.hom ≫ εF.hom ≫ bcM ≫ (t' ≫ g) := by
          simp only [Category.assoc]
      _ = κN.hom ≫ εF.hom ≫ bcM ≫
            IsTopologicallyFiniteType.structHom hB ≫ eZ.inv ≫ 𝒲.map k := by rw [ht'g]
      _ = κN.hom ≫ εF.hom ≫ (bcM ≫ IsTopologicallyFiniteType.structHom hB) ≫
            eZ.inv ≫ 𝒲.map k := by simp only [Category.assoc]
      _ = κN.hom ≫ εF.hom ≫ IsTopologicallyFiniteType.structHom hB₂ ≫
            eZ.inv ≫ 𝒲.map k := by rw [hchartM]
      _ = (κN.hom ≫ εF.hom ≫ IsTopologicallyFiniteType.structHom hB₂) ≫
            eZ.inv ≫ 𝒲.map k := by simp only [Category.assoc]
      _ = IsTopologicallyFiniteType.structHom hB₃ ≫ eZ.inv ≫ 𝒲.map k := by rw [hΓ]

/-- **A composite chart exists at every point of `X`.** The two witnesses are read at `x` and at
its image `y = f x`, the two resulting charts of `Y` are refined against each other at `y`, and
`nonempty_tfTypeCompChart_aux` assembles the result.

The chart of `𝒱'` is taken at `𝒱'.f y`, so it contains `y`; the chart of `𝒱` is the one `f`'s
witness supplies for `𝒰.f x`, and it contains `y` because `y` is the image of a point of that
chart under the structural morphism. Those two memberships are the hypotheses of
`FormalSpectrum.exists_basicOpenChart_inter_iso`. -/
theorem nonempty_tfTypeCompChart {f : X ⟶ Y} {g : Y ⟶ Z} {𝒲 : OpenCover Z}
    {𝒱 𝒱' : OpenCover Y} {𝒰 : OpenCover X}
    (hf : IsTopFiniteTypeHomOn f 𝒱 𝒰) (hg : IsTopFiniteTypeHomOn g 𝒲 𝒱') (x : X) :
    Nonempty (TfTypeCompChart f g 𝒲 x) := by
  obtain ⟨i₀, R, _, _, I, _, hIfg, A, _, _, _, L, _, hA, e, e', hcomp⟩ := hf (𝒰.f x)
  haveI : IsIso e.inv.toLRSHom :=
    inferInstanceAs (IsIso (forgetToLocallyRingedSpace.map e.inv))
  haveI : IsIso e'.inv.toLRSHom :=
    inferInstanceAs (IsIso (forgetToLocallyRingedSpace.map e'.inv))
  set m : FormalScheme.Spf L ⟶ X := e.inv ≫ 𝒰.map (𝒰.f x) with hm_def
  set t : FormalScheme.Spf I ⟶ Y := e'.inv ≫ 𝒱.map i₀ with ht_def
  haveI hm : LocallyRingedSpace.IsOpenImmersion m.toLRSHom :=
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
      (e.inv.toLRSHom ≫ (𝒰.map (𝒰.f x)).toLRSHom))
  haveI ht : LocallyRingedSpace.IsOpenImmersion t.toLRSHom :=
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
      (e'.inv.toLRSHom ≫ (𝒱.map i₀).toLRSHom))
  have hmf : m ≫ f = IsTopologicallyFiniteType.structHom hA ≫ t := by
    rw [hm_def, ht_def, Category.assoc, hcomp, ← Category.assoc, e.inv_hom_id, Category.id_comp]
  obtain ⟨y₀, hy₀⟩ := 𝒰.covers x
  have hxm : x ∈ Set.range m.toLRSHom.base := by
    refine ⟨e.hom.toLRSHom.base y₀, ?_⟩
    change (e.hom ≫ m).toLRSHom.base y₀ = x
    rw [hm_def, ← Category.assoc, e.hom_inv_id, Category.id_comp]
    exact hy₀
  obtain ⟨x₀, hx₀⟩ := hxm
  -- the image point in `Y`
  set y : Y := f.toLRSHom.base x with hy_def
  have hy_eq : t.toLRSHom.base ((IsTopologicallyFiniteType.structHom hA).toLRSHom.base x₀) = y := by
    have h1 := congrArg (fun φ : FormalScheme.Spf L ⟶ Y => φ.toLRSHom.base x₀) hmf
    simp only [FormalScheme.comp_toLRSHom, LocallyRingedSpace.comp_base, TopCat.comp_app] at h1
    rw [hx₀] at h1
    exact h1.symm
  have hyt : y ∈ Set.range t.toLRSHom.base := ⟨_, hy_eq⟩
  -- the `g`-side chart at `y`
  obtain ⟨k, S, _, _, K, _, hKfg, B, _, _, _, M, _, hB, eY', eZ, hgcomp⟩ := hg (𝒱'.f y)
  haveI : IsIso eY'.inv.toLRSHom :=
    inferInstanceAs (IsIso (forgetToLocallyRingedSpace.map eY'.inv))
  set t' : FormalScheme.Spf M ⟶ Y := eY'.inv ≫ 𝒱'.map (𝒱'.f y) with ht'_def
  haveI ht' : LocallyRingedSpace.IsOpenImmersion t'.toLRSHom :=
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion
      (eY'.inv.toLRSHom ≫ (𝒱'.map (𝒱'.f y)).toLRSHom))
  have ht'g : t' ≫ g = IsTopologicallyFiniteType.structHom hB ≫ eZ.inv ≫ 𝒲.map k := by
    rw [ht'_def, Category.assoc, hgcomp, ← Category.assoc, eY'.inv_hom_id, Category.id_comp]
  have hyt' : y ∈ Set.range t'.toLRSHom.base := by
    obtain ⟨w, hw⟩ := 𝒱'.covers y
    refine ⟨eY'.hom.toLRSHom.base w, ?_⟩
    change (eY'.hom ≫ t').toLRSHom.base w = y
    rw [ht'_def, ← Category.assoc, eY'.hom_inv_id, Category.id_comp]
    exact hw
  have hMfg : M.FG := IsTopologicallyFiniteType.fg hB hKfg
  have hLfg : L.FG := IsTopologicallyFiniteType.fg hA hIfg
  set tL : FormalSpectrum.locallyRingedSpaceObj I ⟶ Y.toLocallyRingedSpace := t.toLRSHom
    with htL_def
  set t'L : FormalSpectrum.locallyRingedSpaceObj M ⟶ Y.toLocallyRingedSpace := t'.toLRSHom
    with ht'L_def
  haveI : LocallyRingedSpace.IsOpenImmersion tL := ht
  haveI : LocallyRingedSpace.IsOpenImmersion t'L := ht'
  obtain ⟨c, d, ε, hεhom, hεinv, hyc⟩ :=
    FormalSpectrum.exists_basicOpenChart_inter_iso (X := Y.toLocallyRingedSpace) (A := R)
      (L := I) (A' := B) (L' := M) hIfg hMfg tL t'L y hyt hyt'
  -- the two refined charts of `Y`
  haveI : IsAdicRing (FormalSpectrum.awayCompletionIdeal I c) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal I c hIfg
  haveI : IsAdicRing (FormalSpectrum.awayCompletionIdeal M d) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal M d hMfg
  have hJ₁fg : (FormalSpectrum.awayCompletionIdeal I c).FG :=
    FormalSpectrum.awayCompletionIdeal_fg I c hIfg
  have hJ₂fg : (FormalSpectrum.awayCompletionIdeal M d).FG :=
    FormalSpectrum.awayCompletionIdeal_fg M d hMfg
  -- the `g`-side witness, transported to the `f`-side ring by the recovered ring isomorphism
  have hB₂ : IsTopologicallyFiniteType S K (FormalSpectrum.awayCompletion M d)
      (FormalSpectrum.awayCompletionIdeal M d) :=
    IsTopologicallyFiniteType.awayCompletion d hKfg hB
  set σ := FormalSpectrum.spfIsoRingEquiv ε with hσ_def
  letI : Algebra S (FormalSpectrum.awayCompletion I c) :=
    (σ.toRingHom.comp (algebraMap S (FormalSpectrum.awayCompletion M d))).toAlgebra
  have hB₃ : IsTopologicallyFiniteType S K (FormalSpectrum.awayCompletion I c)
      (K.map (algebraMap S (FormalSpectrum.awayCompletion I c))) :=
    hB₂.ofAlgEquiv { σ with commutes' := fun _ => rfl }
  have hMmid : K.map (algebraMap S (FormalSpectrum.awayCompletion I c)) =
      (FormalSpectrum.awayCompletionIdeal M d).map σ.toRingHom := by
    rw [← hB₂.map_eq, Ideal.map_map]
    rfl
  have hcof : (FormalSpectrum.awayCompletionIdeal I c).IsCofinal
      (K.map (algebraMap S (FormalSpectrum.awayCompletion I c))) := by
    rw [hMmid]
    exact (FormalSpectrum.isCofinal_map_spfIsoRingEquiv ε hJ₁fg hJ₂fg).symm
  haveI : IsAdicRing (K.map (algebraMap S (FormalSpectrum.awayCompletion I c))) :=
    IsAdicRing.of_isCofinal hcof
  have hMmidfg : (K.map (algebraMap S (FormalSpectrum.awayCompletion I c))).FG := by
    rw [hMmid]; exact hJ₂fg.map _
  -- the `f`-side chart, shrunk over the refined chart of `Y`
  haveI : IsAdicComplete (I.map (algebraMap R A)) A := by rw [hA.map_eq]; infer_instance
  haveI : IsAdicRing (FormalSpectrum.awayCompletionIdeal L (algebraMap R A c)) :=
    FormalSpectrum.isAdicRing_awayCompletionIdeal L _ hLfg
  have hL'fg : (FormalSpectrum.awayCompletionIdeal L (algebraMap R A c)).FG :=
    FormalSpectrum.awayCompletionIdeal_fg L (algebraMap R A c) hLfg
  letI := FormalSpectrum.awayBaseAlgebra c hIfg hA.map_eq
  have hA₂ : IsTopologicallyFiniteType (FormalSpectrum.awayCompletion I c)
      (FormalSpectrum.awayCompletionIdeal I c)
      (FormalSpectrum.awayCompletion L (algebraMap R A c))
      (FormalSpectrum.awayCompletionIdeal L (algebraMap R A c)) :=
    IsTopologicallyFiniteType.awayCompletion_baseChange hIfg hA c
  have hA₃ := hA₂.ofCofinal hcof
  have hcofA := hA₂.isCofinal_map hcof
  haveI : IsAdicRing ((K.map (algebraMap S (FormalSpectrum.awayCompletion I c))).map
      (algebraMap (FormalSpectrum.awayCompletion I c)
        (FormalSpectrum.awayCompletion L (algebraMap R A c)))) :=
    IsAdicRing.of_isCofinal hcofA
  have hL₃fg : ((K.map (algebraMap S (FormalSpectrum.awayCompletion I c))).map
      (algebraMap (FormalSpectrum.awayCompletion I c)
        (FormalSpectrum.awayCompletion L (algebraMap R A c)))).FG := hMmidfg.map _
  -- the point `x₀` lies in the shrunk source chart
  obtain ⟨w, hw⟩ := hyc
  have hstructmem : (IsTopologicallyFiniteType.structHom hA).toLRSHom.base x₀ ∈
      Set.range (FormalSpectrum.basicOpenChart I c).base := by
    refine ⟨w, ?_⟩
    refine ht.base_open.injective ?_
    simp only [LocallyRingedSpace.comp_base, TopCat.comp_app] at hw
    exact hw.trans hy_eq.symm
  have hx₀mem : x₀ ∈ Set.range (FormalSpectrum.basicOpenChart L (algebraMap R A c)).base := by
    rw [FormalSpectrum.range_basicOpenChart_base L _ hLfg]
    rw [FormalSpectrum.range_basicOpenChart_base I c hIfg] at hstructmem
    have : x₀ ∈ (TopologicalSpace.Opens.map
        (FormalSpectrum.mapTop I L (algebraMap R A)
          (Ideal.map_le_iff_le_comap.mp hA.map_eq.le))).obj (FormalSpectrum.basicOpen I c) :=
      hstructmem
    rwa [FormalSpectrum.map_preimage_basicOpen] at this
  exact nonempty_tfTypeCompChart_aux hIfg hA hKfg hB m t t' k eZ hmf ht'g c d ε hεhom x x₀ hx₀
    hx₀mem

variable {f : X ⟶ Y} {g : Y ⟶ Z} {𝒲 : OpenCover Z}

/-- **The cover of `X` assembled from a supplied family of composite charts**, indexed by the
points of `X`. The family is an argument rather than an internal `Classical.choice`, for the
reason `AlgebraicGeometry.FormalScheme.OpenCover.ofTfTypeHomCharts` records: a cover whose charts
are chosen internally cannot carry any property the caller did not put into the chart type. -/
def OpenCover.ofCompCharts (charts : ∀ x : X, TfTypeCompChart f g 𝒲 x) : OpenCover X where
  J := X
  obj x := FormalScheme.Spf (charts x).L
  map x := (charts x).src
  f x := x
  covers x := (charts x).mem
  isOpenImmersion x := (charts x).isOpenImmersionSrc

/-- **The cover of `Y` assembled from a family of composite charts, together with a filler cover.**

The charts are indexed by the points of `X`, so they cover only the image of `f`; the second
summand is what makes the result a cover of `Y`. Its pieces carry no tf-type data and need none —
`AlgebraicGeometry.FormalScheme.IsTfTypeTower` quantifies over the charts of the *source* cover,
and every one of those is matched with a piece from the first summand. -/
def OpenCover.ofCompChartsTarget (𝒱₀ : OpenCover Y)
    (charts : ∀ x : X, TfTypeCompChart f g 𝒲 x) : OpenCover Y where
  J := X ⊕ 𝒱₀.J
  obj := Sum.elim (fun x => FormalScheme.Spf (charts x).M) 𝒱₀.obj
  map j := match j with
    | .inl x => (charts x).mid
    | .inr i => 𝒱₀.map i
  f y := .inr (𝒱₀.f y)
  covers y := 𝒱₀.covers y
  isOpenImmersion j := match j with
    | .inl x => (charts x).isOpenImmersionMid
    | .inr i => 𝒱₀.isOpenImmersion i

/-- **The two assembled covers form a tower.** Every field of
`AlgebraicGeometry.FormalScheme.IsTfTypeTower` is a field of the chart at that point, and both
identifications of the middle chart are `Iso.refl` — the chart *is* `Spf` of its own ring, which
is the point of building the cover out of the charts rather than refining a given one. -/
theorem isTfTypeTower_ofCompCharts (𝒱₀ : OpenCover Y)
    (charts : ∀ x : X, TfTypeCompChart f g 𝒲 x) :
    IsTfTypeTower f g 𝒲 (OpenCover.ofCompChartsTarget 𝒱₀ charts)
      (OpenCover.ofCompCharts charts) := by
  intro x
  refine ⟨Sum.inl x, (charts x).k, (charts x).S, inferInstance, inferInstance, (charts x).K,
    inferInstance, (charts x).fgK, (charts x).B, inferInstance, inferInstance, inferInstance,
    (charts x).M, inferInstance, (charts x).A, inferInstance, inferInstance, inferInstance,
    (charts x).L, inferInstance, (charts x).hg, (charts x).hf, Iso.refl _, Iso.refl _,
    (charts x).targetIso, ?_, ?_⟩
  · simpa [OpenCover.ofCompCharts, OpenCover.ofCompChartsTarget] using (charts x).srcCompat
  · simpa [OpenCover.ofCompChartsTarget] using (charts x).midCompat

/-- The composition law, from a family of composite charts:
`AlgebraicGeometry.FormalScheme.IsTfTypeTower.isTopFiniteTypeHom`
(`FormalSchemes.TopFiniteTypeHomComp`) applied to `isTfTypeTower_ofCompCharts`. -/
theorem isTopFiniteTypeHom_comp_of_compCharts (𝒱₀ : OpenCover Y)
    (charts : ∀ x : X, TfTypeCompChart f g 𝒲 x) : IsTopFiniteTypeHom (f ≫ g) :=
  IsTfTypeTower.isTopFiniteTypeHom (isTfTypeTower_ofCompCharts 𝒱₀ charts)

/-- **EGA I 10.13's composition law.** A composite of two topologically finite-type morphisms of
formal schemes is topologically of finite type, with no hypothesis relating the two witnesses.

This is `FormalSchemes.TopFiniteTypeHomComp`'s shared-chart law with its hypothesis discharged:
the shared middle chart is built at each point by `nonempty_tfTypeCompChart`, and the cover of `Y`
it assembles is that family together with the cover `g`'s own witness supplies, which is what
makes it a cover of all of `Y` and not only of the image of `f`. -/
theorem IsTopFiniteTypeHom.trans (hf : IsTopFiniteTypeHom f) (hg : IsTopFiniteTypeHom g) :
    IsTopFiniteTypeHom (f ≫ g) := by
  obtain ⟨𝒱, 𝒰, h𝒰⟩ := hf
  obtain ⟨𝒲, 𝒱', h𝒱'⟩ := hg
  exact isTopFiniteTypeHom_comp_of_compCharts 𝒱'
    (fun x => (nonempty_tfTypeCompChart h𝒰 h𝒱' x).some)

/-! ### Applications -/

/-- **A finite-type morphism into a chart of a cover is finite-type into the whole scheme.** If
`f : X ⟶ 𝒰.obj i` is topologically of finite type and `𝒰` is an affine cover of `Y` with finitely
generated ideals of definition, then `f ≫ 𝒰.map i : X ⟶ Y` is topologically of finite type.

An application of the composition law that the shared-chart form cannot reach: the two factors are
witnessed against unrelated covers of `𝒰.obj i` — `f`'s own, and the one
`AlgebraicGeometry.FormalScheme.isTopFiniteTypeHom_chartMap`
(`FormalSchemes.TopFiniteTypeHomComp`) produces for the chart inclusion, which is `𝒰` itself.

It is also the first witness on this tree with a **multi-chart target cover and non-identity
finiteness data**: the cover of `Y` that `trans` assembles is indexed by `X ⊕ 𝒰.J`, and the
finiteness data is `f`'s, which is arbitrary. `FormalSchemes.TateTopFiniteTypeHom` records that no
such witness existed and names this composition gap as the reason. -/
theorem IsTopFiniteTypeHom.comp_chartMap {W : FormalScheme.{u}} (𝒰 : OpenCover Y)
    (h𝒰 : ∀ j, ∃ (R : Type u) (_ : CommRing R) (_ : TopologicalSpace R) (I : Ideal R)
      (_ : IsAdicRing I) (_ : I.FG), Nonempty (𝒰.obj j ≅ FormalScheme.Spf I))
    (i : 𝒰.J) {φ : W ⟶ 𝒰.obj i} (hφ : IsTopFiniteTypeHom φ) :
    IsTopFiniteTypeHom (φ ≫ 𝒰.map i) :=
  hφ.trans (isTopFiniteTypeHom_chartMap 𝒰 h𝒰 i)

/-- **The composite of two structural morphisms is topologically of finite type**, read through
the general predicate at both factors.

The minimal non-vacuity witness for the composition law: both factors are tf-type morphisms by
`AlgebraicGeometry.IsTopologicallyFiniteType.isTopFiniteTypeHom`
(`FormalSchemes.TopFiniteTypeHom`), and `trans` composes them. It is an application and not a
restatement — `AlgebraicGeometry.IsTopologicallyFiniteType.structHom_trans`
(`FormalSchemes.RelativeTopFiniteTypeTrans`) identifies the composite with the structural morphism
of the composed algebra, but that identification is not what is used here and the covers the two
sides are witnessed against are different. -/
theorem isTopFiniteTypeHom_structHom_comp {S : Type u} [CommRing S] [TopologicalSpace S]
    {K : Ideal S} [IsAdicRing K] (hK : K.FG)
    {B : Type u} [CommRing B] [TopologicalSpace B] [Algebra S B] {M : Ideal B} [IsAdicRing M]
    (hM : M.FG) (hg : IsTopologicallyFiniteType S K B M)
    {A : Type u} [CommRing A] [TopologicalSpace A] [Algebra B A] {L : Ideal A} [IsAdicRing L]
    (hf : IsTopologicallyFiniteType B M A L) :
    IsTopFiniteTypeHom (IsTopologicallyFiniteType.structHom hf ≫
      IsTopologicallyFiniteType.structHom hg) :=
  (IsTopologicallyFiniteType.isTopFiniteTypeHom hM hf).trans
    (IsTopologicallyFiniteType.isTopFiniteTypeHom hK hg)

end AlgebraicGeometry.FormalScheme
