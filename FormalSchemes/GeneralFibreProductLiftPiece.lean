import FormalSchemes.GeneralFibreProductLiftUnique

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The per-piece uniqueness primitive for the general fibre product `X ×_{Spf R} Y`

The uniqueness half of the fibre-product universal property (issue 234d,
`FormalSchemes.GeneralFibreProductLiftUnique`) reduces, via `OpenCover.hom_ext`, to a *per-chart*
statement: on a single affine chart `w : Spf L ⟶ Z` whose restriction `w ≫ m₁` of `m₁` factors
through a single product chart `Spf(A_{P.1} ⊗̂_R B_{P.2})` (with a continuity witness for that
factorisation), the two restrictions `w ≫ m₁` and `w ≫ m₂` of morphisms agreeing after both
projections coincide.

This file isolates that per-chart core as `hom_eq_of_chart_factor`, parametrised by the chart data
(`w`, the index `P`, the factorisation `fac` with `fac ≫ ι P = w ≫ m₁`, and its continuity) rather
than by the internally-chosen `refinedCover` that `fibreLift_unique` uses. Both `fibreLift_unique`
(feeding the internal refined cover) and the general-`fibreLift` overlap obligation (issue 234c,
which supplies an *explicit* basic-open cover of the overlap whose adicity is provable) reduce to
this one lemma. The proof body is the STEP 3–5 core of `fibreLift_unique`, verbatim up to the
substitution of the caller-supplied chart data for the refined-cover data.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
open CompletedTensorProduct

universe u

namespace AlgebraicGeometry

namespace BothChartedFibreDatumXY

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable [TopologicalSpace R] [IsAdicRing I]
variable (D : BothChartedFibreDatumXY R I hI)

/-- **Per-chart uniqueness primitive.** Let `m₁ m₂ : Z ⟶ X ×_{Spf R} Y` agree after both
projections. On a single finitely generated affine chart `w : Spf L ⟶ Z`, suppose the restriction
`w ≫ m₁` of `m₁` factors through the product chart `Spf(A_{P.1} ⊗̂_R B_{P.2})` via
`fac` (i.e. `fac ≫ ι P = w ≫ m₁`), with the global-sections map of `fac` continuous (`hcont`).
Then `w ≫ m₁ = w ≫ m₂`.

This is the STEP 3–5 core of `fibreLift_unique`, abstracted over the chart data so that a caller can
supply an explicit cover (with provable continuity) rather than the internally-chosen refined
cover. -/
theorem hom_eq_of_chart_factor
    (hV : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'), D.V p p' h = bothAlgDataV hI D.gX D.gY p p' h)
    (hf : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.f p p' h = eqToHom (hV p p' h) ≫ bothAlgDataF hI D.gX D.gY p p' h)
    (ht : letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      ∀ p p' (h : p ≠ p'),
        D.t p p' h = eqToHom (hV p p' h) ≫ bothAlgDataT hI D.gX D.gY D.τX D.τY p p' h ≫
          eqToHom (hV p' p h.symm).symm)
    {Z : FormalScheme.{u}}
    (m₁ m₂ : Z.toLocallyRingedSpace ⟶ D.generalFibreProduct.toLocallyRingedSpace)
    (hpr₁ : m₁ ≫ D.pr₁ hV hf ht = m₂ ≫ D.pr₁ hV hf ht)
    (hpr₂ : m₁ ≫ D.pr₂ hV hf ht = m₂ ≫ D.pr₂ hV hf ht)
    {L : Type u} [CommRing L] [TopologicalSpace L] {LJ : Ideal L} [IsAdicRing LJ] (hLfg : LJ.FG)
    (w : FormalSpectrum.locallyRingedSpaceObj LJ ⟶ Z.toLocallyRingedSpace)
    (P : D.formalGlueData.toLocallyRingedSpaceGlueData.J)
    (fac : FormalSpectrum.locallyRingedSpaceObj LJ ⟶
      D.formalGlueData.toLocallyRingedSpaceGlueData.U P)
    (hfac : fac ≫ D.formalGlueData.ι P = w ≫ m₁)
    (hcont :
      letI := D.commRingA; letI := D.algebraA; letI := D.commRingB; letI := D.algebraB
      letI := CompletedTensorProduct.isAdicRing R I (D.A P.1) (D.B P.2) hI
      CompletedTensorProduct.idealOfDefinition R I (D.A P.1) (D.B P.2) ≤
        LJ.comap
          (FormalSpectrum.globalSectionsMap
            (CompletedTensorProduct.idealOfDefinition R I (D.A P.1) (D.B P.2)) LJ fac)) :
    w ≫ m₁ = w ≫ m₂ := by
  letI := D.commRingA
  letI := D.algebraA
  letI := D.commRingB
  letI := D.algebraB
  letI := D.topologyA
  letI := D.isAdicA
  letI := D.topologyB
  letI := D.isAdicB
  haveI : IsAdicRing (idealOfDefinition R I (D.A P.1) (D.B P.2)) :=
    CompletedTensorProduct.isAdicRing R I (D.A P.1) (D.B P.2) hI
  -- STEP 3: `m₂`'s image on the chart lands in the same product chart `P`.
  have hsub : Set.range (w ≫ m₂).base ⊆ Set.range (D.formalGlueData.ι P).base := by
    have hlem := D.range_ι_eq_pr_preimage_inter hV hf ht P
    rintro x ⟨s, rfl⟩
    refine hlem.ge ⟨?_, ?_⟩
    · rw [Set.mem_preimage]
      have e : (w ≫ m₂) ≫ D.pr₁ hV hf ht =
          fac ≫ D.formalGlueData.ι P ≫ D.pr₁ hV hf ht := by
        have h1 : fac ≫ D.formalGlueData.ι P ≫ D.pr₁ hV hf ht =
            (w ≫ m₁) ≫ D.pr₁ hV hf ht :=
          (reassoc_of% hfac) (D.pr₁ hV hf ht)
        rw [h1, Category.assoc, Category.assoc, hpr₁]
      have hpt := congrArg (fun m => m.base s) e
      have hip := congrArg (fun m => m.base (fac.base s)) (D.ι_pr₁ hV hf ht P)
      simp only [LocallyRingedSpace.comp_base, TopCat.comp_app] at hpt hip ⊢
      rw [hpt, hip]
      exact ⟨_, rfl⟩
    · rw [Set.mem_preimage]
      have e : (w ≫ m₂) ≫ D.pr₂ hV hf ht =
          fac ≫ D.formalGlueData.ι P ≫ D.pr₂ hV hf ht := by
        have h1 : fac ≫ D.formalGlueData.ι P ≫ D.pr₂ hV hf ht =
            (w ≫ m₁) ≫ D.pr₂ hV hf ht :=
          (reassoc_of% hfac) (D.pr₂ hV hf ht)
        rw [h1, Category.assoc, Category.assoc, hpr₂]
      have hpt := congrArg (fun m => m.base s) e
      have hip := congrArg (fun m => m.base (fac.base s)) (D.ι_pr₂ hV hf ht P)
      simp only [LocallyRingedSpace.comp_base, TopCat.comp_app] at hpt hip ⊢
      rw [hpt, hip]
      exact ⟨_, rfl⟩
  -- STEP 4: the second lift `fSnd`.
  set fSnd := LocallyRingedSpace.IsOpenImmersion.lift (D.formalGlueData.ι P)
    (w ≫ m₂) hsub with hfSnd
  have hfSnd_fac : fSnd ≫ D.formalGlueData.ι P = w ≫ m₂ := by
    rw [hfSnd]
    exact LocallyRingedSpace.IsOpenImmersion.lift_fac (D.formalGlueData.ι P) (w ≫ m₂) hsub
  -- Projection agreements: cancel the mono chart inclusions `ι^X`, `ι^Y`.
  have hproj₁ : fac ≫ D.pr₁ChartSelf P = fSnd ≫ D.pr₁ChartSelf P := by
    have h1 : fac ≫ D.formalGlueData.ι P ≫ D.pr₁ hV hf ht =
        (w ≫ m₁) ≫ D.pr₁ hV hf ht :=
      (reassoc_of% hfac) (D.pr₁ hV hf ht)
    have h2 : fSnd ≫ D.formalGlueData.ι P ≫ D.pr₁ hV hf ht =
        (w ≫ m₂) ≫ D.pr₁ hV hf ht :=
      (reassoc_of% hfSnd_fac) (D.pr₁ hV hf ht)
    have e1 : (fac ≫ D.pr₁ChartSelf P) ≫ D.xFormalGlueData.ι P.1 =
        (w ≫ m₁) ≫ D.pr₁ hV hf ht :=
      ((Category.assoc _ _ _).trans
        (congrArg (fun t => fac ≫ t) (D.ι_pr₁ hV hf ht P).symm)).trans h1
    have e2 : (fSnd ≫ D.pr₁ChartSelf P) ≫ D.xFormalGlueData.ι P.1 =
        (w ≫ m₂) ≫ D.pr₁ hV hf ht :=
      ((Category.assoc _ _ _).trans
        (congrArg (fun t => fSnd ≫ t) (D.ι_pr₁ hV hf ht P).symm)).trans h2
    have emid : (w ≫ m₁) ≫ D.pr₁ hV hf ht = (w ≫ m₂) ≫ D.pr₁ hV hf ht := by
      rw [Category.assoc, Category.assoc, hpr₁]
    exact (cancel_mono (D.xFormalGlueData.ι P.1)).mp (e1.trans (emid.trans e2.symm))
  have hproj₂ : fac ≫ D.pr₂ChartSelf P = fSnd ≫ D.pr₂ChartSelf P := by
    have h1 : fac ≫ D.formalGlueData.ι P ≫ D.pr₂ hV hf ht =
        (w ≫ m₁) ≫ D.pr₂ hV hf ht :=
      (reassoc_of% hfac) (D.pr₂ hV hf ht)
    have h2 : fSnd ≫ D.formalGlueData.ι P ≫ D.pr₂ hV hf ht =
        (w ≫ m₂) ≫ D.pr₂ hV hf ht :=
      (reassoc_of% hfSnd_fac) (D.pr₂ hV hf ht)
    have e1 : (fac ≫ D.pr₂ChartSelf P) ≫ D.yFormalGlueData.ι P.2 =
        (w ≫ m₁) ≫ D.pr₂ hV hf ht :=
      ((Category.assoc _ _ _).trans
        (congrArg (fun t => fac ≫ t) (D.ι_pr₂ hV hf ht P).symm)).trans h1
    have e2 : (fSnd ≫ D.pr₂ChartSelf P) ≫ D.yFormalGlueData.ι P.2 =
        (w ≫ m₂) ≫ D.pr₂ hV hf ht :=
      ((Category.assoc _ _ _).trans
        (congrArg (fun t => fSnd ≫ t) (D.ι_pr₂ hV hf ht P).symm)).trans h2
    have emid : (w ≫ m₁) ≫ D.pr₂ hV hf ht = (w ≫ m₂) ≫ D.pr₂ hV hf ht := by
      rw [Category.assoc, Category.assoc, hpr₂]
    exact (cancel_mono (D.yFormalGlueData.ι P.2)).mp (e1.trans (emid.trans e2.symm))
  -- Continuity of `fSnd` is derived from that of `fac` (`hcont`).
  have hJ : idealOfDefinition R I (D.A P.1) (D.B P.2) =
      (I.map (algebraMap R (D.A P.1))).map (inl R I (D.A P.1) (D.B P.2)).toRingHom := by
    rw [idealOfDefinition_eq_map, Ideal.map_map]
    congr 1
  have hgpr : globalSectionsMap (I.map (algebraMap R (D.A P.1)))
      (idealOfDefinition R I (D.A P.1) (D.B P.2)) (D.pr₁ChartSelf P) =
      (inl R I (D.A P.1) (D.B P.2)).toRingHom :=
    globalSectionsMap_locallyRingedSpaceMap _ _ _ _
  have hcomp : (globalSectionsMap (idealOfDefinition R I (D.A P.1) (D.B P.2)) LJ fac).comp
        (inl R I (D.A P.1) (D.B P.2)).toRingHom =
      (globalSectionsMap (idealOfDefinition R I (D.A P.1) (D.B P.2)) LJ fSnd).comp
        (inl R I (D.A P.1) (D.B P.2)).toRingHom := by
    rw [← hgpr, ← globalSectionsMap_comp, ← globalSectionsMap_comp]
    exact congrArg (globalSectionsMap (I.map (algebraMap R (D.A P.1))) LJ) hproj₁
  have hc2 : idealOfDefinition R I (D.A P.1) (D.B P.2) ≤
      LJ.comap (globalSectionsMap (idealOfDefinition R I (D.A P.1) (D.B P.2)) LJ fSnd) := by
    have hc1 := hcont
    nth_rewrite 1 [hJ] at hc1 ⊢
    rw [Ideal.map_le_iff_le_comap] at hc1 ⊢
    rw [Ideal.comap_comap, ← hcomp, ← Ideal.comap_comap]
    exact hc1
  -- STEP 5: the two lifts coincide by affine uniqueness (issue 234c/EGA I 10.7).
  have hEq : fac = fSnd :=
    fibreLift_unique_lrs hI hLfg fac fSnd hcont hc2 hproj₁ hproj₂
  -- Conclude `w ≫ m₁ = w ≫ m₂`.
  rw [← hfac, hEq, hfSnd_fac]

end BothChartedFibreDatumXY

end AlgebraicGeometry
