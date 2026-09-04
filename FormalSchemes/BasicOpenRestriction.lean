import FormalSchemes.SpfGammaSheafComponentArbComp

set_option linter.style.header false

/-!
# The restriction of `O_{Spf R}` between two basic opens, as a map of completed localizations

`FormalSpectrum.sectionsBasicOpenEquiv` reads the sections of `O_{Spf R}` over a basic open `D(f)`
as the completed localization `R{1/f} = AdicCompletion (I · R_f) R_f`. Conjugating the
structure-sheaf restriction `Γ(D(f)) ⟶ Γ(D(g))` by it on both sides, for `D(g) ≤ D(f)`, therefore
produces a ring homomorphism

```
R{1/f} →+* R{1/g}
```

which this file names `FormalSpectrum.basicOpenRes`. Naming it is the point: several files describe
the object in prose while saying that no declaration on the tree presents the restriction as a map
of adic completions, and consumers of the basis of basic opens — the colimit description of the
stalk, the sheaf gluing over the distinguished basis — need a name before they can state anything
about it.

What is proved here is the part that does not need a level-by-level computation: `basicOpenRes` is
functorial in the inclusion, and it is **pinned on the image of `R`**, i.e. precomposed with the
completed-localization structure map `FormalSpectrum.awayCompletionHom I f` it is
`FormalSpectrum.awayCompletionHom I g`. That last statement is this neighbourhood's usual
locality-free square, and it is the exact analogue for restrictions of
`FormalSpectrum.arbSheafComponent_comp_awayCompletionHom`
(`FormalSchemes.SpfGammaSheafComponentArbComp`), which pins the sheaf component of an arbitrary
morphism of formal spectra the same way and no further.

## Main results

* `FormalSpectrum.basicOpenRes`: the restriction `Γ(D(f)) ⟶ Γ(D(g))` for `D(g) ≤ D(f)`, conjugated
  by `FormalSpectrum.sectionsBasicOpenEquiv` on both sides, as a ring hom `R{1/f} →+* R{1/g}`.
* `FormalSpectrum.basicOpenRes_self`, `FormalSpectrum.basicOpenRes_comp`: it is the identity on a
  refl inclusion and composes along a chain `D(h) ≤ D(g) ≤ D(f)`.
* `FormalSpectrum.basicOpenRes_comp_awayCompletionHom`: **the locality-free square** —
  `basicOpenRes` precomposed with `awayCompletionHom I f` is `awayCompletionHom I g`.
* `FormalSpectrum.basicOpenResMul`, `FormalSpectrum.basicOpenResMul_comp_awayCompletionHom`: the
  same at the nested inclusion `D(f * g) ≤ D(f)`, which needs no hypothesis and is the form the
  basis arguments below `D(f)` use.
* `FormalSpectrum.arbSheafComponent_comp_basicOpenRes_comp_awayCompletionHom`: for an arbitrary
  morphism of formal spectra, its component on the smaller basic open, composed with the
  restriction, is pinned on the image of `R` in the same way.

## What is *not* proved here

**That `basicOpenRes` is any particular map of completed localizations.** The square above
determines it on the image of `R{1/f}`'s defining ring `R`, and nothing here determines it beyond
that. For the special case `f = 1` there is nothing left to determine, and that case is landed:
`FormalSpectrum.awayCompletionHom_eq_restrict` (`FormalSchemes.SpfGammaSheafComponentArbComp`) says
the restriction `Γ(⊤) ⟶ Γ(D(g))`, read through `FormalSpectrum.globalSectionsEquiv` and
`sectionsBasicOpenEquiv`, is exactly `awayCompletionHom I g`. For a general `f` the residue is a
level-by-level computation of the kind `FormalSchemes.BasicOpenImmersionSheaf` and
`FormalSchemes.BasicOpenImmersionAssembly` carry out for the chart's sheaf component, and this file
deliberately does not attempt it.

The shape a full identification would take, for the record: `FormalSpectrum.chartComponent`
(`FormalSchemes.BasicOpenImmersionSheaf`) is the affine chart's sheaf component on `D(g)`,
conjugated by `sectionsBasicOpenEquiv` on both sides, and is bijective when `I` is `Ideal.FG` and
`f` is a unit in `Localization.Away g` (`IsUnit`), by
`FormalSpectrum.bijective_chartComponent` (`FormalSchemes.BasicOpenImmersionAssembly`). Naturality
of the chart's component along `D(g) ≤ D(f)` expresses `chartComponent I f g` composed with
`basicOpenRes` through the chart's component at `D(f)` itself, whose source open has the whole of
`Spf R{1/f}` as preimage; identifying *that* component with the global-sections identification is
the step that is missing, and it is not supplied here.

**Anything about stalks.** No germ, colimit or stalk comparison appears below. In particular nothing
here says anything about `FormalSpectrum.IsStalkLimit`.

## Implementation notes

`basicOpenRes` takes the inclusion `basicOpen I g ≤ basicOpen I f` as a hypothesis rather than a
condition on `f` and `g`, because that is what the presheaf's restriction map consumes and because
the two conditions on elements the rest of the library uses — `IsUnit ((algebraMap R
(Localization.Away g)) f)`, as in `FormalSpectrum.awayCompletionAwayEquiv`, and the nested form
`g = f * g'` — both produce it. The nested form produces it with no hypothesis at all, through
`FormalSpectrum.basicOpen_mul`, which is why `basicOpenResMul` is stated separately.

The proofs of `basicOpenRes_self` and `basicOpenRes_comp` are the observation that morphisms of
`TopologicalSpace.Opens` are unique: the restriction along a refl inclusion is the identity and the
composite of two restrictions is the restriction along the composite, because the two morphisms
involved are equal in a thin category. Neither needs `IsAdicRing` or a topology on `R`; the
locality-free square does, since `awayCompletionHom_eq_restrict` is stated for an adic ring.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1 and §10.3.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FormalSpectrum

variable {R S : Type u} [CommRing R] [CommRing S]
variable (I : Ideal R) (J : Ideal S)
variable [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing J]

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The structure-sheaf restriction between two basic opens, as a map of completed
localizations.** For `D(g) ≤ D(f)`, the restriction `Γ(D(f), O_{Spf R}) ⟶ Γ(D(g), O_{Spf R})` read
through `FormalSpectrum.sectionsBasicOpenEquiv` on both sides, i.e. a ring hom
`R{1/f} →+* R{1/g}`. -/
def basicOpenRes {f g : R} (hle : basicOpen I g ≤ basicOpen I f) :
    awayCompletion I f →+* awayCompletion I g :=
  (sectionsBasicOpenEquiv I g).toRingHom.comp
    (((structureSheaf I).presheaf.map (homOfLE hle).op).hom.comp
      (sectionsBasicOpenEquiv I f).symm.toRingHom)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- Restriction along the refl inclusion `D(f) ≤ D(f)` is the identity of `R{1/f}`: the restriction
morphism is the identity because morphisms of `TopologicalSpace.Opens` are unique. -/
theorem basicOpenRes_self (f : R) :
    basicOpenRes I (le_refl (basicOpen I f)) = RingHom.id (awayCompletion I f) := by
  refine RingHom.ext fun x => ?_
  simp only [basicOpenRes, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingHom.id_apply]
  rw [show (homOfLE (le_refl (basicOpen I f))).op = 𝟙 _ from Subsingleton.elim _ _]
  simp

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Functoriality along a chain of basic opens.** For `D(h) ≤ D(g) ≤ D(f)`, restricting to `D(g)`
and then to `D(h)` is restricting to `D(h)`; the conjugating isomorphisms in the middle cancel and
the two restriction morphisms agree because morphisms of `TopologicalSpace.Opens` are unique. -/
theorem basicOpenRes_comp {f g h : R} (hgf : basicOpen I g ≤ basicOpen I f)
    (hhg : basicOpen I h ≤ basicOpen I g) :
    (basicOpenRes I hhg).comp (basicOpenRes I hgf) = basicOpenRes I (hhg.trans hgf) := by
  refine RingHom.ext fun x => ?_
  simp only [basicOpenRes, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  congr 2

/-- **The locality-free square: `basicOpenRes` is pinned on the image of `R`.** Precomposed with
the completed-localization structure map `awayCompletionHom I f : R →+* R{1/f}`, the restriction to
`D(g)` is `awayCompletionHom I g : R →+* R{1/g}`.

Both sides are the restriction `Γ(⊤) ⟶ Γ(D(g))` read through `FormalSpectrum.globalSectionsEquiv`
and `sectionsBasicOpenEquiv`, by `FormalSpectrum.awayCompletionHom_eq_restrict` at `f` and at `g`,
so the content is that the restriction `⊤ ⟶ D(f) ⟶ D(g)` factors as it must.

This determines `basicOpenRes` on the image of `R` and **not beyond it**; the analogous statement
for the sheaf component of an arbitrary morphism of formal spectra is
`FormalSpectrum.arbSheafComponent_comp_awayCompletionHom`, and there too the full identification is
a separate and harder question. -/
theorem basicOpenRes_comp_awayCompletionHom {f g : R} (hle : basicOpen I g ≤ basicOpen I f) :
    (basicOpenRes I hle).comp (awayCompletionHom I f) = awayCompletionHom I g := by
  refine RingHom.ext fun r => ?_
  rw [RingHom.comp_apply, RingHom.congr_fun (awayCompletionHom_eq_restrict I f) r,
    RingHom.congr_fun (awayCompletionHom_eq_restrict I g) r]
  simp only [basicOpenRes, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.symm_apply_apply]
  congr 1
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  congr 1

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The restriction to a nested basic open**, `R{1/f} →+* R{1/f * g}`. The inclusion
`D(f * g) ≤ D(f)` holds for every `f` and `g` by `FormalSpectrum.basicOpen_mul`, so this form
carries no hypothesis; the opens `D(f * g)` are the basis of `D(f)` that the basis arguments of
this library use. -/
def basicOpenResMul (f g : R) : awayCompletion I f →+* awayCompletion I (f * g) :=
  basicOpenRes I (by rw [basicOpen_mul]; exact inf_le_left)

/-- The locality-free square at the nested inclusion `D(f * g) ≤ D(f)`. -/
theorem basicOpenResMul_comp_awayCompletionHom (f g : R) :
    (basicOpenResMul I f g).comp (awayCompletionHom I f) = awayCompletionHom I (f * g) :=
  basicOpenRes_comp_awayCompletionHom I _

/-- **The sheaf component of an arbitrary morphism, after a restriction, is pinned on the image of
`R`.** For `F : Spf S ⟶ Spf R` and `D(g) ≤ D(f)`, the conjugated component
`FormalSpectrum.arbSheafComponent I J F g` composed with `basicOpenRes` and then with
`awayCompletionHom I f` is the global-sections map `φ = globalSectionsMap I J F` followed by the
target structure map `awayCompletionHom J (φ g)`.

This is `FormalSpectrum.basicOpenRes_comp_awayCompletionHom` followed by
`FormalSpectrum.arbSheafComponent_comp_awayCompletionHom`, and it is the strongest statement about
the composite that does not need either factor to be identified. -/
theorem arbSheafComponent_comp_basicOpenRes_comp_awayCompletionHom
    (F : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I) {f g : R}
    (hle : basicOpen I g ≤ basicOpen I f) :
    ((arbSheafComponent I J F g).comp (basicOpenRes I hle)).comp (awayCompletionHom I f) =
      (awayCompletionHom J (globalSectionsMap I J F g)).comp (globalSectionsMap I J F) := by
  rw [RingHom.comp_assoc, basicOpenRes_comp_awayCompletionHom,
    arbSheafComponent_comp_awayCompletionHom]

end FormalSpectrum
