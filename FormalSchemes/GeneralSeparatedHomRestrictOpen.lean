import FormalSchemes.SpfOpenSeparated
import FormalSchemes.GeneralSeparatedHomIdentity

set_option linter.style.header false

/-!
# An open formal subscheme is separated over its ambient scheme (EGA I §10.15)

`FormalScheme.IsSeparatedHom` (`FormalSchemes.GeneralSeparatedHom`) is separatedness of a morphism
at an arbitrary target. Every value of it on the tree so far is either conservativity applied at an
affine target and transported (`FormalSchemes.GeneralSeparatedHomValues`) or an identity
(`FormalScheme.isSeparatedHom_id`, `FormalSchemes.GeneralSeparatedHomIdentity`). This file supplies

```
FormalScheme.isSeparatedHom_restrictOpenHom (hX : X.LocallyFG) (U : Opens X) :
  FormalScheme.IsSeparatedHom (X.restrictOpen_locallyFG hX U) hX (X.restrictOpenHom hX U)
```

at an **arbitrary** `X` and an **arbitrary** open `U`: the inclusion of an open formal subscheme is
a separated morphism. Neither end is required to be a `FormalScheme.Spf`, and the morphism is not
an identity — its range is `U` (`FormalScheme.range_restrictOpenι_base`), so it is an isomorphism
only when `U = ⊤`.

A second section, added by issue 2148, runs the transport this file is built on the **other** way:
`FormalScheme.isSeparatedOverSpf_of_isOpenImmersion` below trivialises the base change at `A := R`
because its consumer puts the chart's own ring on both sides, and restoring it gives statement (A)
of issue 1987 — separatedness surviving a restriction of the *source* — whenever the open lies
inside one affine chart over `Spf R`. That section's own header docstring says what it settles and
why the general case cannot be assembled out of it.

A **third** section, added by the same issue, settles (A) at the opposite class of opens: a union
of whole chart ranges of a presentation. Dropping charts from a chart family is not a construction
— every field of `AlgebraicGeometry.AffineChartedFibreDatumX` is a `∀` over its index type — and
separatedness survives it because the criterion of
`FormalSchemes.GeneralSeparatedChartCodiagonal` is a condition on one *pair* of charts at a time.
That section's header docstring states the equivalence this turns on, and records that what is
left of issue 2148's goal 2 no longer mentions the open at all.

## The route

The cover of the target is the one `FormalScheme.isSeparatedHom_id` uses, and for the same reason:
`FormalScheme.LocallyFG` gives every point an affine chart which is an open immersion with finitely
generated ideal, so the ranges of the charts cover `X` and each `X|_{V x}` is identified with
`Spf I x` by `FormalScheme.restrictOpenIso` at a range hypothesis that is `rfl`.

What the per-chart clause then asks is that `(X|_U)|_{g⁻¹ V x}` be separated over `Spf I x` along
`FormalScheme.restrictOpenMap` followed by that identification. **That composite is an open
immersion**, which is the whole content of the reduction: the inclusion of an open subscheme
restricts to an open immersion on preimages, and the chart identification is an isomorphism. So the
per-chart clause is an instance of

```
FormalScheme.isSeparatedOverSpf_of_isOpenImmersion (hI : I.FG) {Z : FormalScheme}
  (χ : Z.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I)
  [LocallyRingedSpace.IsOpenImmersion χ] : FormalScheme.IsSeparatedOverSpf hI Z χ
```

— *any* formal scheme presented as an open subscheme of `Spf I`, by an arbitrary open immersion, is
separated over `Spf I`.

That general form is `FormalScheme.isSeparatedOverSpf_restrictOpen_Spf`
(`FormalSchemes.SpfOpenSeparated`, issue 1990) with two changes, and both are needed here:

* **The base change is trivialised.** Issue 1990 states its conclusion over `Spf R` for an open of
  `Spf A` at an `R`-algebra `A`; the per-chart clause of `FormalScheme.IsSeparatedHom` puts the
  chart's own ring on both sides, so this is the case `A := R`. As in
  `AlgebraicGeometry.spf_isSeparatedOverSpf_self`, the specialisation is not definitional —
  `Ideal.map (algebraMap R R) I` and `I` are equal by `Ideal.map_id` and not by `rfl` — and the
  transport is `FormalSpectrum.locallyRingedSpaceObjCongr`, whose compatibility with the structural
  morphism is `FormalSpectrum.locallyRingedSpaceObjCongr_hom_eq_map`.
* **The presentation is arbitrary.** Issue 1990's source is literally a `FormalScheme.restrictOpen`
  of a `FormalScheme.Spf`; here it is whatever `Z` the caller has. The bridge is
  `FormalScheme.restrictOpenIso` at the open `⟨Set.range χ.base, _⟩`, which is where the
  open-immersion hypothesis is spent and the only place it is used.

Taking `χ` to be an identity recovers `AlgebraicGeometry.spf_isSeparatedOverSpf_self`; nothing here
supersedes it, since that lemma is a hypothesis of the transport rather than a consequence.

## What this closes, and what it does not

* It closes the third entry of `FormalSchemes.GeneralSeparatedHom`'s "What is *not* proved here"
  list, which asked for a value at a target that is not a `FormalScheme.Spf` and a morphism that is
  not an identity. **That entry is removed by this issue**; the list now has three.
* *Arbitrary* is again the honest word rather than *non-affine*, exactly as
  `FormalSchemes.GeneralSeparatedHomIdentity` records for the identity: the target here is an
  arbitrary `FormalScheme.LocallyFG` formal scheme, and nothing on this tree exhibits a formal
  scheme it knows not to be affine. What is new is the **morphism**, which is an open immersion and
  not an identity, and not any knowledge about the target.
* It closes **none** of the three remaining open directions of §10.15 — the composition law,
  conservativity's hard direction, and the refinement direction of `FormalScheme.IsSeparatedHom`.
  All three want a witness at a *given* presentation of the target, and this file's per-chart
  witness is built from the chart rather than restricted from one that was handed to it; see the
  paragraph `FormalSchemes.GeneralSeparatedHom` now carries on what the three have in common.
* Nothing here is a statement about `FormalScheme.restrictOpenSchemeMap` at a general morphism. The
  source of the reduction is that the morphism being restricted is itself an open immersion, and
  that is what `FormalScheme.isOpenImmersion_restrictOpenMap` below asks for.

## Placement of the value, of the helper, and a second consumer for two others

`FormalSchemes.GeneralSeparatedScheme` records the rule that a value belongs in the module that
owns its object, and `FormalSchemes.GeneralSeparatedHomValues` records why the
`FormalScheme.IsSeparatedHom` values do not follow it. The same reason applies here and more
strongly: the owner of `FormalScheme.restrictOpenHom` is `FormalSchemes.OpenFormalSubscheme`, which
does not import `FormalSchemes.GeneralSeparatedHom` at all and could not state this theorem without
pulling the whole fibre-product layer into the middle of the tree. A leaf module costs one module
and moves nothing.


`FormalScheme.isOpenImmersion_restrictOpenMap` is general and belongs beside
`FormalScheme.restrictOpenMap` in `FormalSchemes.OpenFormalSubscheme`. That module's reverse
closure is **76** against this file's **0**, and the instance has one consumer, here; it is
declined on the same ratio and for the same reason as the three helpers
`FormalSchemes.GeneralSeparatedHomIdentity` declines, and is worth re-costing when a second
consumer appears.

Two of those three helpers now **have** that second consumer, which is the event that file's note
asks to be recorded: `FormalSpectrum.locallyRingedSpaceObjCongr` and
`FormalSpectrum.locallyRingedSpaceObjCongr_hom_eq_map` are used here as well as by
`AlgebraicGeometry.spf_isSeparatedOverSpf_self`. The ratio that declined their move has not changed
— `FormalSchemes.FormalSpectrum`'s reverse closure is **534** — so this records the second consumer
and moves nothing.

## Main definitions and results

* `AlgebraicGeometry.FormalScheme.isOpenImmersion_restrictOpenMap`: restricting an open immersion
  to the preimage of an open leaves an open immersion.
* `AlgebraicGeometry.FormalScheme.isSeparatedOverSpf_of_isOpenImmersion`: **a formal scheme that
  open-immerses into `Spf I` is separated over `Spf I`**, at an arbitrary presentation.
* `AlgebraicGeometry.FormalScheme.isSeparatedHom_restrictOpenHom`: **the inclusion of an open
  formal subscheme is separated**, at an arbitrary target and an arbitrary open.
* `AlgebraicGeometry.FormalScheme.isSeparatedOverSpf_of_isOpenImmersion_chart`: a formal scheme
  that open-immerses into `Spf (I·A)` is separated over `Spf R`.
* `AlgebraicGeometry.FormalScheme.isSeparatedOverSpf_restrictOpen_of_subset_range`: **statement (A)
  at an open contained in one affine chart** — `X` restricted to `W` is separated over `Spf R` as
  soon as `W` lies inside the range of an affine chart of `X` over the base.
* `AlgebraicGeometry.FormalScheme.isSeparatedOverSpf_restrictOpen_of_subset_range_ι`: the same at a
  chart of a presentation of `X`, which is the form issue 1987 states (A) in.
* `AlgebraicGeometry.FormalScheme.isSeparatedHom_restrictOpen_of_subset_range`: the same in the
  `AlgebraicGeometry.FormalScheme.IsSeparatedHom` vocabulary.
* `AlgebraicGeometry.AffineChartedFibreDatumX.reindex`: a subfamily of a chart family, as a datum.
* `AlgebraicGeometry.AffineChartedFibreDatumX.reindexHom`,
  `AlgebraicGeometry.AffineChartedFibreDatumX.isOpenImmersion_reindexHom` and
  `AlgebraicGeometry.AffineChartedFibreDatumX.range_reindexHom`: a subfamily's glued object is the
  open formal subscheme cut out by the union of the selected chart ranges.
* `AlgebraicGeometry.BothChartedFibreDatumXY.isSeparated_reindex`: **separatedness passes to every
  subfamily of a chart family.**
* `AlgebraicGeometry.BothChartedFibreDatumXY.isSeparatedOverSpf_restrictOpen_of_iUnion_range_ι`:
  **statement (A) at an open that is a union of chart ranges of a presentation.**

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.15.
-/

noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry FormalSpectrum

universe u

namespace AlgebraicGeometry.FormalScheme

variable {X Y : FormalScheme.{u}} (hX : X.LocallyFG) (hY : Y.LocallyFG)

/-- **Restricting an open immersion to the preimage of an open leaves an open immersion.**

`FormalScheme.restrictOpenMap` is `LocallyRingedSpace.IsOpenImmersion.lift` of
`FormalScheme.restrictOpenι hX (f⁻¹V) ≫ f` along `FormalScheme.restrictOpenι hY V`, and
`LocallyRingedSpace.IsOpenImmersion.lift` is `inv (pullback.snd _ _) ≫ pullback.fst _ _` in
Mathlib. When the morphism being lifted is itself an open immersion,
`LocallyRingedSpace.IsOpenImmersion.pullback_fst_of_right` makes the second factor one; the first
is an isomorphism. So the proof is the two `delta`s that expose that composite and instance
search. -/
instance isOpenImmersion_restrictOpenMap (f : X.toLocallyRingedSpace ⟶ Y.toLocallyRingedSpace)
    [LocallyRingedSpace.IsOpenImmersion f] (V : Opens Y) :
    LocallyRingedSpace.IsOpenImmersion (X.restrictOpenMap hX Y hY f V) := by
  delta FormalScheme.restrictOpenMap LocallyRingedSpace.IsOpenImmersion.lift
  infer_instance

variable {R : Type u} [CommRing R] [TopologicalSpace R] {I : Ideal R} [IsAdicRing I]

/-- **The transport that turns an open of `Spf J` separated over `Spf I` along `m` into an
arbitrary open immersion into `Spf I` separated over `Spf I`.**

Stated with `J`, the comparison `c` and the structural morphism `m` as parameters rather than at
the values the caller supplies, because the caller's `J` is `Ideal.map (algebraMap R R) I`, which
is equal to `I` and not definitionally so: an argument carried out at the value would have to
rewrite an ideal underneath `FormalSpectrum.locallyRingedSpaceObj`, which is the rewrite
`FormalSpectrum.locallyRingedSpaceObjCongr` exists because `rw` cannot do.

The open immersion is spent exactly once, on `FormalScheme.restrictOpenIso` at the open cut out by
the range of `χ ≫ c.inv`; everything after that is the triangle
`FormalScheme.restrictOpenIso_hom_comp` and `c.inv ≫ c.hom = 𝟙`. -/
private theorem isSeparatedOverSpf_of_isOpenImmersion_aux {J : Ideal R} [IsAdicRing J]
    (hI : I.FG) (hJ : J.FG) {Z : FormalScheme.{u}}
    (c : locallyRingedSpaceObj J ≅ locallyRingedSpaceObj I)
    (m : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I) (hm : m = c.hom)
    (χ : Z.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I)
    [LocallyRingedSpace.IsOpenImmersion χ]
    (H : ∀ T : Opens (FormalScheme.Spf J),
      IsSeparatedOverSpf hI ((FormalScheme.Spf J).restrictOpen (locallyFG_Spf hJ) T)
        ((FormalScheme.Spf J).restrictOpenι (locallyFG_Spf hJ) T ≫ m)) :
    IsSeparatedOverSpf hI Z χ := by
  haveI himm : LocallyRingedSpace.IsOpenImmersion (χ ≫ c.inv) := inferInstance
  obtain ⟨T, hT⟩ : ∃ T : Opens (FormalScheme.Spf J),
      Set.range (χ ≫ c.inv).base = (T : Set (FormalScheme.Spf J)) :=
    ⟨⟨Set.range (χ ≫ c.inv).base, himm.base_open.isOpen_range⟩, rfl⟩
  have hfac := (FormalScheme.Spf J).restrictOpenIso_hom_comp (locallyFG_Spf hJ) T (χ ≫ c.inv) hT
  refine isSeparatedOverSpf_of_iso hI
    ((FormalScheme.Spf J).restrictOpenIso (locallyFG_Spf hJ) T (χ ≫ c.inv) hT).symm ?_ (H T)
  rw [hm, Iso.symm_hom, Iso.inv_comp_eq, ← Category.assoc, hfac]
  simp

/-- **A formal scheme that open-immerses into `Spf I` is separated over `Spf I`** (EGA I §10.15),
at an arbitrary presentation of the open subscheme.

`FormalScheme.isSeparatedOverSpf_restrictOpen_Spf` (`FormalSchemes.SpfOpenSeparated`) is this
statement for the presentation `FormalScheme.restrictOpen` supplies and over a base `Spf R` under
`Spf A`; this is the case `A := R`, at a source the caller names. Both changes are spent by the
transport above — the first on `FormalSpectrum.locallyRingedSpaceObjCongr` at `Ideal.map_id`, the
second on `FormalScheme.restrictOpenIso`.

Note that `rw` does not fire on `Ideal.map (algebraMap R R) I` with `Ideal.map_id`, since `rw`
matches syntactically and `algebraMap R R` is only definitionally `RingHom.id R`, while the *term*
`Ideal.map_id I` typechecks at that type; the `show … from` spelling below is the same one
`AlgebraicGeometry.spf_isSeparatedOverSpf_self` records. -/
theorem isSeparatedOverSpf_of_isOpenImmersion (hI : I.FG) {Z : FormalScheme.{u}}
    (χ : Z.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I)
    [LocallyRingedSpace.IsOpenImmersion χ] :
    IsSeparatedOverSpf hI Z χ := by
  haveI : IsAdicRing (I.map (algebraMap R R)) := by
    rw [show I.map (algebraMap R R) = I from Ideal.map_id I]
    infer_instance
  refine isSeparatedOverSpf_of_isOpenImmersion_aux hI (hI.map (algebraMap R R))
    (locallyRingedSpaceObjCongr (Ideal.map_id I))
    (locallyRingedSpaceMap I (I.map (algebraMap R R)) (algebraMap R R) Ideal.le_comap_map)
    ((locallyRingedSpaceObjCongr_hom_eq_map (Ideal.map_id I) Ideal.le_comap_map).symm) χ
    (fun T => isSeparatedOverSpf_restrictOpen_Spf (A := R) I hI T)

/-- **The inclusion of an open formal subscheme is a separated morphism** (EGA I §10.15), at an
arbitrary target and an arbitrary open.

The cover of the target is the one `FormalScheme.isSeparatedHom_id` uses — the ranges of the affine
charts `FormalScheme.LocallyFG` supplies, one per point — and the per-chart clause is
`FormalScheme.isSeparatedOverSpf_of_isOpenImmersion` at the composite of
`FormalScheme.restrictOpenMap` with the chart identification, which is an open immersion by
`FormalScheme.isOpenImmersion_restrictOpenMap` and because the identification is an isomorphism.

The chart isomorphism is elaborated first at its own spelling and only then ascribed to the
`FormalScheme.Spf` one, for the reason `FormalScheme.isSeparatedHom_id` records: instance search
matches at reducible transparency and `FormalScheme.Spf` is not reducible, so the open-immersion
instance for the chart is not found if the ascription is made up front.

Neither `X.restrictOpen hX U` nor `X` is a `FormalScheme.Spf` for a general `X`, and the morphism
has range `U` (`FormalScheme.range_restrictOpenι_base`), so it is an isomorphism only at `U = ⊤`.
That is what makes this a value the base-affine predicate and the identity could not supply between
them. -/
theorem isSeparatedHom_restrictOpenHom (hX : X.LocallyFG) (U : Opens X) :
    IsSeparatedHom (X.restrictOpen_locallyFG hX U) hX (X.restrictOpenHom hX U) := by
  haveI : LocallyRingedSpace.IsOpenImmersion (X.restrictOpenHom hX U).toLRSHom :=
    inferInstanceAs (LocallyRingedSpace.IsOpenImmersion (X.restrictOpenι hX U))
  have hX' := hX
  choose R hcr hts I hadic f hIfg hmem hopen using hX'
  refine ⟨X, fun x => ⟨Set.range (f x).base, (hopen x).base_open.isOpen_range⟩, ?_, fun x => ?_⟩
  · exact Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ⟨x, hmem x⟩
  · haveI := hopen x
    have e₁ := X.restrictOpenIso hX
      ⟨Set.range (f x).base, (hopen x).base_open.isOpen_range⟩ (f x) rfl
    have e₀ : (FormalScheme.Spf (I x)).toLocallyRingedSpace ≅
        (X.restrictOpen hX
          ⟨Set.range (f x).base, (hopen x).base_open.isOpen_range⟩).toLocallyRingedSpace := e₁
    exact ⟨R x, hcr x, hts x, I x, hadic x, hIfg x, e₀.symm,
      isSeparatedOverSpf_of_isOpenImmersion (hIfg x) _⟩

/-! ### Statement (A) at an open inside one affine chart

`FormalScheme.isSeparatedOverSpf_of_isOpenImmersion` above is stated over the base the source
already lies over, which is the shape the per-chart clause of `FormalScheme.IsSeparatedHom` asks
for and the reason the base change was trivialised at `A := R`. Issue 2148 wants the other shape:
an open of a formal scheme **over `Spf R`**, where the affine it sits inside is `Spf (I·A)` for an
`R`-algebra `A` and the structural morphism factors through it. Restoring the base change costs
nothing — `FormalScheme.isSeparatedOverSpf_restrictOpen_Spf` is already stated at a general `A` —
and it is what turns the transport above into a statement about a *source* restriction.

**What this settles, and what it does not.** Issue 1987's statement (A) asks that
`FormalScheme.IsSeparatedOverSpf` survive restricting the source to an arbitrary open of an
arbitrary presented `X`. The three theorems below settle it whenever the open lies inside **one**
chart, with no refinement of the chart family and no new datum: the restriction is then an open
subscheme of a single `Spf (I·A)`, which issue 1990 already covers. **(A) at a general open is
untouched** — an open meeting two charts needs the basic-open refinement of the chart family that
issue 2148's goal 2 is about, and the cross-chart overlap element for it is
`FormalSpectrum.exists_refined_overlap_element` (`FormalSchemes.BasicOpenChartImage`).

**Which standing sentences these theorems move, named rather than certified.** Of the four files
that describe the missing statement, three quantify over the **open** and their claims survive:
`FormalSchemes.SpfOpenSeparated`, `FormalSchemes.GeneralSeparatedHom` and
`FormalSchemes.AwayBaseFactorisationRange`. The first and the third also offer a reader the
closest thing the tree has, which is no longer `FormalScheme.isSeparatedOverSpf_restrictOpen_Spf`,
so each gains a clause naming the chart-local case. The fourth quantifies over the **source** and
is false after this issue: `FormalSchemes.GeneralSeparatedHomLocal`'s refinement bullet said
source restriction had landed at no source other than an affine `FormalScheme.Spf`, and the
theorems below land it at an arbitrary one; it is repaired there.
`FormalSchemes.GeneralSeparatedScheme`'s inventory of every value of
`FormalScheme.IsSeparatedOverSpf` on this tree gains the three below, which that file's own
rebuild rule admits — they conclude in the predicate, they are not its criteria or transports,
they are not conjunctions with `FormalScheme.IsRelativelyTopFiniteType`, and none of them takes a
`FormalScheme.IsSeparatedOverSpf` as a hypothesis. **Naming the sentence that moved is checkable;
certifying that none did is not**, which is why the first version of this paragraph said the
latter and was wrong about one of its four.

**And the missing half cannot be assembled out of this one.** `FormalScheme.IsSeparatedHom` is
local on the **target**: its cover is a cover of `Y` and its per-piece clause is
`FormalScheme.IsSeparatedOverSpf` of a *preimage*. A family of opens of the **source**, each inside
a chart and together covering `W`, is not of that shape, and there is **no rule on this tree that
glues `FormalScheme.IsSeparatedOverSpf` along a cover of the source** — the predicate is an
existential over a presentation of the whole of `X` restricted to `W`. Conservativity's hard
direction, which is what would let a target-local statement be read back as one, is one of the
directions `FormalSchemes.GeneralSeparatedHom` records as open. That is the reason the general case
is a datum construction and not a covering argument.
-/

section ChartLocal

variable {A : Type u} [CommRing A] [Algebra R A]
variable [TopologicalSpace A] [IsAdicRing (I.map (algebraMap R A))]

/-- **A formal scheme that open-immerses into an affine chart over the base is separated over the
base.** The `A`-general form of `FormalScheme.isSeparatedOverSpf_of_isOpenImmersion`: the target of
the open immersion is `Spf (I·A)` for an `R`-algebra `A`, and the structural morphism is the
immersion followed by the map of formal spectra induced by `algebraMap R A`.

The two are **not** in a specialisation relation on the nose in either direction, for the reason
this file's docstring records: at `A := R` the ideal `Ideal.map (algebraMap R R) I` is equal to `I`
by `Ideal.map_id` and not by `rfl`, so recovering the earlier statement from this one costs exactly
the `FormalSpectrum.locallyRingedSpaceObjCongr` transport that its own proof already spends. Both
are kept.

The open immersion is spent once, on `FormalScheme.restrictOpenIso` at the open cut out by the
range of `χ`; `FormalScheme.isSeparatedOverSpf_restrictOpen_Spf` supplies the statement there and
`FormalScheme.isSeparatedOverSpf_of_iso` moves it across. The `show` ascription on the
open-immersion instance is here for the same reason `FormalScheme.isSeparatedHom_restrictOpenHom`
ascribes its chart isomorphism by hand: instance search matches at reducible transparency and
`FormalScheme.Spf` is not reducible, so the instance for `χ` is not found at the
`FormalScheme.Spf` spelling of its target unless it is put there by hand. The **reason** is shared
and the **device** is not — that proof delays the `FormalScheme.Spf` spelling until after the
isomorphism is elaborated, and this one puts the instance at that spelling. -/
theorem isSeparatedOverSpf_of_isOpenImmersion_chart (hI : I.FG) {Z : FormalScheme.{u}}
    (χ : Z.toLocallyRingedSpace ⟶ locallyRingedSpaceObj (I.map (algebraMap R A)))
    [himm : LocallyRingedSpace.IsOpenImmersion χ] :
    IsSeparatedOverSpf hI Z
      (χ ≫ locallyRingedSpaceMap I (I.map (algebraMap R A)) (algebraMap R A)
        Ideal.le_comap_map) := by
  haveI : LocallyRingedSpace.IsOpenImmersion
      (show Z.toLocallyRingedSpace ⟶
        (FormalScheme.Spf (I.map (algebraMap R A))).toLocallyRingedSpace from χ) := himm
  obtain ⟨T, hT⟩ : ∃ T : Opens (FormalScheme.Spf (I.map (algebraMap R A))),
      Set.range χ.base = (T : Set (FormalScheme.Spf (I.map (algebraMap R A)))) :=
    ⟨⟨Set.range χ.base, himm.base_open.isOpen_range⟩, rfl⟩
  have hfac := (FormalScheme.Spf (I.map (algebraMap R A))).restrictOpenIso_hom_comp
    (locallyFG_Spf (hI.map (algebraMap R A))) T χ hT
  refine isSeparatedOverSpf_of_iso hI
    ((FormalScheme.Spf (I.map (algebraMap R A))).restrictOpenIso
      (locallyFG_Spf (hI.map (algebraMap R A))) T χ hT).symm ?_
    (isSeparatedOverSpf_restrictOpen_Spf I hI T)
  rw [Iso.symm_hom, Iso.inv_comp_eq, ← Category.assoc, hfac]
  rfl

/-- **Statement (A) at an open contained in one affine chart** (EGA I §10.15): if `W` lies inside
the range of an open immersion `j : Spf (I·A) ⟶ X` whose composite with the structural morphism is
the map of formal spectra induced by `algebraMap R A`, then `X` restricted to `W` is separated over
`Spf R`.

No presentation of `X` appears and none is built. The only thing the hypothesis is used for is to
factor the inclusion of `W` through `j`: `LocallyRingedSpace.IsOpenImmersion.lift` does that on the
range containment, `LocallyRingedSpace.IsOpenImmersion.lift_fac` makes the triangle commute, and
the lift is again an open immersion by the same `delta` of
`LocallyRingedSpace.IsOpenImmersion.lift` that `FormalScheme.isOpenImmersion_restrictOpenMap` above
performs, followed by instance search.

`W` is an arbitrary open of `X` inside the chart, not a basic open of it: the basic opens are what
`FormalScheme.isSeparatedOverSpf_restrictOpen_Spf` builds its presentation from, one chart per
basic open inside the image, and that happens inside the theorem this one calls. -/
theorem isSeparatedOverSpf_restrictOpen_of_subset_range (hI : I.FG) (hX : X.LocallyFG)
    {s : X.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I} (W : Opens X)
    (j : locallyRingedSpaceObj (I.map (algebraMap R A)) ⟶ X.toLocallyRingedSpace)
    [LocallyRingedSpace.IsOpenImmersion j]
    (hjs : j ≫ s =
      locallyRingedSpaceMap I (I.map (algebraMap R A)) (algebraMap R A) Ideal.le_comap_map)
    (hW : (W : Set X) ⊆ Set.range j.base) :
    IsSeparatedOverSpf hI (X.restrictOpen hX W) (X.restrictOpenι hX W ≫ s) := by
  have hrange : Set.range (X.restrictOpenι hX W).base ⊆ Set.range j.base := by
    rw [range_restrictOpenι_base]; exact hW
  haveI : LocallyRingedSpace.IsOpenImmersion
      (LocallyRingedSpace.IsOpenImmersion.lift j (X.restrictOpenι hX W) hrange) := by
    delta LocallyRingedSpace.IsOpenImmersion.lift
    infer_instance
  have hfac := LocallyRingedSpace.IsOpenImmersion.lift_fac j (X.restrictOpenι hX W) hrange
  have key := isSeparatedOverSpf_of_isOpenImmersion_chart (A := A) hI
    (Z := X.restrictOpen hX W) (LocallyRingedSpace.IsOpenImmersion.lift j
      (X.restrictOpenι hX W) hrange)
  rwa [← hjs, ← Category.assoc, hfac] at key

end ChartLocal

/-- **Statement (A) at an open contained in one chart of a presentation.** The hypothesis of
`FormalScheme.isSeparatedOverSpf_restrictOpen_of_subset_range` is exactly what a presentation hands
over at each index: `AffineChartedFibreDatumX.ι_xStructMap` says the `i`-th glue inclusion followed
by the glued structural morphism is `AffineChartedFibreDatumX.xStructMapChart i`, which **is** the
map of formal spectra induced by `algebraMap R (A i)`, and the comparison `e` carries that from
`AffineChartedFibreDatumX.xGlued` to `X`.

This is the form issue 1987's statement (A) is quoted in — a presented `X`, its own charts — with
the containment hypothesis that issue 2148's goal 2 exists to remove. At a `W` meeting two charts
the datum has to be refined, and the two halves of that refinement are
`FormalSpectrum.exists_refined_overlap_element` and
`FormalSpectrum.awayCompletionCongrBasicOpenAlg` (`FormalSchemes.BasicOpenChartImage`,
`FormalSchemes.AwayCompletionRestrictUnique`).

The two ascriptions are the price of the datum's instance-implicit fields, and they are in opposite
directions. The compatibility square is proved **before** the `letI` block, in term mode rather
than by `rw`: the index type of `AffineChartedFibreDatumX.xFormalGlueData` agrees with the datum's
own only up to unfolding, so `rw` reports the goal as not type-correct at `instances` transparency
where `Category.assoc` and `congrArg` do not care. The open-immersion instance is re-ascribed
**after** it, since the target's spelling changes once the datum's ring and algebra fields are
let-bound. -/
theorem isSeparatedOverSpf_restrictOpen_of_subset_range_ι {hI : I.FG} (hX : X.LocallyFG)
    {s : X.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I}
    {BX : Type u} [CommRing BX] [Algebra R BX] {DX : AffineChartedFibreDatumX R I hI BX}
    (e : DX.xGlued.toLocallyRingedSpace ≅ X.toLocallyRingedSpace)
    (he : e.hom ≫ s = DX.xStructMap) (i : DX.J) (W : Opens X)
    (hW : (W : Set X) ⊆ Set.range (DX.xFormalGlueData.ι i ≫ e.hom).base) :
    IsSeparatedOverSpf hI (X.restrictOpen hX W) (X.restrictOpenι hX W ≫ s) := by
  have hjs : (DX.xFormalGlueData.ι i ≫ e.hom) ≫ s = DX.xStructMapChart i :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun m => DX.xFormalGlueData.ι i ≫ m) he).trans (DX.ι_xStructMap i))
  haveI himm : LocallyRingedSpace.IsOpenImmersion (DX.xFormalGlueData.ι i ≫ e.hom) := by
    haveI := DX.xFormalGlueData.ι_isOpenImmersion i
    haveI : LocallyRingedSpace.IsOpenImmersion e.hom := inferInstance
    infer_instance
  letI := DX.commRing
  letI := DX.algebra
  letI := DX.topology i
  letI := DX.isAdic i
  haveI : LocallyRingedSpace.IsOpenImmersion
      (show locallyRingedSpaceObj (I.map (algebraMap R (DX.A i))) ⟶ X.toLocallyRingedSpace
        from DX.xFormalGlueData.ι i ≫ e.hom) := himm
  exact isSeparatedOverSpf_restrictOpen_of_subset_range (A := DX.A i) hI hX W
    (DX.xFormalGlueData.ι i ≫ e.hom) hjs hW

/-- **The same in the `FormalScheme.IsSeparatedHom` vocabulary**, which is the form the open
directions of §10.15 consume. Free from
`FormalScheme.isSeparatedOverSpf_restrictOpen_of_subset_range` through
`FormalScheme.isSeparatedHom_of_isSeparatedOverSpf`, exactly as
`FormalScheme.isSeparatedHom_restrictOpen_Spf` is free from its own base-affine form. -/
theorem isSeparatedHom_restrictOpen_of_subset_range {A : Type u} [CommRing A] [Algebra R A]
    [TopologicalSpace A] [IsAdicRing (I.map (algebraMap R A))] (hI : I.FG) (hX : X.LocallyFG)
    {s : X.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I} (W : Opens X)
    (j : locallyRingedSpaceObj (I.map (algebraMap R A)) ⟶ X.toLocallyRingedSpace)
    [LocallyRingedSpace.IsOpenImmersion j]
    (hjs : j ≫ s =
      locallyRingedSpaceMap I (I.map (algebraMap R A)) (algebraMap R A) Ideal.le_comap_map)
    (hW : (W : Set X) ⊆ Set.range j.base) :
    IsSeparatedHom (X.restrictOpen_locallyFG hX W) (locallyFG_Spf hI)
      (FormalScheme.Hom.mk (X.restrictOpenι hX W ≫ s)) :=
  isSeparatedHom_of_isSeparatedOverSpf hI _ _
    (isSeparatedOverSpf_restrictOpen_of_subset_range hI hX W j hjs hW)

end AlgebraicGeometry.FormalScheme

namespace AlgebraicGeometry

open _root_.CompletedTensorProduct _root_.CompletedTensorAwayInterchange

/-! ### Statement (A) at an open that is a union of chart ranges

The section above settles statement (A) whenever the open lies inside **one** chart. This one
settles it at the opposite extreme — an open that is a **union of whole chart ranges** of a
presentation — and the two together are exactly the cases reachable without refining the chart
family, which is the residue issue 2148's goal 2 names.

## The two halves, and why the second one is free

Dropping charts from a presentation is not a construction. Every field of
`AlgebraicGeometry.AffineChartedFibreDatumX` is a `∀` over its index type, so an injection
`e : J' → DX.J` pulls each of them back and `AffineChartedFibreDatumX.reindex` below is a structure
literal with no proof obligation of its own: the `≠` hypotheses it has to produce come from `e`
being injective and nothing else. What is not free is that the result still presents an open of
`X` and is still separated, and those are the two halves here.

**Separatedness is the surprising half, and it is free too — once the criterion is put in the right
form.** `BothChartedFibreDatumXY.isSeparated_iff_isClosed_preimage_ι`
(`FormalSchemes.GeneralSeparatedChartPreimage`) is stated over the product charts of
`X ×_{Spf R} X`, whose index is a *pair* of chart indices, and
`BothChartedFibreDatumXY.preimage_range_diagonal'_eq_range_chartCodiagonalMap`
(`FormalSchemes.GeneralSeparatedChartCodiagonal`) identifies what each product chart sees of the
diagonal as the range of `AffineChartedFibreDatumX.chartCodiagonalMap i j`, which is built from
`A i`, `A j`, `g i j` and `τ i j` and from nothing else in the datum.
`BothChartedFibreDatumXY.isSeparated_iff_isClosed_range_chartCodiagonalMap`
(`FormalSchemes.GeneralSeparatedChartCodiagonal`, put there by issue 2148) packages the two into a
single equivalence

```
IsSeparated DX σX hστX hσcX ↔
  ∀ i j, i ≠ j → IsClosed (Set.range (DX.chartCodiagonalMap i j _).base)
```

whose right-hand side quantifies over **one ordered pair of charts at a time**. A subfamily's pairs
are a subset of the whole family's, and its chart codiagonal at a pair is the original's — by
`rfl`, since `AffineChartedFibreDatumX.reindex` changes no chart algebra and no overlap element —
so `BothChartedFibreDatumXY.isSeparated_reindex` is the restriction of a `∀` and costs three lines.
The diagonal pairs `i = j` never enter: they are discharged inside the equivalence by
`CompletedTensorProduct.codiagonal_surjective`, which is a fact about `A i` alone.

That the equivalence is what makes this work is worth stating as a **negative**: the
`FormalScheme`-level predicate `AlgebraicGeometry.FormalScheme.IsSeparatedOverSpf` is an
existential over a presentation of the whole of `X`, and the categorical definition
`BothChartedFibreDatumXY.IsSeparated` is a closed-immersion condition on a morphism into
`X ×_{Spf R} X`; neither has any visible restriction map to a subfamily. The pair-local form does,
and this is the first consumer **outside** `FormalSchemes.GeneralSeparatedChartCodiagonal` that
needs the `←` direction of the criterion as well as the `→` one — inside that file
`BothChartedFibreDatumXY.isSeparated_of_chartCodiagonal_surjective` is that direction and nothing
else.

**The geometric half** is `AffineChartedFibreDatumX.glueChartMorphisms`
(`FormalSchemes.ChartedDatumGlueMorphisms`) at the ambient datum's own chart inclusions. Their
overlap condition is `CategoryTheory.GlueData.ofGlueData'_ι_comp`, which holds outright; they are
open immersions because a glue inclusion always is; and they meet only along the double overlaps by
`LocallyRingedSpace.GlueData.range_ι_inter_subset`. So
`AffineChartedFibreDatumX.isOpenImmersion_reindexHom` and
`AffineChartedFibreDatumX.range_reindexHom` are the criterion of
`FormalSchemes.ChartedDatumGlueOpenImmersion` applied to a family that was already on the tree, and
the subfamily's glued object is the open `⋃ i, range (ι (e i))` of `X`.

## What this closes, and the shape of what is left

**What is left of goal 2 no longer mentions the open.** Statement (A) at a general open of a
general presented `X` now follows from a single `W`-independent statement: *every presentation of
`X` can be refined to one all of whose chart ranges are basic opens of the original charts.* Given
that, an arbitrary open `W` is a union of refined chart ranges — the basic opens of an affine chart
are a basis (`FormalSpectrum.exists_basicOpen_le`, used in `FormalSchemes.SpfOpenSeparated` for the
one-chart case) and the chart ranges cover `X` — and the theorem below finishes. The cross-chart
overlap element such a refinement needs is `FormalSpectrum.exists_refined_overlap_element`
(`FormalSchemes.BasicOpenChartImage`) and the identification of two presentations of one basic open
is `FormalSpectrum.awayCompletionCongrBasicOpenAlg` (`FormalSchemes.AwayCompletionRestrictUnique`);
the refinement's own `σ` and its two laws are what remains unbuilt.

**Which standing sentences this moves.** `FormalSchemes.SpfOpenSeparated` and
`FormalSchemes.AwayBaseFactorisationRange` each carry a clause naming the chart-local case as the
closest the tree has to (A); both gain the union-of-charts case beside it. The claims that (A) at
an **arbitrary** open of a general presented `X` is unproved survive untouched, in all four files —
a union of chart ranges is not an arbitrary open, and no open meeting a chart partially is of this
shape. `FormalSchemes.GeneralSeparatedScheme`'s inventory of every value of
`AlgebraicGeometry.FormalScheme.IsSeparatedOverSpf` gains
`BothChartedFibreDatumXY.isSeparatedOverSpf_reindex_xGlued` and
`BothChartedFibreDatumXY.isSeparatedOverSpf_restrictOpen_of_iUnion_range_ι` by its own rebuild
rule, and not `BothChartedFibreDatumXY.isSeparated_reindex`, which concludes in the datum-level
predicate.

## Placement, measured rather than argued

The two moves this section could make are **independent, and only one of them is declined**.

**The criterion is not here.**
`BothChartedFibreDatumXY.isSeparated_iff_isClosed_range_chartCodiagonalMap` is in
`FormalSchemes.GeneralSeparatedChartCodiagonal`, beside the two identifications it is assembled
from and beside `BothChartedFibreDatumXY.isSeparated_of_chartCodiagonal_surjective`, whose diagonal
branch was a verbatim copy of the equivalence's and is now that equivalence's `Iff.mpr`. That is a
move into an **existing** module, so it adds no import edge, moves `scripts/closure_audit.py` by
**0**, and costs only re-elaboration: the reverse closure of
`FormalSchemes.GeneralSeparatedChartCodiagonal` is **16**, so seventeen modules including itself.
The dedup is why it is worth that and not merely tidier — a criterion whose sufficient-condition
form already lives in another file cannot be deduplicated from here.

**The datum constructions are here, and that is declined on a ratio.**
`AffineChartedFibreDatumX.reindex` and `AffineChartedFibreDatumX.reindexHom` belong by the tree's
own rule with `AlgebraicGeometry.AffineChartedFibreDatumX`, which does not import
`FormalSchemes.GeneralSeparatedChartCodiagonal`; a leaf over both plus
`FormalSchemes.GeneralSeparatedScheme` and `FormalSchemes.OpenFormalSubscheme` was built and
audited before this disposition was taken, and the next two figures are that one-off measurement of
a tree that was then discarded rather than a standing claim about this one. It cost **25**
`scripts/closure_audit.py` MISMATCHes across **20** files: every module in the leaf's import
closure whose docstring quotes how many dependents it has gains one of them. The reverse closure of
`FormalSchemes.StructureSheaf` is **526**, and that file is one of the twenty, so what prices the
disposition is the repair and not the leaf. In this file the audit is unmoved at **0**, no import
edge is added, and nothing outside this file re-elaborates: the reverse closure of
`FormalSchemes.GeneralSeparatedHomRestrictOpen` is **0**. So the move is **declined on that ratio
and not on principle**, exactly as this file declines
`FormalScheme.isOpenImmersion_restrictOpenMap`'s move above, and is worth re-costing the moment a
second consumer appears — the refinement of goal 2 will be one.
-/

namespace AffineChartedFibreDatumX

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable [TopologicalSpace R] [IsAdicRing I]
variable {BX : Type u} [CommRing BX] [Algebra R BX]
variable (DX : AffineChartedFibreDatumX R I hI BX)

/-- **A subfamily of a chart family, as a datum in its own right.** Every field of
`AlgebraicGeometry.AffineChartedFibreDatumX` is a `∀` over the index type, so an injection
`e : J' → DX.J` pulls all of them back and the only thing that has to be produced is a proof of
`e i ≠ e j` from `i ≠ j`, which is what injectivity is. No chart algebra, no overlap element and no
transition is changed, and that is what makes every statement below hold by `rfl` or by
restricting a `∀`.

Injectivity is needed and not decoration: the `τ`, `σ` and triple-overlap fields are indexed by
*distinct* indices, and a non-injective `e` would be asked for a transition between a chart and
itself. -/
def reindex {J' : Type u} (e : J' → DX.J) (he : Function.Injective e) :
    AffineChartedFibreDatumX R I hI BX :=
  letI := DX.commRing
  letI := DX.algebra
  letI := DX.topology
  letI := DX.isAdic
  { J := J'
    A := fun i => DX.A (e i)
    commRing := fun i => DX.commRing (e i)
    algebra := fun i => DX.algebra (e i)
    g := fun i j => DX.g (e i) (e j)
    τ := fun i j h => DX.τ (e i) (e j) fun hh => h (he hh)
    τ_symm := fun i j _ => DX.τ_symm (e i) (e j) _
    t' := fun i j k hij hik hjk =>
      DX.t' (e i) (e j) (e k) (fun hh => hij (he hh)) (fun hh => hik (he hh))
        (fun hh => hjk (he hh))
    t_fac := fun i j k hij hik hjk =>
      DX.t_fac (e i) (e j) (e k) (fun hh => hij (he hh)) (fun hh => hik (he hh))
        (fun hh => hjk (he hh))
    cocycle := fun i j k hij hik hjk =>
      DX.cocycle (e i) (e j) (e k) (fun hh => hij (he hh)) (fun hh => hik (he hh))
        (fun hh => hjk (he hh))
    topology := fun i => DX.topology (e i)
    isAdic := fun i => DX.isAdic (e i)
    xt' := fun i j k hij hik hjk =>
      DX.xt' (e i) (e j) (e k) (fun hh => hij (he hh)) (fun hh => hik (he hh))
        (fun hh => hjk (he hh))
    xt_fac := fun i j k hij hik hjk =>
      DX.xt_fac (e i) (e j) (e k) (fun hh => hij (he hh)) (fun hh => hik (he hh))
        (fun hh => hjk (he hh))
    xcocycle := fun i j k hij hik hjk =>
      DX.xcocycle (e i) (e j) (e k) (fun hh => hij (he hh)) (fun hh => hik (he hh))
        (fun hh => hjk (he hh)) }

variable {J' : Type u} (e : J' → DX.J) (he : Function.Injective e)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The chart codiagonal of a subfamily is the original's**, by `rfl`: it is assembled from
`A i`, `A j`, `g i j` and `τ i j`, and `AffineChartedFibreDatumX.reindex` carries all four across
unchanged. This is the
whole reason separatedness restricts. -/
theorem reindex_chartCodiagonalMap (i j : J') (hij : i ≠ j) :
    (DX.reindex e he).chartCodiagonalMap i j hij =
      DX.chartCodiagonalMap (e i) (e j) (fun hh => hij (he hh)) := rfl

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The structural morphism of a subfamily chart is the original's**, by `rfl`. -/
theorem reindex_xStructMapChart (i : J') :
    (DX.reindex e he).xStructMapChart i = DX.xStructMapChart (e i) := rfl

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The ambient datum's chart inclusions satisfy the subfamily's own overlap condition.** This is
`CategoryTheory.GlueData.ofGlueData'_ι_comp` at `AffineChartedFibreDatumX.xGlueData'`, where the
overlap immersion is `FormalSpectrum.basicOpenChart` and the transition is
`awayCompletionTransition` — the two spellings
`AffineChartedFibreDatumX.glueChartMorphisms` asks for. Nothing about the subfamily is used beyond
`e i ≠ e j`. -/
theorem reindex_ι_naturality (i j : J') (h : i ≠ j) :
    letI := (DX.reindex e he).commRing; letI := (DX.reindex e he).algebra;
    letI := (DX.reindex e he).topology; letI := (DX.reindex e he).isAdic;
    basicOpenChart (I.map (algebraMap R ((DX.reindex e he).A i))) ((DX.reindex e he).g i j) ≫
        DX.xFormalGlueData.ι (e i) =
      awayCompletionTransition ((DX.reindex e he).g i j) ((DX.reindex e he).g j i)
          ((DX.reindex e he).τ i j h) ≫
        basicOpenChart (I.map (algebraMap R ((DX.reindex e he).A j))) ((DX.reindex e he).g j i) ≫
          DX.xFormalGlueData.ι (e j) :=
  CategoryTheory.GlueData.ofGlueData'_ι_comp DX.xGlueData' (e i) (e j) fun hh => h (he hh)

/-- **The comparison morphism of a subfamily**, `X_{J'} ⟶ X`: the ambient datum's own chart
inclusions, glued over the subfamily. -/
def reindexHom :
    (DX.reindex e he).xGlued.toLocallyRingedSpace ⟶ DX.xGlued.toLocallyRingedSpace :=
  (DX.reindex e he).glueChartMorphisms (fun i => DX.xFormalGlueData.ι (e i))
    (DX.reindex_ι_naturality e he)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The comparison restricts to the ambient chart inclusion on each subfamily chart.** -/
@[reassoc (attr := simp)]
theorem ι_reindexHom (i : J') :
    (DX.reindex e he).xFormalGlueData.ι i ≫ DX.reindexHom e he = DX.xFormalGlueData.ι (e i) :=
  (DX.reindex e he).ι_glueChartMorphisms _ _ i

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The comparison's range is the union of the selected chart ranges.** -/
theorem range_reindexHom :
    Set.range (DX.reindexHom e he).base = ⋃ i, Set.range (DX.xFormalGlueData.ι (e i)).base :=
  (DX.reindex e he).range_glueChartMorphisms _ _

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Two selected charts meet only along their double overlap.** The containment is
`LocallyRingedSpace.GlueData.range_ι_inter_subset` at the ambient datum, read through
`AffineChartedFibreDatumX.range_xGlueData_f_comp_of_ne`, which is what rewrites the glue datum's
overlap immersion into the `FormalSpectrum.basicOpenChart` spelling the criterion asks for.

The rewrite is applied with `▸` rather than by `rw`: the subfamily's index type agrees with `J'`
only up to unfolding `AffineChartedFibreDatumX.reindex`, and `rw` reports the goal as not
type-correct at `instances` transparency, the same obstruction
`FormalScheme.isSeparatedOverSpf_restrictOpen_of_subset_range_ι` records above. -/
theorem reindex_range_ι_inter_subset (i j : J') (hij : i ≠ j) :
    letI := (DX.reindex e he).commRing; letI := (DX.reindex e he).algebra;
    Set.range (DX.xFormalGlueData.ι (e i)).base ∩
        Set.range (DX.xFormalGlueData.ι (e j)).base ⊆
      Set.range (basicOpenChart (I.map (algebraMap R ((DX.reindex e he).A i)))
        ((DX.reindex e he).g i j) ≫ DX.xFormalGlueData.ι (e i)).base := by
  have hsub := DX.xLrsGlueData.range_ι_inter_subset (e i) (e j)
  have hrange := DX.range_xGlueData_f_comp_of_ne (e i) (e j) (fun hh => hij (he hh))
    (DX.xFormalGlueData.ι (e i))
  exact hrange ▸ hsub

/-- **The comparison morphism of a subfamily is an open immersion**, so the subfamily's glued
object is the open formal subscheme of `X` cut out by
`AffineChartedFibreDatumX.range_reindexHom`. -/
instance isOpenImmersion_reindexHom :
    LocallyRingedSpace.IsOpenImmersion (DX.reindexHom e he) :=
  (DX.reindex e he).isOpenImmersion_glueChartMorphisms _ _
    (fun i => FormalScheme.GlueData.ι_isOpenImmersion DX.xFormalGlueData (e i))
    (fun i j hij => DX.reindex_range_ι_inter_subset e he i j hij)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The comparison is a morphism over `Spf R`.** Both sides are morphisms out of a glued object,
so `FormalScheme.GlueData.hom_ext` reduces this to the charts, where both are the same
`AffineChartedFibreDatumX.xStructMapChart`.

Written in term mode for the reason `AffineChartedFibreDatumX.reindex_range_ι_inter_subset`
records: `AffineChartedFibreDatumX.xGlued` is `FormalScheme.GlueData.gluedFormalScheme` of the
datum's glue data only up to unfolding, so the composite is not type-correct at `instances`
transparency and `rw` refuses the goal that `FormalScheme.GlueData.hom_ext` produces. -/
@[reassoc (attr := simp)]
theorem reindexHom_comp_xStructMap :
    DX.reindexHom e he ≫ DX.xStructMap = (DX.reindex e he).xStructMap :=
  (DX.reindex e he).xFormalGlueData.hom_ext fun i =>
    ((Category.assoc ((DX.reindex e he).xFormalGlueData.ι i) (DX.reindexHom e he)
          DX.xStructMap).symm.trans
        ((congrArg (fun m => m ≫ DX.xStructMap) (DX.ι_reindexHom e he i)).trans
          (DX.ι_xStructMap (e i)))).trans ((DX.reindex e he).ι_xStructMap i).symm

end AffineChartedFibreDatumX

namespace BothChartedFibreDatumXY

variable {R : Type u} [CommRing R] {I : Ideal R} {hI : I.FG}
variable [TopologicalSpace R] [IsAdicRing I]
variable {BX : Type u} [CommRing BX] [Algebra R BX]
variable (DX : AffineChartedFibreDatumX R I hI BX)
variable
  (σX : letI := DX.commRing; letI := DX.algebra;
    ∀ (i i' i'' : DX.J), i ≠ i' → i ≠ i'' → i' ≠ i'' →
    (awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i i' * DX.g i i'') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (DX.A i'))) (DX.g i' i'' * DX.g i' i)))
  (hστX : letI := DX.commRing; letI := DX.algebra;
    ∀ (i i' i'' : DX.J) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
    (σX i i' i'' h1 h2 h3).symm.toAlgHom.comp (furtherLocSnd I (DX.g i' i'') (DX.g i' i) hI) =
      (furtherLocFst I (DX.g i i') (DX.g i i'') hI).comp (DX.τ i i' h1).symm.toAlgHom)
  (hσcX : letI := DX.commRing; letI := DX.algebra;
    ∀ (i i' i'' : DX.J) (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i''),
    (σX i i' i'' h1 h2 h3).trans ((σX i' i'' i h3 h1.symm h2.symm).trans
      (σX i'' i i' h2.symm h3.symm h1)) =
      AlgEquiv.refl (R := R)
        (A₁ := awayCompletion (I.map (algebraMap R (DX.A i))) (DX.g i i' * DX.g i i'')))

variable {J' : Type u} (e : J' → DX.J) (he : Function.Injective e)

/-- **The triple-overlap datum of a subfamily**: the ambient one at the selected indices. Its two
laws are `BothChartedFibreDatumXY.reindexSigma_furtherLoc` and
`BothChartedFibreDatumXY.reindexSigma_cocycle`, which are the ambient laws at those indices and
nothing else. -/
def reindexSigma :
    letI := (DX.reindex e he).commRing; letI := (DX.reindex e he).algebra;
    ∀ (i i' i'' : (DX.reindex e he).J), i ≠ i' → i ≠ i'' → i' ≠ i'' →
    (awayCompletion (I.map (algebraMap R ((DX.reindex e he).A i)))
        ((DX.reindex e he).g i i' * (DX.reindex e he).g i i'') ≃ₐ[R]
      awayCompletion (I.map (algebraMap R ((DX.reindex e he).A i')))
        ((DX.reindex e he).g i' i'' * (DX.reindex e he).g i' i)) :=
  fun i i' i'' h1 h2 h3 =>
    σX (e i) (e i') (e i'') (fun hh => h1 (he hh)) (fun hh => h2 (he hh)) (fun hh => h3 (he hh))

omit [TopologicalSpace R] [IsAdicRing I] in
include hστX he in
/-- **The subfamily's `σ`/`τ` restriction law**, the ambient *hστX* at the selected indices. -/
theorem reindexSigma_furtherLoc (i i' i'' : J') (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i'') :
    letI := (DX.reindex e he).commRing; letI := (DX.reindex e he).algebra
    (reindexSigma DX σX e he i i' i'' h1 h2 h3).symm.toAlgHom.comp
        (furtherLocSnd I ((DX.reindex e he).g i' i'') ((DX.reindex e he).g i' i) hI) =
      (furtherLocFst I ((DX.reindex e he).g i i') ((DX.reindex e he).g i i'') hI).comp
        ((DX.reindex e he).τ i i' h1).symm.toAlgHom :=
  hστX (e i) (e i') (e i'') (fun hh => h1 (he hh)) (fun hh => h2 (he hh)) (fun hh => h3 (he hh))

omit [TopologicalSpace R] [IsAdicRing I] in
include hσcX he in
/-- **The subfamily's algebra triple cocycle**, the ambient *hσcX* at the selected indices. -/
theorem reindexSigma_cocycle (i i' i'' : J') (h1 : i ≠ i') (h2 : i ≠ i'') (h3 : i' ≠ i'') :
    letI := (DX.reindex e he).commRing; letI := (DX.reindex e he).algebra
    (reindexSigma DX σX e he i i' i'' h1 h2 h3).trans
        ((reindexSigma DX σX e he i' i'' i h3 h1.symm h2.symm).trans
          (reindexSigma DX σX e he i'' i i' h2.symm h3.symm h1)) =
      AlgEquiv.refl (R := R)
        (A₁ := awayCompletion (I.map (algebraMap R ((DX.reindex e he).A i)))
          ((DX.reindex e he).g i i' * (DX.reindex e he).g i i'')) :=
  hσcX (e i) (e i') (e i'') (fun hh => h1 (he hh)) (fun hh => h2 (he hh)) (fun hh => h3 (he hh))

include he in
/-- **Separatedness passes to every subfamily of a chart family.** The pairs of a subfamily are a
subset of the whole family's, and the subfamily's chart codiagonal at a pair is the original's by
`AffineChartedFibreDatumX.reindex_chartCodiagonalMap`, so this is
`BothChartedFibreDatumXY.isSeparated_iff_isClosed_range_chartCodiagonalMap`
(`FormalSchemes.GeneralSeparatedChartCodiagonal`) used in both directions and nothing else.

There is no comparable statement for `AlgebraicGeometry.FormalScheme.IsSeparatedOverSpf` proved
directly: that predicate is an existential over a presentation of the *whole* of `X`, with no
restriction map to a subfamily, which is why the pair-local criterion is what this goes through. -/
theorem isSeparated_reindex (hsep : IsSeparated DX σX hστX hσcX) :
    IsSeparated (DX.reindex e he) (reindexSigma DX σX e he)
      (reindexSigma_furtherLoc DX σX hστX e he) (reindexSigma_cocycle DX σX hσcX e he) := by
  rw [isSeparated_iff_isClosed_range_chartCodiagonalMap]
  intro i j hij
  exact (isSeparated_iff_isClosed_range_chartCodiagonalMap DX σX hστX hσcX).mp hsep
    (e i) (e j) fun hh => hij (he hh)

include he in
/-- **A subfamily of a separated chart family glues to a formal scheme separated over `Spf R`**, at
the presentation the subfamily itself is. The comparison isomorphism is the identity: the object is
the subfamily's own glued object, not something it is compared to. -/
theorem isSeparatedOverSpf_reindex_xGlued (hsep : IsSeparated DX σX hστX hσcX) :
    FormalScheme.IsSeparatedOverSpf hI (DX.reindex e he).xGlued (DX.reindex e he).xStructMap :=
  ⟨BX, inferInstance, inferInstance, DX.reindex e he, reindexSigma DX σX e he,
    reindexSigma_furtherLoc DX σX hστX e he, reindexSigma_cocycle DX σX hσcX e he,
    Iso.refl _, Category.id_comp _, isSeparated_reindex DX σX hστX hσcX e he hsep⟩

include he in
/-- **Statement (A) at an open that is a union of chart ranges of a presentation** (EGA I §10.15):
if `X` is presented by `DX` over `s`, the presentation is separated, and `W` is the union of the
ranges of the charts selected by an injection `e`, then `X` restricted to `W` is separated over
`Spf R`.

This is the form issue 1987 states (A) in — a presented `X`, its own charts — at the class of opens
that needs no refinement of the chart family, and it is the complement of
`FormalScheme.isSeparatedOverSpf_restrictOpen_of_subset_range_ι`, which covers the opens inside a
single chart. Neither subsumes the other and together they do not exhaust the opens of `X`: an open
meeting a chart partially and not contained in one is of neither shape, and is what goal 2's
refinement is for.

The hypothesis is spent twice and the two are independent: `AffineChartedFibreDatumX.reindexHom`
composed with the comparison is an open immersion whose range is `W`, which is what
`FormalScheme.restrictOpenIso` needs, and
`AffineChartedFibreDatumX.reindexHom_comp_xStructMap` is what makes the comparison a morphism over
the base. -/
theorem isSeparatedOverSpf_restrictOpen_of_iUnion_range_ι {X : FormalScheme.{u}}
    (hX : X.LocallyFG) {s : X.toLocallyRingedSpace ⟶ locallyRingedSpaceObj I}
    (ε : DX.xGlued.toLocallyRingedSpace ≅ X.toLocallyRingedSpace) (hε : ε.hom ≫ s = DX.xStructMap)
    (hsep : IsSeparated DX σX hστX hσcX) (W : Opens X)
    (hW : (W : Set X) = ⋃ i, Set.range (DX.xFormalGlueData.ι (e i) ≫ ε.hom).base) :
    FormalScheme.IsSeparatedOverSpf hI (X.restrictOpen hX W) (X.restrictOpenι hX W ≫ s) := by
  have hr : Set.range (DX.reindexHom e he ≫ ε.hom).base = (W : Set X) := by
    rw [hW]
    simp only [LocallyRingedSpace.comp_base, TopCat.coe_comp, Set.range_comp,
      DX.range_reindexHom e he]
    exact Set.image_iUnion
  refine FormalScheme.isSeparatedOverSpf_of_iso hI
    (X.restrictOpenIso hX W (DX.reindexHom e he ≫ ε.hom) hr) ?_
    (isSeparatedOverSpf_reindex_xGlued DX σX hστX hσcX e he hsep)
  rw [← Category.assoc, FormalScheme.restrictOpenIso_hom_comp, Category.assoc, hε]
  exact DX.reindexHom_comp_xStructMap e he

end BothChartedFibreDatumXY

end AlgebraicGeometry
