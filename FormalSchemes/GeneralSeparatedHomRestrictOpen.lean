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
closure is **75** against this file's **0**, and the instance has one consumer, here; it is
declined on the same ratio and for the same reason as the three helpers
`FormalSchemes.GeneralSeparatedHomIdentity` declines, and is worth re-costing when a second
consumer appears.

Two of those three helpers now **have** that second consumer, which is the event that file's note
asks to be recorded: `FormalSpectrum.locallyRingedSpaceObjCongr` and
`FormalSpectrum.locallyRingedSpaceObjCongr_hom_eq_map` are used here as well as by
`AlgebraicGeometry.spf_isSeparatedOverSpf_self`. The ratio that declined their move has not changed
— `FormalSchemes.FormalSpectrum`'s reverse closure is **531** — so this records the second consumer
and moves nothing.

## Main definitions and results

* `AlgebraicGeometry.FormalScheme.isOpenImmersion_restrictOpenMap`: restricting an open immersion
  to the preimage of an open leaves an open immersion.
* `AlgebraicGeometry.FormalScheme.isSeparatedOverSpf_of_isOpenImmersion`: **a formal scheme that
  open-immerses into `Spf I` is separated over `Spf I`**, at an arbitrary presentation.
* `AlgebraicGeometry.FormalScheme.isSeparatedHom_restrictOpenHom`: **the inclusion of an open
  formal subscheme is separated**, at an arbitrary target and an arbitrary open.

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

end AlgebraicGeometry.FormalScheme
