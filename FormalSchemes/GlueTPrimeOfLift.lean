import FormalSchemes.PullbackRangeLRS

set_option linter.style.header false

/-!
# The transition-of-transitions `t'` of a same-target open-immersion glue datum, by lift

Let `Z` be a locally ringed space and let the charts of a `CategoryTheory.GlueData'` all share the
single target `Z` (as they do for the four-chart Tate self-fibre-product `𝔈_q ×_{Spf R} 𝔈_q` and for
the general fibre product `X ×_S Y` over an affine base, where each chart is `Spf` of a completed
tensor product mapping into the common `Spf(A ⊗̂_R B)`). For such a glue datum the transition-of-
transitions field

```
t' i j k : pullback (f i j) (f i k) ⟶ pullback (f j k) (f j i)
```

together with its compatibility

```
t_fac : t' i j k ≫ pullback.snd (f j k) (f j i) = pullback.fst (f i j) (f i k) ≫ t i j
```

can be built **uniformly** by the open-immersion universal property, sidestepping any explicit
pullback plumbing or completed-tensor associativity computation.

Concretely, `pullback.snd (f j k) (f j i)` is an open immersion (base change of the open immersion
`f j k`), so any morphism into its codomain whose topological image lands in its range lifts
canonically through it (`LocallyRingedSpace.IsOpenImmersion.lift`). Taking that morphism to be
`pullback.fst (f i j) (f i k) ≫ t i j` yields `t'` with `t_fac` **free** as `lift_fac`. The single
remaining obligation is the range inclusion

```
Set.range (pullback.fst (f i j) (f i k) ≫ t i j).base
  ⊆ Set.range (pullback.snd (f j k) (f j i)).base
```

which, by cancelling the mono `f j i` and using the range identities below, reduces to a statement
purely about the images of the charts and the transition in `Z` — the genuine geometric content of
the cocycle, isolated away from all categorical bookkeeping.

## Main definitions / results

* `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.range_pullback_fst`: the range of
  `pullback.fst f g` is `f⁻¹(im g)` (companion to `range_pullback_snd`).
* `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.range_pullback_snd_comp`: the range of
  `pullback.snd f g ≫ g` is `im f ∩ im g` (companion to `range_pullback_fst_comp`).
* `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.glueTPrimeOfLift`: the lift-built `t'`.
* `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.glueTPrimeOfLift_fac`: its `t_fac` law
  (`lift_fac`, free).
* `AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion.isIso_glueTPrimeOfLift`: when the range
  inclusion is an equality, `t'` is an isomorphism — the input a genuine `GlueData'.cocycle`
  consumes.

## References

* Mathlib `CategoryTheory.GlueData'` (the `t'`/`t_fac`/`cocycle` fields).
* Mathlib `AlgebraicGeometry.Scheme.Pullback` (the scheme-level analogue of the glue cocycle).
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
-/

open CategoryTheory Limits

namespace AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion

universe u

variable {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)

/-- The range of the underlying map of `pullback.fst f g` is `f⁻¹(im g)`. Companion to
`range_pullback_snd`, obtained from it through the pullback symmetry `X ×_Z Y ≅ Y ×_Z X`. -/
theorem range_pullback_fst [LocallyRingedSpace.IsOpenImmersion g] :
    Set.range (pullback.fst f g).base = f.base ⁻¹' Set.range g.base := by
  have hsurj : Function.Surjective (pullbackSymmetry f g).hom.base := fun y =>
    ⟨(pullbackSymmetry f g).inv.base y, LocallyRingedSpace.iso_inv_base_hom_base_apply _ y⟩
  rw [← pullbackSymmetry_hom_comp_snd f g, LocallyRingedSpace.comp_base, TopCat.coe_comp,
    Set.range_comp, Set.range_eq_univ.mpr hsurj, Set.image_univ, range_pullback_snd]

/-- The range of the underlying map of the canonical map `pullback.snd f g ≫ g : X ×_Z Y ⟶ Z` is the
intersection `im f ∩ im g`. Companion to `range_pullback_fst_comp`, equal to it by
`pullback.condition`. -/
theorem range_pullback_snd_comp [LocallyRingedSpace.IsOpenImmersion f]
    [LocallyRingedSpace.IsOpenImmersion g] :
    Set.range (pullback.snd f g ≫ g).base = Set.range f.base ∩ Set.range g.base := by
  rw [← pullback.condition, range_pullback_fst_comp]

/-! ### The lift-built `t'` and its laws -/

variable {V₁ V₂ W₁ W₂ : LocallyRingedSpace.{u}}
  (a : V₁ ⟶ Z) (b : V₂ ⟶ Z) (c : W₁ ⟶ Z) (d : W₂ ⟶ Z) (τ : V₁ ⟶ W₂)
  [LocallyRingedSpace.IsOpenImmersion a] [LocallyRingedSpace.IsOpenImmersion c]

/-- **The lift-built `t'`.** For charts `a b : ⟶ Z` (source overlaps toward two other charts),
`c d : ⟶ Z` (target overlaps) with `a`, `c` open immersions, and a transition `τ : dom a ⟶ dom d`,
the induced map on triple overlaps `pullback a b ⟶ pullback c d`, constructed as the open-immersion
lift of `pullback.fst a b ≫ τ` through the open immersion `pullback.snd c d`. The hypothesis `H` is
the only geometric input; `t_fac` (below) is then free. -/
noncomputable def glueTPrimeOfLift
    (H : Set.range (pullback.fst a b ≫ τ).base ⊆ Set.range (pullback.snd c d).base) :
    pullback a b ⟶ pullback c d :=
  lift (pullback.snd c d) (pullback.fst a b ≫ τ) H

/-- **The `t_fac` law, for free.** `glueTPrimeOfLift ≫ pullback.snd c d = pullback.fst a b ≫ τ`,
directly by `lift_fac`. This is exactly the `GlueData'.t_fac` field once the charts/transition are
plugged in. -/
@[reassoc]
theorem glueTPrimeOfLift_fac
    (H : Set.range (pullback.fst a b ≫ τ).base ⊆ Set.range (pullback.snd c d).base) :
    glueTPrimeOfLift a b c d τ H ≫ pullback.snd c d = pullback.fst a b ≫ τ :=
  lift_fac _ _ H

/-- **The `t'` first-leg-through-chart law, for free.** Composing the lift-built `t'` with the
*canonical map* `pullback.fst c d ≫ c : pullback c d ⟶ Z` of its target overlap into the common base
`Z` gives `pullback.fst a b ≫ τ ≫ d`. This is the first-leg analogue of `glueTPrimeOfLift_fac` (the
second-leg law `t_fac`): it is obtained from `t_fac` by post-composing with `d` and folding through
`pullback.condition` (`pullback.fst c d ≫ c = pullback.snd c d ≫ d`). It is the `glueTPrimeOfLift`
analogue of Mathlib's `AlgebraicGeometry.Cover.gluedCoverT'_fst`, and the leg law a `GlueData'`
cocycle telescoping (`t' i j k ≫ t' j k i ≫ t' k i j = 𝟙`) reaches for once the composite is
cancelled against the mono `pullback.fst a b ≫ a`: it exposes the genuine transition `τ ≫ d` sitting
on the shared triple overlap, which no amount of categorical bookkeeping can remove (`τ ≫ d ≠ a` in
general — the transition permutes the summands of the overlap object). -/
@[reassoc]
theorem glueTPrimeOfLift_fst_comp
    (H : Set.range (pullback.fst a b ≫ τ).base ⊆ Set.range (pullback.snd c d).base) :
    glueTPrimeOfLift a b c d τ H ≫ pullback.fst c d ≫ c = pullback.fst a b ≫ τ ≫ d := by
  rw [pullback.condition, glueTPrimeOfLift_fac_assoc]

/-- **`t'` is an isomorphism** when the range inclusion is in fact an equality. This upgrades the
lift to an iso (`lift` of an open immersion is an iso precisely when the two ranges coincide), which
is the form a genuine `GlueData'.cocycle` (three `t'` composing to `𝟙`) consumes. The extra
hypotheses (the other source leg `b` an open immersion, `τ` an isomorphism) make
`pullback.fst a b ≫ τ` itself an open immersion, so it too admits the mutually-inverse lift. -/
theorem isIso_glueTPrimeOfLift [LocallyRingedSpace.IsOpenImmersion b] [IsIso τ]
    (H : Set.range (pullback.fst a b ≫ τ).base ⊆ Set.range (pullback.snd c d).base)
    (Heq : Set.range (pullback.fst a b ≫ τ).base = Set.range (pullback.snd c d).base) :
    IsIso (glueTPrimeOfLift a b c d τ H) := by
  haveI : LocallyRingedSpace.IsOpenImmersion (pullback.fst a b ≫ τ) :=
    LocallyRingedSpace.IsOpenImmersion.comp _ _
  refine ⟨lift (pullback.fst a b ≫ τ) (pullback.snd c d) Heq.ge, ?_, ?_⟩
  · rw [glueTPrimeOfLift, ← cancel_mono (pullback.fst a b ≫ τ), Category.assoc, lift_fac,
      Category.id_comp, lift_fac]
  · rw [glueTPrimeOfLift, ← cancel_mono (pullback.snd c d), Category.assoc, lift_fac,
      Category.id_comp, lift_fac]

end AlgebraicGeometry.LocallyRingedSpace.IsOpenImmersion
