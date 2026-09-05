import FormalSchemes.Spf

set_option linter.style.header false

/-!
# Stalks of `O_{Spf R}` as a limit: the comparison map, and the question

`FormalSchemes.StructureSheafSections` describes the **sections** of `O_{Spf R}` over an open `U`
as the limit of the tower `n ↦ Γ(U, thickeningSheaf I n)` — `FormalSpectrum.sectionsLimitIso` — and
that description is an **isomorphism for free**: `TopCat.Sheaf.forget` creates limits and
evaluation preserves them, so `Γ(U, -)` carries the limit defining `FormalSpectrum.structureSheaf`
to a limit of rings. Everything downstream of it, up to
`FormalSpectrum.sectionsBasicOpenEquiv` and `FormalSpectrum.globalSectionsEquiv`, rests on that one
formal step.

This file is the **stalk** analogue, and the formal step is exactly what is missing there.
`TopCat.Presheaf.stalkFunctor` is a *filtered colimit*, not a limit-preserving functor, and
filtered colimits do not commute with inverse limits. So the comparison map exists — it is
`CategoryTheory.Limits.limit.lift` applied to the projections `FormalSpectrum.stalkProj`, which
`FormalSchemes.Spf` already builds — but nothing makes it an isomorphism, and **this file does not
claim that it is**.

## What is here

* the tower of stalks, mirroring `FormalSpectrum.sectionsTower` with evaluation at `U` replaced by
  the stalk at `x`;
* the cone compatibility, as a **named** lemma at an arbitrary pair `m ≤ n`. The same computation
  exists on the tree already, as a proof-local `have` against level `0` inside
  `FormalSpectrum.isUnit_of_isUnit_stalkProj` (`FormalSchemes.Thickenings`). That `have` is
  deliberately left where it is: `FormalSchemes.Thickenings` sits directly over
  `FormalSchemes.Spf`, as this file does, so rerouting it would add an import edge and recompile
  that file's reverse closure to replace a nine-line pair of `have`s — a dedup question, and not
  this file's;
* the comparison map and the question it poses;
* the identification of the tower's level `n` with a localization of `R ⧸ I ^ (n + 1)`.

## Main definitions and results

* `FormalSpectrum.stalkAtFunctor`: `FormalSpectrum.sectionsFunctor` with evaluation at an open
  replaced by the stalk at a point — `TopCat.Sheaf.forget` followed by
  `TopCat.Presheaf.stalkFunctor`.
* `FormalSpectrum.stalkTower`: the tower `n ↦ (thickeningSheaf I n).presheaf.stalk x`, i.e.
  `FormalSpectrum.structureSheafFunctor` composed with that.
* `FormalSpectrum.stalkProj_comp_stalkTower_map`: **the cone compatibility** — the level-`n`
  projection composed with the tower's transition map is the level-`m` projection, for every
  `m ≤ n`.
* `FormalSpectrum.stalkCone`, `FormalSpectrum.stalkToLimit` and
  `FormalSpectrum.stalkToLimit_comp_π`: the cone the projections form, the induced
  `O_{Spf R, x} ⟶ lim_n O_{X_n, x}`, and the computation of its legs.
* `FormalSpectrum.IsStalkLimit` and `FormalSpectrum.isStalkLimit_iff_bijective`: **the question,
  posed** — is that comparison an isomorphism? — and its concrete form.
* `FormalSpectrum.levelPrime` and `FormalSpectrum.thickeningStalkLocalizationEquiv`: the level-`n`
  stalk is `Localization.AtPrime` of `R ⧸ I ^ (n + 1)` at the point's image, by
  `FormalSpectrum.thickeningStalkIso` and `AlgebraicGeometry.StructureSheaf.stalkIso`.

## What is *not* proved here

**Whether `FormalSpectrum.stalkToLimit` is an isomorphism.** Nothing here decides
`FormalSpectrum.IsStalkLimit`, in either direction, and it should not be assumed either way. That is
the positive stalk half of EGA I 10.8 and it is the larger piece of work; naming the map is what
lets it be stated.

Informally — and **no declaration below says this**, so it is a reading and not a theorem *here* —
the left-hand side is a colimit over the basic opens `D(f)` containing `x` of
`AdicCompletion (I·R_f) R_f`, since `FormalSpectrum.sectionsBasicOpenEquiv` computes the sections
there and `FormalSpectrum.isTopologicalBasis_basicOpen` says those opens are a basis; so the
question is whether completion commutes with that filtered colimit. That reading is a theorem
elsewhere on the tree: `FormalSpectrum.exists_adicCompletion_germ_eq` and
`FormalSpectrum.exists_basicOpen_res_eq` (`FormalSchemes.StructureSheafStalkBasicOpen`) are its
surjectivity and separation halves, stated without a colimit being formed. Whether completion
commutes with it is not proved there either, and no consequence of the reading is proved here.

**The passage from `Localization.AtPrime` of a quotient to a quotient of `Localization.AtPrime`.**
`thickeningStalkLocalizationEquiv` presents level `n` as a localization of `R ⧸ I ^ (n + 1)`; to
read the limit as an adic completion of the *stalk* `O_{Spec R, x}` one wants that localization
identified with `R_p ⧸ I ^ (n + 1) · R_p`, and then
`AdicCompletion.towerLimitRingEquiv` — the bridge `FormalSchemes.Sections` uses for the sections
tower — applies. No declaration below does any of that, and it is not missing from the tree: the
algebra is `IsLocalization.atPrime_quotient` and `Localization.atPrimeQuotientEquiv`
(`FormalSchemes.LocalizationQuotientPrime`), the prime-complement input the away case did not need
is `IsLocalization.algebraMapSubmonoid_primeCompl_comap` there, and
`FormalSpectrum.stalkTowerLevelEquiv` and `FormalSpectrum.stalkTowerLimitEquiv`
(`FormalSchemes.StructureSheafStalkLevels`) carry out the identification, and
`FormalSpectrum.specStalkAdicCompletionEquiv` there reaches the adic completion of the stalk of
`O_{Spec R}` itself. The docstring of `thickeningStalkLocalizationEquiv` below says the same thing
at the declaration.

**Non-vacuity is not an issue for the statements below**, because they take the point `x` as an
argument: `FormalSpectrum.IsStalkLimit I x` is a condition at a given point and there is nothing
for it to quantify over vacuously. It is the `∀ x` form that would need a nonemptiness statement,
and the general one is `FormalSpectrum.nonempty_iff_ne_top`
(`FormalSchemes.TateInvNodeChartSpfNonempty`), which this file cannot cite as a term: that module
is far downstream of this one, and a general statement about `Spf` must not import a Tate leaf.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1 and §10.8.
* [The Stacks Project, Tag 0AIX](https://stacks.math.columbia.edu/tag/0AIX)
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]

omit [TopologicalSpace R] [IsAdicRing I]

variable (x : FormalSpectrum I)

/-! ### The tower of stalks -/

/-- **`FormalSpectrum.sectionsFunctor` with evaluation replaced by a stalk**: the functor sending a
sheaf of commutative rings on `Spf R` to its stalk at `x`, obtained by forgetting the sheaf
condition and taking the stalk of the underlying presheaf.

Unlike `sectionsFunctor` it does **not** preserve limits — `TopCat.Presheaf.stalkFunctor` is a
filtered colimit — which is the entire difference between this file and
`FormalSchemes.StructureSheafSections`. -/
abbrev stalkAtFunctor : TopCat.Sheaf CommRingCat (TopCat.of (FormalSpectrum I)) ⥤ CommRingCat :=
  TopCat.Sheaf.forget CommRingCat (TopCat.of (FormalSpectrum I)) ⋙
    TopCat.Presheaf.stalkFunctor CommRingCat x

/-- The tower `n ↦ (thickeningSheaf I n).presheaf.stalk x` of stalks of the thickening sheaves at a
fixed point `x ∈ Spf R`. This is `FormalSpectrum.sectionsTower` with `sectionsFunctor` replaced by
`stalkAtFunctor`. -/
abbrev stalkTower : ℕᵒᵖ ⥤ CommRingCat := structureSheafFunctor I ⋙ stalkAtFunctor I x

theorem stalkTower_obj (n : ℕ) :
    (stalkTower I x).obj ⟨n⟩ = (thickeningSheaf I n).presheaf.stalk x :=
  rfl

/-- **The projections form a cone.** The level-`n` projection `FormalSpectrum.stalkProj` composed
with the tower's transition map is the level-`m` projection, for every `m ≤ n`: apply the stalk
functor to `CategoryTheory.Limits.limit.w`.

The `m = 0` case of this computation already occurs on the tree, as a proof-local `have` inside
`FormalSpectrum.isUnit_of_isUnit_stalkProj` (`FormalSchemes.Thickenings`), where it factors the
level-`0` projection through the level-`n` one. That occurrence is deliberately left alone:
`FormalSchemes.Thickenings` is not downstream of this file — the two sit side by side directly over
`FormalSchemes.Spf` — so rerouting it would add an import edge and recompile that file's reverse
closure to replace a nine-line pair of `have`s. -/
theorem stalkProj_comp_stalkTower_map {m n : ℕ} (h : m ≤ n) :
    stalkProj I x n ≫ (stalkTower I x).map (homOfLE h).op = stalkProj I x m := by
  have hw : limit.π (structureSheafFunctor I) ⟨n⟩ ≫
      (structureSheafFunctor I).map (homOfLE h).op = limit.π (structureSheafFunctor I) ⟨m⟩ :=
    limit.w (structureSheafFunctor I) (homOfLE h).op
  rw [stalkProj, stalkProj, ← hw]
  exact (Functor.map_comp _ _ _).symm

/-- The stalk of `O_{Spf R}` at `x`, as a cone over the tower of stalks of the thickening sheaves,
with `FormalSpectrum.stalkProj` for its legs. -/
def stalkCone : Cone (stalkTower I x) where
  pt := (structureSheaf I).presheaf.stalk x
  π :=
    { app := fun n => stalkProj I x n.unop
      naturality := by
        intro j k f
        simp only [Functor.const_obj_map]
        exact (stalkProj_comp_stalkTower_map I x (leOfHom f.unop)).symm }

/-! ### The comparison map, and the question -/

/-- **The comparison map `O_{Spf R, x} ⟶ lim_n O_{X_n, x}`.** It exists for the formal reason that
`FormalSpectrum.stalkProj` is a cone; nothing here makes it an isomorphism, and the module
docstring says why it is not automatic. -/
def stalkToLimit : (structureSheaf I).presheaf.stalk x ⟶ limit (stalkTower I x) :=
  limit.lift (stalkTower I x) (stalkCone I x)

@[simp, reassoc]
theorem stalkToLimit_comp_π (n : ℕ) :
    stalkToLimit I x ≫ limit.π (stalkTower I x) ⟨n⟩ = stalkProj I x n :=
  limit.lift_π (stalkCone I x) ⟨n⟩

/-- **The question this file exists to name**: is the stalk of `O_{Spf R}` at `x` the limit of the
stalks of the thickening sheaves?

It is **undecided on this tree**, in both directions. The positive answer is the stalk half of
EGA I 10.8 — that the stalk of the completion is the completion of the stalk — and it is stated
here as a property of the comparison map rather than as an abstract isomorphism so that a proof
has a specific morphism to be about. -/
def IsStalkLimit : Prop := IsIso (stalkToLimit I x)

/-- `FormalSpectrum.IsStalkLimit` read on elements: the comparison map is bijective. -/
theorem isStalkLimit_iff_bijective :
    IsStalkLimit I x ↔ Function.Bijective (stalkToLimit I x).hom :=
  ⟨fun h => (ConcreteCategory.isIso_iff_bijective _).mp h,
    fun h => (ConcreteCategory.isIso_iff_bijective _).mpr h⟩

/-! ### The levels of the tower are localizations -/

/-- The prime of `R ⧸ I ^ (n + 1)` corresponding to `x ∈ Spf R` under the homeomorphism
`FormalSpectrum.thickeningTopIso` of `Spf R` with the `n`-th thickening's spectrum. -/
def levelPrime (n : ℕ) : PrimeSpectrum (R ⧸ I ^ (n + 1)) :=
  (ConcreteCategory.hom (thickeningTopIso I n).hom) x

/-- **The level-`n` stalk is a localization of `R ⧸ I ^ (n + 1)`.**
`FormalSpectrum.thickeningStalkIso` identifies it with a stalk of the structure sheaf of
`Spec (R ⧸ I ^ (n + 1))`, and `AlgebraicGeometry.StructureSheaf.stalkIso` presents that stalk as a
localization at the corresponding prime.

This is as far as the identification goes here. Turning `Localization.AtPrime` of a quotient into a
quotient of `Localization.AtPrime` — which is what makes the limit of this tower an adic completion
of `O_{Spec R, x}` — is not proved below, but it is not missing either: it is
`Localization.atPrimeQuotientEquiv` (`FormalSchemes.LocalizationQuotientPrime`), a specialisation
of Mathlib's `IsLocalization.of_surjective`, and `FormalSpectrum.stalkTowerLevelEquiv`
(`FormalSchemes.StructureSheafStalkLevels`) applies it to this equivalence. See the module
docstring for the ingredients. -/
def thickeningStalkLocalizationEquiv (n : ℕ) :
    ((thickeningSheaf I n).presheaf.stalk x : Type u) ≃+*
      Localization.AtPrime (levelPrime I x n).asIdeal :=
  (thickeningStalkIso I n x).commRingCatIsoToRingEquiv.trans
    (StructureSheaf.stalkIso (R ⧸ I ^ (n + 1)) (levelPrime I x n)).symm.toRingEquiv

end FormalSpectrum
