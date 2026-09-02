import FormalSchemes.AffineThickenings
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.RingTheory.Ideal.Quotient.PowTransition

set_option linter.style.header false

/-!
# The kernel of the tower of sections over an open with affine thickenings

`FormalSchemes.AdicCofinalOpenImmersion` reduces the adicity of an affine open immersion of formal
spectra to its **openness half** `J ≤ √(I · B)`, and records a sketch of the only route proposed
for it: write `B` as the inverse limit of `Bₙ = Γ (U, O_{Spec (R ⧸ Iⁿ⁺¹)})` and run successive
approximation against a finite generating set of `I`. That sketch needs three inputs,

1. the transition maps `Bₙ₊₁ ↠ Bₙ` are surjective,
2. `B ↠ B₀`,
3. `ker (Bₙ₊₁ → Bₙ) = Iⁿ⁺¹ · Bₙ₊₁`,

of which `FormalSchemes.AffineThickenings` supplies the first two from the hypothesis
`FormalSpectrum.HasAffineThickenings` and names the third as the one it does not prove. **This file
proves the third input**, in the form that covers every pair of levels at once, and nothing here
should be read as proving the openness half: the successive approximation itself is still absent,
and so is any statement relating `I · B` to `J`.

## The general fact, and where the quasi-coherence hides

The kernel in question is the sections over `Uₙ₊₁` of the ideal sheaf of the closed immersion
`Spec (R ⧸ Iⁿ⁺¹) ↪ Spec (R ⧸ Iⁿ⁺²)`, and identifying it with the extension of `Iⁿ⁺¹` is
quasi-coherence of that ideal sheaf. Mathlib has exactly that, as
`AlgebraicGeometry.Scheme.IdealSheafData`: `AlgebraicGeometry.Scheme.ker_of_isAffine` says the
kernel ideal sheaf of a morphism into an affine scheme is
`AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop` of the kernel on global sections, and
`AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop_ideal` evaluates that at an affine open as the
*extension* of the global ideal. So the geometric content is
`AlgebraicGeometry.ker_app_specMap` below, which holds for an arbitrary ring map `φ : A ⟶ C` — no
surjectivity, no nilpotence, no finiteness — and needs only that the open is affine.

Affineness of the open is not decoration and is why `FormalSpectrum.HasAffineThickenings` is a
hypothesis rather than a lemma: `AlgebraicGeometry.Scheme.Hom.ker` is indexed by the *affine* opens
of the target, and `AlgebraicGeometry.Scheme.Hom.ker_apply` identifies it with the componentwise
kernel only there.

## What this buys, and what it does not

`FormalSpectrum.ker_towerSectionsComap` is stated between two arbitrary levels `m ≤ n`, which is
what the successive approximation will want: at `m = n`, `n + 1` it is the sketch's third input,
`ker (Bₙ₊₁ → Bₙ) = Iⁿ⁺¹ · Bₙ₊₁`, and at `m = 0` it is `ker (Bₙ ↠ B₀) = I · Bₙ`, the statement
whose limit over `n` the approximation has to compare with `I · B`. Both are recorded separately.
Note that the level-`0` form is *not* obtained by composing the step form `n` times — it is the
same lemma at another pair of levels, so no induction is involved.

The limit step that consumes these — from `ker (Bₙ ↠ B₀) = I · Bₙ` for every `n`, together with
`Bₙ₊₁ ↠ Bₙ` and `B = lim Bₙ`, conclude `ker (B ↠ B₀) = I · B` — is **not attempted here**; it is
`FormalSpectrum.ker_sectionsPi_zero` in `FormalSchemes.TowerLimitKernel`, which is where
`Ideal.FG` enters. Everything in `FormalSchemes.AdicCofinalOpenImmersion` — in particular the
openness half `J ≤ √(I · B)` — is untouched by either file, and so is
`FormalSchemes.AdicOnSections`'s refutation of the on-the-nose containment.

## Main definitions

* `FormalSpectrum.towerRingHom`: `Ideal.Quotient.factorPow` at the shifted indices, bundled into
  `CommRingCat` — the transition map `R ⧸ I ^ (n + 1) ⟶ R ⧸ I ^ (m + 1)` of the tower of
  thickenings, for `m ≤ n`. At `m = n`, `n + 1` it is `FormalSpectrum.stepRingHom`.
* `FormalSpectrum.thickeningSectionsMk`: the canonical ring map
  `R →+* Γ (U, thickeningSheaf I n)`.
* `FormalSpectrum.stepQuotientEquiv`: the ring isomorphism
  `Bₙ₊₁ ⧸ (Iⁿ⁺¹ · Bₙ₊₁) ≃+* Bₙ`, which is the surjection of `FormalSchemes.AffineThickenings`
  and the kernel computed here, read as one statement.

## Main results

* `AlgebraicGeometry.ker_appTop_specMap`, `AlgebraicGeometry.ker_app_specMap`,
  `AlgebraicGeometry.ker_structureSheaf_comap`: the kernel of `Spec φ` on sections over an affine
  open is the extension of `RingHom.ker φ`, in the `Scheme.Hom.app` and the
  `StructureSheaf.comap` spellings.
* `FormalSpectrum.map_topMap_thickeningOpen_tower`: the opens cut out of two levels of the tower
  by one open of `Spf R` correspond under the transition map, for any two levels. Its plumbing is
  `FormalSpectrum.towerRingHom_succ`,
  `FormalSpectrum.thickeningTopIso_hom_comp_topMap_towerRingHom`,
  `FormalSpectrum.topMap_towerRingHom_comp_inv` and
  `FormalSpectrum.thickeningOpen_le_comap_tower`, each the arbitrary-levels form of a statement
  `FormalSchemes.StructureSheaf` proves for one step.
* `FormalSpectrum.ker_towerSectionsComap`, `FormalSpectrum.ker_towerSectionsComap_map`: the
  kernel of `Bₙ → Bₘ`, as an extension from `R ⧸ I ^ (n + 1)` and as an extension from `R`.
* `FormalSpectrum.ker_stepSheafHom_app`: **the sketch's third input**,
  `ker (Bₙ₊₁ → Bₙ) = Iⁿ⁺¹ · Bₙ₊₁`.
* `FormalSpectrum.ker_sectionsComap_zero`: its level-`0` companion, `ker (Bₙ ↠ B₀) = I · Bₙ`.
* `FormalSpectrum.map_thickeningSectionsMk_pow`, `FormalSpectrum.ker_sectionsComap_zero_pow`: the
  image of `I ^ (n + 1)` at level `n` is zero, so the reduction map `Bₙ ↠ B₀` has **nilpotent**
  kernel.
* `FormalSpectrum.ker_stepSheafHom_app_top`,
  `FormalSpectrum.ker_stepSheafHom_app_basicOpen`: the two hypothesis-free instances.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.12.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

variable {A C : CommRingCat} (φ : A ⟶ C)

/-- The kernel of `Spec φ` on **global** sections is the image of `RingHom.ker φ` under
`Scheme.ΓSpecIso`. This is the affine bookkeeping that `AlgebraicGeometry.ker_app_specMap` runs
through `Scheme.ΓSpecIso_naturality`; it carries no geometric content. -/
theorem ker_appTop_specMap :
    RingHom.ker ((Spec.map φ).appTop).hom
      = Ideal.map ((Scheme.ΓSpecIso A).inv).hom (RingHom.ker φ.hom) := by
  rw [← RingHom.ker_equiv_comp _ (Scheme.ΓSpecIso C).commRingCatIsoToRingEquiv,
    RingEquiv.toRingHom_eq_coe, Iso.commRingCatIsoToRingEquiv_toRingHom,
    ← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality, CommRingCat.hom_comp,
    ← RingHom.comap_ker]
  exact (Ideal.map_comap_of_equiv
    (Scheme.ΓSpecIso A).commRingCatIsoToRingEquiv.symm).symm

/-- **The kernel of `Spec φ` on sections over an affine open is the extension of
`RingHom.ker φ`.** No hypothesis on `φ`.

This is the quasi-coherence of the kernel ideal sheaf, read off Mathlib's
`AlgebraicGeometry.Scheme.IdealSheafData`: `AlgebraicGeometry.Scheme.Hom.ker_apply` identifies the
kernel ideal sheaf at an affine open with the componentwise kernel there,
`AlgebraicGeometry.Scheme.ker_of_isAffine` computes it from global sections because the target is
affine, and `AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop_ideal` evaluates that as an
extension.

Affineness of `V` cannot be dropped, and the reason is structural rather than an artefact of the
proof: `AlgebraicGeometry.Scheme.Hom.ker` is an ideal sheaf *datum*, indexed by the affine opens of
the target, so a value at a non-affine open is not something the statement could even name. What
`AlgebraicGeometry.Scheme.Hom.ker_apply` supplies is that at an affine open the datum agrees with
the componentwise kernel; without quasi-compactness of the morphism only the one-sided
`AlgebraicGeometry.Scheme.Hom.ideal_ker_le` holds, but here the morphism is `Spec` of a ring map,
so quasi-compactness is an instance and affineness of the open is the only hypothesis in play. -/
theorem ker_app_specMap (V : (Spec A).Opens) (hV : IsAffineOpen V) :
    RingHom.ker ((Spec.map φ).app V).hom
      = Ideal.map (algebraMap A Γ(Spec A, V)) (RingHom.ker φ.hom) := by
  rw [← Scheme.Hom.ker_apply (Spec.map φ) ⟨V, hV⟩, Scheme.ker_of_isAffine,
    Scheme.IdealSheafData.ofIdealTop_ideal, ker_appTop_specMap, Ideal.map_map]
  rfl

/-- `AlgebraicGeometry.ker_app_specMap` in the `StructureSheaf.comap` spelling, which is the one
the tower of thickenings of a formal spectrum is written in. The shape of the statement matches
`AlgebraicGeometry.surjective_structureSheaf_comap`, which is the same map's surjectivity. -/
theorem ker_structureSheaf_comap (V : Opens (PrimeSpectrum A)) (hV : IsAffineOpen (X := Spec A) V)
    {W : Opens (PrimeSpectrum C)} (hW : W = (Opens.map (Spec.topMap φ)).obj V)
    (h : (W : Set (PrimeSpectrum C)) ⊆ PrimeSpectrum.comap φ.hom ⁻¹' (V : Set (PrimeSpectrum A))) :
    RingHom.ker (StructureSheaf.comap φ.hom V W h)
      = Ideal.map (algebraMap A Γ(Spec A, V)) (RingHom.ker φ.hom) := by
  subst hW
  exact ker_app_specMap φ V hV

end AlgebraicGeometry

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]

section Tower

omit [TopologicalSpace R] [IsAdicRing I]

variable {m n : ℕ}

/-- The transition map `R ⧸ I ^ (n + 1) ⟶ R ⧸ I ^ (m + 1)` of the tower of thickenings, for
`m ≤ n`: the ring map classifying the closed immersion of the `m`-th thickening into the `n`-th
one.

This is `Ideal.Quotient.factorPow` at the shifted indices the thickenings of `Spf R` are numbered
by, bundled into `CommRingCat` so that `Spec.topMap` can be applied to it. It stands to
`FormalSpectrum.stepRingHom` — which is the same term at `m = n`, `n + 1`, recorded as
`FormalSpectrum.towerRingHom_succ` — exactly as `Ideal.Quotient.factorPow` stands to
`Ideal.Quotient.factorPowSucc`. -/
def towerRingHom (hmn : m ≤ n) :
    CommRingCat.of (R ⧸ I ^ (n + 1)) ⟶ CommRingCat.of (R ⧸ I ^ (m + 1)) :=
  CommRingCat.ofHom (Ideal.Quotient.factorPow I (Nat.succ_le_succ hmn))

theorem towerRingHom_succ (n : ℕ) : towerRingHom I (Nat.le_succ n) = stepRingHom I n :=
  rfl

/-- The triangle of maps out of `Spf R` into the thickenings `Spec (R ⧸ I ^ (m + 1))` and
`Spec (R ⧸ I ^ (n + 1))` commutes with the transition map of the tower. This is
`FormalSpectrum.thickeningTopIso_hom_comp_topMap_stepRingHom` at an arbitrary pair of levels. -/
theorem thickeningTopIso_hom_comp_topMap_towerRingHom (hmn : m ≤ n) :
    (thickeningTopIso I m).hom ≫ Spec.topMap (towerRingHom I hmn) = (thickeningTopIso I n).hom := by
  ext x
  exact congrFun (comap_factor_comp_toThickening I (Nat.succ_ne_zero m) (Nat.succ_ne_zero n)
    (Nat.succ_le_succ hmn)) x

theorem topMap_towerRingHom_comp_inv (hmn : m ≤ n) :
    Spec.topMap (towerRingHom I hmn) ≫ (thickeningTopIso I n).inv = (thickeningTopIso I m).inv := by
  rw [Iso.comp_inv_eq, ← thickeningTopIso_hom_comp_topMap_towerRingHom I hmn, Iso.inv_hom_id_assoc]

variable (U : Opens (FormalSpectrum I))

/-- **The opens cut out of two levels of the tower by one open of `Spf R` correspond under the
transition map.** This is `FormalSpectrum.map_topMap_thickeningOpen` at an arbitrary pair of
levels. -/
theorem map_topMap_thickeningOpen_tower (hmn : m ≤ n) :
    (Opens.map (Spec.topMap (towerRingHom I hmn))).obj (thickeningOpen I n U)
      = thickeningOpen I m U := by
  have h : (Opens.map (Spec.topMap (towerRingHom I hmn) ≫ (thickeningTopIso I n).inv)).obj U
      = thickeningOpen I m U := by
    rw [topMap_towerRingHom_comp_inv]
    rfl
  exact h

theorem thickeningOpen_le_comap_tower (hmn : m ≤ n) :
    (thickeningOpen I m U : Set (PrimeSpectrum (R ⧸ I ^ (m + 1)))) ⊆
      PrimeSpectrum.comap (towerRingHom I hmn).hom ⁻¹'
        (thickeningOpen I n U : Set (PrimeSpectrum (R ⧸ I ^ (n + 1)))) := by
  rw [← map_topMap_thickeningOpen_tower I U hmn]
  exact fun x hx => hx

end Tower

/-- The canonical ring map `R →+* Γ (U, thickeningSheaf I n)`: reduce modulo `I ^ (n + 1)` and
take the resulting section of the structure sheaf of the `n`-th thickening. -/
def thickeningSectionsMk (n : ℕ) (U : Opens (FormalSpectrum I)) :
    R →+* ((thickeningSheaf I n).presheaf.obj (op U) : Type u) :=
  (algebraMap (R ⧸ I ^ (n + 1)) ((thickeningSheaf I n).presheaf.obj (op U))).comp
    (Ideal.Quotient.mk (I ^ (n + 1)))

variable {I}

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The kernel of the tower of sections, between two arbitrary levels `m ≤ n`, is the extension
of the kernel of the transition map of the tower.**

The hypothesis is used exactly once, at level `n`, to make the open of the ambient thickening
affine; the geometric content is `AlgebraicGeometry.ker_structureSheaf_comap`. -/
theorem ker_towerSectionsComap {U : Opens (FormalSpectrum I)} (hU : HasAffineThickenings I U)
    {m n : ℕ} (hmn : m ≤ n) :
    RingHom.ker (StructureSheaf.comap (towerRingHom I hmn).hom (thickeningOpen I n U)
        (thickeningOpen I m U) (thickeningOpen_le_comap_tower I U hmn))
      = Ideal.map (algebraMap (R ⧸ I ^ (n + 1))
          ((thickeningSheaf I n).presheaf.obj (op U)))
          (RingHom.ker (towerRingHom I hmn).hom) :=
  ker_structureSheaf_comap (towerRingHom I hmn) _ (hU n)
    (map_topMap_thickeningOpen_tower I U hmn).symm _

omit [TopologicalSpace R] [IsAdicRing I] in
/-- `FormalSpectrum.ker_towerSectionsComap` with the kernel of the transition map computed: the
kernel of `Bₙ → Bₘ` is the ideal of `Bₙ` generated by the image of `I ^ (m + 1)`. -/
theorem ker_towerSectionsComap_map {U : Opens (FormalSpectrum I)} (hU : HasAffineThickenings I U)
    {m n : ℕ} (hmn : m ≤ n) :
    RingHom.ker (StructureSheaf.comap (towerRingHom I hmn).hom (thickeningOpen I n U)
        (thickeningOpen I m U) (thickeningOpen_le_comap_tower I U hmn))
      = Ideal.map (thickeningSectionsMk I n U) (I ^ (m + 1)) := by
  have hker : RingHom.ker (towerRingHom I hmn).hom
      = Ideal.map (Ideal.Quotient.mk (I ^ (n + 1))) (I ^ (m + 1)) :=
    Ideal.Quotient.factor_ker (Ideal.pow_le_pow_right (Nat.succ_le_succ hmn))
  rw [ker_towerSectionsComap hU hmn, hker, Ideal.map_map]
  rfl

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The third input of the successive-approximation sketch**: over an open with affine
thickenings the transition map of the tower of sections has kernel `Iⁿ⁺¹ · Bₙ₊₁`.

`FormalSchemes.AffineThickenings` supplies the other two inputs, `Bₙ₊₁ ↠ Bₙ`
(`FormalSpectrum.surjective_stepSheafHom_app`) and `B ↠ B₀`
(`FormalSpectrum.surjective_sectionsPi_zero`). The limit step that would turn the three into
`ker (B ↠ B₀) = I · B` is not proved anywhere; see this module's docstring. -/
theorem ker_stepSheafHom_app {U : Opens (FormalSpectrum I)} (hU : HasAffineThickenings I U)
    (n : ℕ) :
    RingHom.ker ((stepSheafHom I n).hom.app (op U)).hom
      = Ideal.map (thickeningSectionsMk I (n + 1) U) (I ^ (n + 1)) :=
  ker_towerSectionsComap_map hU (Nat.le_succ n)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The level-`0` companion**: over an open with affine thickenings the reduction map
`Bₙ ↠ B₀` has kernel `I · Bₙ`. This is `FormalSpectrum.ker_towerSectionsComap_map` at `m = 0`, not
a composite of `FormalSpectrum.ker_stepSheafHom_app` — no induction is involved. -/
theorem ker_sectionsComap_zero {U : Opens (FormalSpectrum I)} (hU : HasAffineThickenings I U)
    (n : ℕ) :
    RingHom.ker (StructureSheaf.comap (towerRingHom I (Nat.zero_le n)).hom (thickeningOpen I n U)
        (thickeningOpen I 0 U) (thickeningOpen_le_comap_tower I U (Nat.zero_le n)))
      = Ideal.map (thickeningSectionsMk I n U) I := by
  rw [ker_towerSectionsComap_map hU (Nat.zero_le n), pow_one]

omit [TopologicalSpace R] [IsAdicRing I] in
/-- The image of `I ^ (n + 1)` in `Γ (U, thickeningSheaf I n)` is zero: the sections at level `n`
are an algebra over `R ⧸ I ^ (n + 1)`, so `FormalSpectrum.thickeningSectionsMk` factors through
that quotient by construction. -/
theorem map_thickeningSectionsMk_pow (n : ℕ) (U : Opens (FormalSpectrum I)) :
    Ideal.map (thickeningSectionsMk I n U) (I ^ (n + 1)) = ⊥ := by
  rw [Ideal.map_eq_bot_iff_le_ker]
  intro x hx
  simpa [thickeningSectionsMk, RingHom.mem_ker] using
    congrArg (algebraMap (R ⧸ I ^ (n + 1)) ((thickeningSheaf I n).presheaf.obj (op U)))
      (Ideal.Quotient.eq_zero_iff_mem.mpr hx)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The reduction map of the tower has nilpotent kernel**: `(ker (Bₙ ↠ B₀)) ^ (n + 1) = ⊥`, so
`Spec B₀` is an infinitesimal thickening inside `Spec Bₙ` and the two have the same underlying
space. This is `FormalSpectrum.ker_sectionsComap_zero` combined with the fact that `I ^ (n + 1)`
already dies at level `n`.

The same argument runs for `Bₙ ↠ Bₘ` at any `m ≤ n`, only with a different exponent: that kernel
is the extension of `I ^ (m + 1)` (`FormalSpectrum.ker_towerSectionsComap_map`), so its `k`-th
power is the extension of `I ^ ((m + 1) * k)` and is `⊥` as soon as `(m + 1) * k ≥ n + 1` — for
`m > 0` that is a *smaller* exponent than the `n + 1` recorded here. Only `m = 0` is stated,
because it is the level the successive approximation compares against. -/
theorem ker_sectionsComap_zero_pow {U : Opens (FormalSpectrum I)}
    (hU : HasAffineThickenings I U) (n : ℕ) :
    RingHom.ker (StructureSheaf.comap (towerRingHom I (Nat.zero_le n)).hom (thickeningOpen I n U)
        (thickeningOpen I 0 U) (thickeningOpen_le_comap_tower I U (Nat.zero_le n))) ^ (n + 1)
      = ⊥ := by
  rw [ker_sectionsComap_zero hU n]
  exact (Ideal.map_pow (thickeningSectionsMk I n U) I (n + 1)).symm.trans
    (map_thickeningSectionsMk_pow n U)

/-- **Level `n` of the tower is the quotient of level `n + 1` by the extension of `I ^ (n + 1)`.**

This is the surjection `FormalSpectrum.surjective_stepSheafHom_app` and the kernel
`FormalSpectrum.ker_stepSheafHom_app` read as one statement, and it is the form in which the
sketch's tower is an actual tower of quotients. -/
def stepQuotientEquiv {U : Opens (FormalSpectrum I)} (hU : HasAffineThickenings I U) (n : ℕ) :
    (((thickeningSheaf I (n + 1)).presheaf.obj (op U) : Type u) ⧸
        Ideal.map (thickeningSectionsMk I (n + 1) U) (I ^ (n + 1)))
      ≃+* ((thickeningSheaf I n).presheaf.obj (op U) : Type u) :=
  (Ideal.quotEquivOfEq (ker_stepSheafHom_app hU n).symm).trans
    (RingHom.quotientKerEquivOfSurjective (surjective_stepSheafHom_app hU n))

variable (I)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Unconditional instance at the top open**: `⊤` has affine thickenings, so the transition map
of the tower of sections over `⊤` has kernel the extension of `I ^ (n + 1)`. -/
theorem ker_stepSheafHom_app_top (n : ℕ) :
    RingHom.ker ((stepSheafHom I n).hom.app (op ⊤)).hom
      = Ideal.map (thickeningSectionsMk I (n + 1) ⊤) (I ^ (n + 1)) :=
  ker_stepSheafHom_app (hasAffineThickenings_top I) n

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Unconditional instance on a basic open**: every `D(f) ⊆ Spf R` has affine thickenings, so
the transition map of the tower of sections over `D(f)` has kernel the extension of `I ^ (n + 1)`.
The rings involved are the localizations `(R ⧸ I ^ (n + 1))_f`
(`FormalSpectrum.isLocalization_away_basicOpen_sections`). -/
theorem ker_stepSheafHom_app_basicOpen (f : R) (n : ℕ) :
    RingHom.ker ((stepSheafHom I n).hom.app (op (basicOpen I f))).hom
      = Ideal.map (thickeningSectionsMk I (n + 1) (basicOpen I f)) (I ^ (n + 1)) :=
  ker_stepSheafHom_app (hasAffineThickenings_basicOpen I f) n

end FormalSpectrum
