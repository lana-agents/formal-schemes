import FormalSchemes.TowerLimitKernel
import FormalSchemes.OpenImmersionIsoOfRangeEq

set_option linter.style.header false

/-!
# The openness half of adicity, over an open whose thickenings are affine

`FormalSchemes.AdicCofinalOpenImmersion` splits the adicity of an affine open immersion of formal
spectra into two containments and settles one of them. For an open immersion
`m : Spf J ⟶ Spf I` with `algebraMap R B = globalSectionsMap I J m`:

* `I · B ≤ √J` — the **nilpotence** half — is `FormalSpectrum.map_le_radical_of_hom`,
  unconditional, for an arbitrary morphism;
* `J ≤ √(I · B)` — the **openness** half — was open in general, and is what this file proves,
  under one hypothesis: that the infinitesimal thickenings of the range of `m` are affine opens
  of the thickenings of `Spf R` (`FormalSpectrum.HasAffineThickenings`,
  `FormalSchemes.AffineThickenings`).

That was the last unformalised step of the sketch recorded in
`FormalSchemes.AdicCofinalOpenImmersion`'s module docstring — *"`√(ker (B ↠ B₀)) = √J` because
both cut out `U`"* — whose earlier steps are `FormalSchemes.AffineThickenings`,
`FormalSchemes.ThickeningTowerKernel` and `FormalSpectrum.ker_sectionsPi_zero`
(`FormalSchemes.TowerLimitKernel`). **It does not prove that the hypothesis holds at an arbitrary
affine open immersion**; that is proved downstream, in
`FormalSchemes.AffineThickeningsOpenImmersion`, and is untouched here. See "What this file leaves
to its successor" below.

## The argument

Write `U = Set.range m.base`, an open of `Spf R`, and `Γ (U, O_{Spf R})` for its sections. The
statement to prove is an equality of closed subsets of `Spec B`, `V (I · B) = V (J)`, of which one
inclusion is the nilpotence half. The other is proved by identifying **both** sets with the points
of `U`.

1. **Every point of `U` names a prime of the sections ring.** The stalk of `O_{Spf R}` at `x` is
   local, so `FormalSpectrum.sectionsPrime` — the contraction of its maximal ideal along the germ
   map — is a prime of `Γ (U, O_{Spf R})`, and a section lies in it exactly when its germ at `x`
   is not a unit.

2. **Over an affine reduction those are all of them.** Invertibility of a germ of `O_{Spf R}` is
   decided at level `0` of the tower (`FormalSpectrum.isUnit_of_isUnit_stalkProj`), level `0` is
   the structure sheaf of `Spec (R ⧸ I)`, and over an affine open a scheme's stalk is the
   localization of its sections at `IsAffineOpen.primeIdealOf` — a bijection between the points
   of the open and the primes of its sections. So the primes of `Γ (U, O_{Spf R})` containing the
   kernel of the reduction map are exactly the `FormalSpectrum.sectionsPrime`s
   (`FormalSpectrum.exists_mem_eq_sectionsPrime`). This is the only place *this file* spends
   affineness, and it spends only level `0`; step 3's imported input spends it at every level.

3. **The kernel of the reduction map is `I · Γ (U, O_{Spf R})`.** That is
   `FormalSpectrum.ker_sectionsPi_zero_eq_sectionsOpenIdeal`, which needs affineness at *every*
   level and finite generation of `I` (`Ideal.FG`).

4. **`m` identifies `Γ (U, O_{Spf R})` with `B`**, by `FormalSpectrum.rangeSectionsHom`, carrying
   `FormalSpectrum.sectionsOpenIdeal I U` to `I · B`.

5. **`m` carries the prime at `m y` to the point `y`.** For an arbitrary morphism of formal
   spectra the stalk map is local, so it neither creates nor destroys invertibility of a germ
   (`FormalSpectrum.mem_sectionsPrime_c_app_res_iff`); and at the top open the prime at a point is
   the point itself (`FormalSpectrum.mem_sectionsPrime_top_iff`, which is
   `FormalSpectrum.isUnit_germ_top_iff` of `FormalSchemes.SpfGammaBase` restated).

Steps 1, 4 and 5 use no affineness and no finite generation; 5 uses no open immersion either. The
open immersion enters in exactly two places: the range is an *open*, so that step 2 has an open to
be affine over, and `FormalSpectrum.rangeSectionsHom` is *surjective*, which is what lets step 5's
equality of contracted primes be cancelled.

## What this file leaves to its successor

The hypothesis, and nothing else. Within this file `FormalSpectrum.HasAffineThickenings` is
unconditional on `⊤` (`FormalSpectrum.hasAffineThickenings_top`), on every basic open
(`FormalSpectrum.hasAffineThickenings_basicOpen`), and on the range of an open immersion that is
the range of a basic-open chart; the general case is carried as a hypothesis throughout.

**It is now discharged**, by `FormalSpectrum.hasAffineThickenings_opensRange`
(`FormalSchemes.AffineThickeningsOpenImmersion`), for an arbitrary affine open immersion and with
no hypothesis on `I`, `J` or the range. So every theorem below has an unconditional companion
there: `FormalSpectrum.le_radical_map_of_openImmersion`,
`FormalSpectrum.isCofinal_map_of_openImmersion` — EGA I 10.12 — and
`AlgebraicGeometry.IsTopologicallyFiniteType.of_openImmersion`.

The route that discharges it is *not* the one the paragraph replaced here expected. It does not go
via "the reduction is affine, hence so is every nilpotent thickening", which would be Serre's
cohomological criterion and is still absent from Mathlib. It produces the spanning family that
`AlgebraicGeometry.isAffineOpen_of_isAffineOpen_basicOpen` asks for in `B` itself and pushes it
forward to every level of the tower at once; see that file's module docstring, and the correction
it records to `FormalSchemes.AffineThickenings`'s account.

## Main definitions

* `FormalSpectrum.sectionsPrime`: the prime of `Γ (U, O_{Spf R})` at a point of `U`.
* `FormalSpectrum.rangeSectionsHom`: the identification of the sections over the range of an open
  immersion with the global sections of its source.

## Main results

* `FormalSpectrum.mem_sectionsPrime_iff_mem_primeIdealOf`,
  `FormalSpectrum.exists_mem_eq_sectionsPrime`: over an open whose reduction is affine, the primes
  of the sections ring containing the kernel of the reduction map are exactly the primes at points
  of the open.
* `FormalSpectrum.mem_sectionsPrime_c_app_res_iff`, `FormalSpectrum.mem_sectionsPrime_top_iff`: the
  prime at a point transports along an arbitrary morphism of formal spectra, and at the top open it
  is the point.
* `FormalSpectrum.bijective_rangeSectionsHom` and its surjective half
  `FormalSpectrum.surjective_rangeSectionsHom`: the identification of the sections over the range
  with the global sections of the source is an isomorphism of rings. Only surjectivity is used
  here; injectivity is what `FormalSchemes.AffineThickeningsOpenImmersion` needs.
* `FormalSpectrum.le_radical_map_of_hasAffineThickenings`: **the openness half.**
* `FormalSpectrum.isCofinal_map_of_hasAffineThickenings`: hence `I · B` is an ideal of definition
  of `B` up to cofinality — the row's statement, under the hypothesis.
* `FormalSpectrum.le_radical_map_of_range_eq_univ`: **unconditionally, for an open immersion that
  is onto** — the hypothesis discharges itself through
  `FormalSpectrum.hasAffineThickenings_top`.
* `FormalSpectrum.le_radical_map_of_range_eq_basicOpenChart`: the basic-open case, which
  `FormalSpectrum.isCofinal_map_of_range_eq_basicOpenChart` already knew by a different route.

  Both of these, and `AlgebraicGeometry.IsTopologicallyFiniteType.of_openImmersion_range_eq_univ`
  below, are special cases of the unconditional forms in
  `FormalSchemes.AffineThickeningsOpenImmersion`; they are kept because they are upstream of it.
  Each says so in its own docstring.
* `AlgebraicGeometry.IsTopologicallyFiniteType.of_openImmersion_of_hasAffineThickenings`,
  `AlgebraicGeometry.IsTopologicallyFiniteType.of_openImmersion_range_eq_univ`: conservativity's
  affine step, under the hypothesis and unconditionally-when-onto.
* `FormalSpectrum.le_radical_pow_of_range_eq_univ`: non-vacuity, `I ≤ √(I ^ 2)` read off a
  presentation of `Spf R` at `I ^ 2`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.12, §10.13.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.3.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]

/-!
### The prime of the sections ring at a point of the open
-/

/-- The prime of `Γ (U, O_{Spf R})` at a point `x ∈ U`. -/
def sectionsPrime (U : Opens (FormalSpectrum I)) (x : FormalSpectrum I) (hx : x ∈ U) :
    PrimeSpectrum ((structureSheaf I).presheaf.obj (op U) : Type u) where
  asIdeal := Ideal.comap ((structureSheaf I).presheaf.germ U x hx).hom
    (IsLocalRing.maximalIdeal ((structureSheaf I).presheaf.stalk x))
  isPrime := Ideal.IsPrime.comap _

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Membership in the prime at `x` is non-invertibility of the germ at `x`.** This is the whole
content of `FormalSpectrum.sectionsPrime`: the stalk is local
(`FormalSpectrum.isLocalRing_structureSheaf_stalk`), and an element of a local ring lies in the
maximal ideal exactly when it is not a unit. -/
theorem mem_sectionsPrime_iff (U : Opens (FormalSpectrum I)) (x : FormalSpectrum I) (hx : x ∈ U)
    (s : ((structureSheaf I).presheaf.obj (op U) : Type u)) :
    s ∈ (sectionsPrime I U x hx).asIdeal ↔
      ¬ IsUnit (((structureSheaf I).presheaf.germ U x hx).hom s) := by
  rw [sectionsPrime, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]

variable (U : Opens (FormalSpectrum I)) (x : FormalSpectrum I)

/-- **Invertibility of a germ of `O_{Spf R}` is decided at level `0` of the tower.** One direction
is functoriality; the other is `FormalSpectrum.isUnit_of_isUnit_stalkProj`, which is where the
locality of the tower is spent. The level-`0` component of a section over `U` is
`FormalSpectrum.sectionsPi`, and `TopCat.Presheaf.stalkFunctor_map_germ_apply` is what identifies
its germ with the projection of the germ. -/
theorem isUnit_germ_iff_isUnit_sectionsPi_zero (hx : x ∈ U)
    (s : ((structureSheaf I).presheaf.obj (op U) : Type u)) :
    IsUnit (((structureSheaf I).presheaf.germ U x hx).hom s) ↔
      IsUnit (((thickeningSheaf I 0).presheaf.germ U x hx).hom ((sectionsPi I 0 U).hom s)) := by
  rw [show ((thickeningSheaf I 0).presheaf.germ U x hx).hom ((sectionsPi I 0 U).hom s) =
      (stalkProj I x 0).hom (((structureSheaf I).presheaf.germ U x hx).hom s) from
    (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
      (limit.π (structureSheafFunctor I) ⟨0⟩).hom s).symm]
  exact ⟨fun h => h.map _, fun h => isUnit_of_isUnit_stalkProj I x 0 _ h⟩

/-- The point of the reduction `Spec (R ⧸ I)` corresponding to `x ∈ U`. -/
def thickeningPoint (hx : x ∈ U) : (thickeningOpen I 0 U : Type u) :=
  ⟨(thickeningTopIso I 0).hom x, hom_mem_thickeningOpen I 0 x hx⟩

/-- **Over an open whose reduction is affine, the prime at `x` is the contraction of Mathlib's
`IsAffineOpen.primeIdealOf`.** Only level `0` of `FormalSpectrum.HasAffineThickenings` is used
here.

Three identifications in a row: the germ is decided at level `0`
(`FormalSpectrum.isUnit_germ_iff_isUnit_sectionsPi_zero`); the level-`0` sheaf is the structure
sheaf of `Spec (R ⧸ I)` transported along `FormalSpectrum.thickeningTopIso`, so its germs are
germs there (`FormalSpectrum.thickeningStalkIso_hom_germ`); and over an affine open the stalk is
the localization of the sections at `IsAffineOpen.primeIdealOf`
(`IsAffineOpen.isLocalization_stalk`), where invertibility of the image of a section is avoidance
of the prime (`IsLocalization.AtPrime.isUnit_to_map_iff`). -/
theorem mem_sectionsPrime_iff_mem_primeIdealOf
    (hU : IsAffineOpen (X := Spec (CommRingCat.of (R ⧸ I ^ (0 + 1)))) (thickeningOpen I 0 U))
    (hx : x ∈ U) (s : ((structureSheaf I).presheaf.obj (op U) : Type u)) :
    s ∈ (sectionsPrime I U x hx).asIdeal ↔
      (sectionsPi I 0 U).hom s ∈ (hU.primeIdealOf (thickeningPoint I U x hx)).asIdeal := by
  rw [mem_sectionsPrime_iff, isUnit_germ_iff_isUnit_sectionsPi_zero]
  set t := (sectionsPi I 0 U).hom s with ht
  haveI := hU.isLocalization_stalk (thickeningPoint I U x hx)
  have hiso : IsUnit (((thickeningSheaf I 0).presheaf.germ U x hx).hom t) ↔
      IsUnit (((Spec.structureSheaf (R ⧸ I ^ (0 + 1))).presheaf.germ (thickeningOpen I 0 U)
        ((thickeningTopIso I 0).hom x) (hom_mem_thickeningOpen I 0 x hx)).hom t) := by
    rw [← thickeningStalkIso_hom_germ I 0 x U hx t]
    exact (isUnit_map_iff (thickeningStalkIso I 0 x).hom.hom _).symm
  rw [hiso]
  have hkey : IsUnit (((Spec.structureSheaf (R ⧸ I ^ (0 + 1))).presheaf.germ
        (thickeningOpen I 0 U) ((thickeningTopIso I 0).hom x)
        (hom_mem_thickeningOpen I 0 x hx)).hom t) ↔
      t ∈ (hU.primeIdealOf (thickeningPoint I U x hx)).asIdeal.primeCompl :=
    IsLocalization.AtPrime.isUnit_to_map_iff
      ((Spec (CommRingCat.of (R ⧸ I ^ (0 + 1)))).presheaf.stalk (thickeningPoint I U x hx).1)
      (hU.primeIdealOf (thickeningPoint I U x hx)).asIdeal t
  rw [hkey]
  exact not_not

variable {I U}

/-- **Every prime of `Γ (U, O_{Spf R})` containing the kernel of the reduction map is the prime at
a point of `U`.** -/
theorem exists_mem_eq_sectionsPrime
    (hU : IsAffineOpen (X := Spec (CommRingCat.of (R ⧸ I ^ (0 + 1)))) (thickeningOpen I 0 U))
    (hsurj : Function.Surjective (sectionsPi I 0 U).hom)
    (p : PrimeSpectrum ((structureSheaf I).presheaf.obj (op U) : Type u))
    (hp : RingHom.ker (sectionsPi I 0 U).hom ≤ p.asIdeal) :
    ∃ (y : FormalSpectrum I) (hy : y ∈ U), p = sectionsPrime I U y hy := by
  haveI : (p.asIdeal.map (sectionsPi I 0 U).hom).IsPrime :=
    Ideal.map_isPrime_of_surjective hsurj hp
  set q : PrimeSpectrum ((thickeningSheaf I 0).presheaf.obj (op U) : Type u) :=
    ⟨p.asIdeal.map (sectionsPi I 0 U).hom, inferInstance⟩ with hq
  obtain ⟨z, hz⟩ : ∃ z : (thickeningOpen I 0 U : Type u), hU.primeIdealOf z = q := by
    refine ⟨hU.isoSpec.inv.base q, ?_⟩
    rw [IsAffineOpen.primeIdealOf]
    change (hU.isoSpec.inv ≫ hU.isoSpec.hom).base q = q
    rw [hU.isoSpec.inv_hom_id]
    rfl
  have hzU : (thickeningTopIso I 0).inv z.1 ∈ U := z.2
  refine ⟨(thickeningTopIso I 0).inv z.1, hzU, ?_⟩
  have hpt : thickeningPoint I U ((thickeningTopIso I 0).inv z.1) hzU = z := by
    apply Subtype.ext
    rw [thickeningPoint]
    exact (thickeningHomeomorph I (0 + 1) (Nat.succ_ne_zero 0)).apply_symm_apply z.1
  apply PrimeSpectrum.ext
  ext s
  rw [mem_sectionsPrime_iff_mem_primeIdealOf I U _ hU hzU s, hpt, hz, hq]
  dsimp only
  constructor
  · exact fun h => Ideal.mem_map_of_mem _ h
  · intro h
    have := Ideal.mem_comap.mpr h
    rwa [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hp] at this

/-!
### Transport along a morphism of formal spectra
-/

section Transport

variable {S : Type u} [CommRing S] [TopologicalSpace S] (K : Ideal S) [IsAdicRing K]

omit [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace S] [IsAdicRing K] in
/-- **The prime at a point transports along any morphism of formal spectra.** -/
theorem mem_sectionsPrime_c_app_res_iff
    (w : locallyRingedSpaceObj K ⟶ locallyRingedSpaceObj I)
    (V : Opens (FormalSpectrum I)) (V' : Opens (FormalSpectrum K))
    (hle : V' ≤ (Opens.map w.base).obj V) (y : FormalSpectrum K) (hy' : y ∈ V')
    (hy : w.base y ∈ V) (s : ((structureSheaf I).presheaf.obj (op V) : Type u)) :
    s ∈ (sectionsPrime I V (w.base y) hy).asIdeal ↔
      ((structureSheaf K).presheaf.map (homOfLE hle).op).hom ((w.c.app (op V)).hom s) ∈
        (sectionsPrime K V' y hy').asIdeal := by
  rw [mem_sectionsPrime_iff, mem_sectionsPrime_iff, not_iff_not,
    TopCat.Presheaf.germ_res_apply,
    show ((structureSheaf K).presheaf.germ ((Opens.map w.base).obj V) y (hle hy')).hom
        ((w.c.app (op V)).hom s) =
        (w.stalkMap y).hom (((structureSheaf I).presheaf.germ V (w.base y) hy).hom s) from
      (LocallyRingedSpace.stalkMap_germ_apply w V y hy s).symm]
  exact (isUnit_map_iff (w.stalkMap y).hom _).symm

/-- **At the top open the prime at a point is the point.** -/
theorem mem_sectionsPrime_top_iff (y : FormalSpectrum K) (b : S) :
    (globalSectionsEquiv K).symm b ∈ (sectionsPrime K ⊤ y trivial).asIdeal ↔
      b ∈ (toPrimeSpectrum K y).asIdeal := by
  rw [mem_sectionsPrime_iff, isUnit_germ_top_iff, not_not]
  rfl

end Transport

/-!
### The openness half
-/

section Openness

variable (I)
variable {B : Type u} [CommRing B] [TopologicalSpace B] (J : Ideal B) [IsAdicRing J]
variable (m : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
  [hm : LocallyRingedSpace.IsOpenImmersion m]

omit [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace B] [IsAdicRing J] in
/-- The preimage of the range of `m` is everything. -/
theorem top_le_map_opensRange :
    (⊤ : Opens (FormalSpectrum J)) ≤
      (Opens.map m.base).obj (LocallyRingedSpace.IsOpenImmersion.opensRange m) :=
  fun y _ => Set.mem_range_self y

omit [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace B] [IsAdicRing J] in
/-- The sheaf component of an open immersion at its own range is an isomorphism: this is the
`PresheafedSpace.IsOpenImmersion.c_iso` field at the source open `⊤`, whose image is the
range. -/
theorem isIso_c_app_opensRange :
    IsIso (m.c.app (op (LocallyRingedSpace.IsOpenImmersion.opensRange m))) := by
  have h1 : LocallyRingedSpace.IsOpenImmersion.opensRange m = hm.base_open.functor.obj ⊤ := by
    apply Opens.ext
    rw [LocallyRingedSpace.IsOpenImmersion.coe_opensRange]
    exact Set.image_univ.symm
  rw [h1]
  exact hm.c_iso ⊤

/-- The identification of `Γ (range m, O_{Spf R})` with `B`. -/
def rangeSectionsHom :
    ((structureSheaf I).presheaf.obj
      (op (LocallyRingedSpace.IsOpenImmersion.opensRange m)) : Type u) →+* B :=
  (globalSectionsEquiv J).toRingHom.comp
    ((((structureSheaf J).presheaf.map
        (homOfLE (top_le_map_opensRange I J m)).op).hom).comp
      (m.c.app (op (LocallyRingedSpace.IsOpenImmersion.opensRange m))).hom)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **`FormalSpectrum.rangeSectionsHom` is bijective.** Its three factors are all isomorphisms:
the sheaf component of an open immersion at its range (`FormalSpectrum.isIso_c_app_opensRange`);
the restriction along `⊤ ≤ m ⁻¹ (range m)`, which is an isomorphism because the two opens are equal
and `Opens` is a preorder; and `FormalSpectrum.globalSectionsEquiv`.

Only the surjective half (`FormalSpectrum.surjective_rangeSectionsHom`) is used in this file, and
it is the only thing the open-immersion hypothesis is used for in
`FormalSpectrum.le_radical_map_of_hasAffineThickenings` beyond the range being open — everything
else here holds for an arbitrary morphism of formal spectra. The injective half is what lets a
spanning family of `B` be *pulled back* to one of `Γ (range m, O_{Spf R})` rather than only pushed
forward, and that is what `FormalSchemes.AffineThickeningsOpenImmersion` consumes; the two halves
are stated together because they have one proof. -/
theorem bijective_rangeSectionsHom : Function.Bijective (rangeSectionsHom I J m) := by
  haveI := isIso_c_app_opensRange I J m
  haveI : IsIso (homOfLE (top_le_map_opensRange I J m)) :=
    ⟨homOfLE le_top, Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  have h1 : Function.Bijective
      (m.c.app (op (LocallyRingedSpace.IsOpenImmersion.opensRange m))).hom :=
    ConcreteCategory.bijective_of_isIso _
  have h2 : Function.Bijective (((structureSheaf J).presheaf.map
      (homOfLE (top_le_map_opensRange I J m)).op).hom) :=
    ConcreteCategory.bijective_of_isIso _
  exact (globalSectionsEquiv J).bijective.comp (h2.comp h1)

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **`FormalSpectrum.rangeSectionsHom` is surjective** — the half of
`FormalSpectrum.bijective_rangeSectionsHom` this file uses. -/
theorem surjective_rangeSectionsHom : Function.Surjective (rangeSectionsHom I J m) :=
  (bijective_rangeSectionsHom I J m).2

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The identification carries the point of `Spf J` at `z` to the prime of the sections ring at
`m z`.** -/
theorem comap_rangeSectionsHom_toPrimeSpectrum (z : FormalSpectrum J) :
    Ideal.comap (rangeSectionsHom I J m) (toPrimeSpectrum J z).asIdeal =
      (sectionsPrime I (LocallyRingedSpace.IsOpenImmersion.opensRange m) (m.base z)
        (Set.mem_range_self z)).asIdeal := by
  ext s
  rw [Ideal.mem_comap, ← mem_sectionsPrime_top_iff J z (rangeSectionsHom I J m s),
    show (globalSectionsEquiv J).symm (rangeSectionsHom I J m s) =
      ((structureSheaf J).presheaf.map (homOfLE (top_le_map_opensRange I J m)).op).hom
        ((m.c.app (op (LocallyRingedSpace.IsOpenImmersion.opensRange m))).hom s) from
    (globalSectionsEquiv J).symm_apply_apply _]
  exact (mem_sectionsPrime_c_app_res_iff J m
    (LocallyRingedSpace.IsOpenImmersion.opensRange m) ⊤ (top_le_map_opensRange I J m) z trivial
    (Set.mem_range_self z) s).symm

omit [TopologicalSpace R] [IsAdicRing I] [TopologicalSpace B] [IsAdicRing J] in
/-- **Restricting a global section of `Spf R` to the range of `m` and transporting it to `B` is
`FormalSpectrum.globalSectionsMap`.** -/
theorem res_c_app_opensRange (s : ((structureSheaf I).presheaf.obj
    (op (⊤ : Opens (FormalSpectrum I))) : Type u)) :
    ((structureSheaf J).presheaf.map (homOfLE (top_le_map_opensRange I J m)).op).hom
        ((m.c.app (op (LocallyRingedSpace.IsOpenImmersion.opensRange m))).hom
          (((structureSheaf I).presheaf.map (homOfLE
            (le_top (a := LocallyRingedSpace.IsOpenImmersion.opensRange m))).op).hom s)) =
      (m.c.app (op (⊤ : Opens (FormalSpectrum I)))).hom s := by
  have h1 : (m.c.app (op (LocallyRingedSpace.IsOpenImmersion.opensRange m))).hom
      (((structureSheaf I).presheaf.map (homOfLE
        (le_top (a := LocallyRingedSpace.IsOpenImmersion.opensRange m))).op).hom s) =
      ((structureSheaf J).presheaf.map ((Opens.map m.base).map (homOfLE
        (le_top (a := LocallyRingedSpace.IsOpenImmersion.opensRange m)))).op).hom
          ((m.c.app (op (⊤ : Opens (FormalSpectrum I)))).hom s) := by
    have h := ConcreteCategory.congr_hom (m.c.naturality (homOfLE
      (le_top (a := LocallyRingedSpace.IsOpenImmersion.opensRange m))).op) s
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
    exact h
  rw [h1]
  have hid : (structureSheaf J).presheaf.map ((Opens.map m.base).map (homOfLE
        (le_top (a := LocallyRingedSpace.IsOpenImmersion.opensRange m)))).op ≫
      (structureSheaf J).presheaf.map (homOfLE (top_le_map_opensRange I J m)).op =
      𝟙 ((structureSheaf J).presheaf.obj (op (⊤ : Opens (FormalSpectrum J)))) := by
    rw [← Functor.map_comp]
    exact (congrArg (structureSheaf J).presheaf.map (Subsingleton.elim _ (𝟙 _))).trans
      ((structureSheaf J).presheaf.map_id _)
  have h2 : ((structureSheaf J).presheaf.map (homOfLE (top_le_map_opensRange I J m)).op).hom
      (((structureSheaf J).presheaf.map ((Opens.map m.base).map (homOfLE
        (le_top (a := LocallyRingedSpace.IsOpenImmersion.opensRange m)))).op).hom
          ((m.c.app (op (⊤ : Opens (FormalSpectrum I)))).hom s)) =
      (m.c.app (op (⊤ : Opens (FormalSpectrum I)))).hom s := by
    have h := ConcreteCategory.congr_hom hid
      ((m.c.app (op (⊤ : Opens (FormalSpectrum I)))).hom s)
    rw [ConcreteCategory.comp_apply] at h
    exact h
  exact h2

/-- **The identification carries the structural map of the sections ring to the algebra map.**
This is what makes `FormalSpectrum.sectionsOpenIdeal` at the range correspond to `I · B`. -/
theorem rangeSectionsHom_sectionsOpenHom (r : R) :
    rangeSectionsHom I J m
        (sectionsOpenHom I (LocallyRingedSpace.IsOpenImmersion.opensRange m) r) =
      globalSectionsMap I J m r := by
  rw [globalSectionsMap_apply, rangeSectionsHom, sectionsOpenHom]
  simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_coe]
  congr 1
  exact res_c_app_opensRange I J m ((globalSectionsEquiv I).symm r)

section Algebra

variable [Algebra R B]

/-- **The openness half of adicity**, over an open immersion whose range has affine thickenings. -/
theorem le_radical_map_of_hasAffineThickenings
    (halg : algebraMap R B = globalSectionsMap I J m) (hI : I.FG)
    (hU : HasAffineThickenings I (LocallyRingedSpace.IsOpenImmersion.opensRange m)) :
    J ≤ (I.map (algebraMap R B)).radical := by
  rw [le_radical_map_iff_forall_mem_range I J]
  intro q hq
  haveI : (Ideal.comap (rangeSectionsHom I J m) q.asIdeal).IsPrime :=
    Ideal.IsPrime.comap _
  set p : PrimeSpectrum ((structureSheaf I).presheaf.obj
      (op (LocallyRingedSpace.IsOpenImmersion.opensRange m)) : Type u) :=
    ⟨Ideal.comap (rangeSectionsHom I J m) q.asIdeal, inferInstance⟩ with hpdef
  have hker : RingHom.ker
      (sectionsPi I 0 (LocallyRingedSpace.IsOpenImmersion.opensRange m)).hom ≤ p.asIdeal := by
    rw [ker_sectionsPi_zero_eq_sectionsOpenIdeal I hU hI, sectionsOpenIdeal, hpdef]
    refine Ideal.map_le_iff_le_comap.mpr fun r hr => ?_
    change rangeSectionsHom I J m (sectionsOpenHom I _ r) ∈ q.asIdeal
    rw [rangeSectionsHom_sectionsOpenHom, ← halg]
    exact hq (Ideal.mem_map_of_mem _ hr)
  obtain ⟨y, hy, hp⟩ :=
    exists_mem_eq_sectionsPrime (hU 0) (surjective_sectionsPi_zero hU) p hker
  obtain ⟨z, hz⟩ : ∃ z : FormalSpectrum J, m.base z = y := hy
  subst hz
  refine ⟨z, PrimeSpectrum.ext ?_⟩
  refine Ideal.comap_injective_of_surjective (rangeSectionsHom I J m)
    (surjective_rangeSectionsHom I J m) ?_
  rw [comap_rangeSectionsHom_toPrimeSpectrum]
  exact (congrArg PrimeSpectrum.asIdeal hp).symm

/-- **The openness half over an open immersion that is onto, with no affineness hypothesis.**
`FormalSpectrum.hasAffineThickenings_top` is unconditional, so when the range of `m` is everything
the hypothesis of `FormalSpectrum.le_radical_map_of_hasAffineThickenings` discharges itself.

**Now a special case** of `FormalSpectrum.le_radical_map_of_openImmersion`
(`FormalSchemes.AffineThickeningsOpenImmersion`), which does not use `hrange`. Kept because it is
upstream of that file and cannot cite it. -/
theorem le_radical_map_of_range_eq_univ
    (halg : algebraMap R B = globalSectionsMap I J m) (hI : I.FG)
    (hrange : Set.range m.base = Set.univ) :
    J ≤ (I.map (algebraMap R B)).radical := by
  refine le_radical_map_of_hasAffineThickenings I J m halg hI ?_
  have htop : LocallyRingedSpace.IsOpenImmersion.opensRange m = ⊤ :=
    Opens.ext (by rw [LocallyRingedSpace.IsOpenImmersion.coe_opensRange, hrange]; rfl)
  rw [htop]
  exact hasAffineThickenings_top I

/-- **The openness half over an open immersion whose range is that of a basic-open chart.**

This is `FormalSpectrum.isCofinal_map_of_range_eq_basicOpenChart`'s containment, reached by a
different route: that theorem transports the on-the-nose equality
`FormalSpectrum.map_algebraMap_awayCompletion` along presentation-independence, and this one runs
the sections argument of this file on the same open.

**Now a special case** of `FormalSpectrum.le_radical_map_of_openImmersion`
(`FormalSchemes.AffineThickeningsOpenImmersion`), which uses neither `f` nor `hrange`. Kept
because it is upstream of that file and cannot cite it. -/
theorem le_radical_map_of_range_eq_basicOpenChart
    (halg : algebraMap R B = globalSectionsMap I J m) (hI : I.FG) (f : R)
    (hrange : Set.range m.base = Set.range (basicOpenChart I f).base) :
    J ≤ (I.map (algebraMap R B)).radical :=
  le_radical_map_of_hasAffineThickenings I J m halg hI
    (hasAffineThickenings_opensRange_of_range_eq_basicOpenChart hI f m hrange)

/-- **`I · B` is an ideal of definition of `B`, up to cofinality**, over an open immersion whose
range has affine thickenings: the assembly of this file's openness half with the unconditional
nilpotence half `FormalSpectrum.map_le_radical_of_hom`, through
`FormalSpectrum.isCofinal_map_of_le_radical`. -/
theorem isCofinal_map_of_hasAffineThickenings (hI : I.FG) (hJ : J.FG)
    (halg : algebraMap R B = globalSectionsMap I J m)
    (hU : HasAffineThickenings I (LocallyRingedSpace.IsOpenImmersion.opensRange m)) :
    Ideal.IsCofinal J (I.map (algebraMap R B)) :=
  isCofinal_map_of_le_radical I J hI hJ m halg
    (le_radical_map_of_hasAffineThickenings I J m halg hI hU)


end Algebra

end Openness

section NonVacuity

variable (I)

/-!
### Non-vacuity
-/

/-- **Non-vacuity, through a genuinely non-reflexive instance.** The `Spf`-functoriality morphism
of `RingHom.id R` presents `Spf R` at `I` over its presentation at `I ^ 2`; it is an isomorphism
(`FormalSpectrum.isIso_locallyRingedSpaceMapId`) hence an open immersion that is onto, its action
on global sections is `RingHom.id R` (`FormalSpectrum.globalSectionsMap_locallyRingedSpaceMap`),
and the containment `FormalSpectrum.le_radical_map_of_range_eq_univ` returns for it is `I ≤ √(I ^
2)`. That is not reflexivity, and it is not closed by `rfl`.

The conclusion is of course independently provable, and that is the point: it is a check that the
machinery of this file returns the right answer on an instance whose answer is known by other
means, on a morphism that is not an identity and at a presentation that is not the one the
statement is about. -/
theorem le_radical_pow_of_range_eq_univ (hI : I.FG) : I ≤ (I ^ 2).radical := by
  have hle : I ^ 2 ≤ I := Ideal.pow_le_self two_ne_zero
  have hIsq : (I ^ 2).FG := hI.pow
  haveI : IsAdicRing (I ^ 2) := IsAdicRing.of_isCofinal (Ideal.IsCofinal.pow I two_ne_zero)
  set w := locallyRingedSpaceMap (I ^ 2) I (RingHom.id R) (le_comap_id_of_le (I ^ 2) I hle)
    with hw
  haveI : IsIso w := isIso_locallyRingedSpaceMapId (I ^ 2) I hle hIsq hI
  haveI : LocallyRingedSpace.IsOpenImmersion w := inferInstance
  have hrange : Set.range w.base = Set.univ :=
    Set.range_eq_univ.mpr fun y =>
      ⟨(asIso w).inv.base y, LocallyRingedSpace.iso_inv_base_hom_base_apply (asIso w) y⟩
  have halg : algebraMap R R = globalSectionsMap (I ^ 2) I w := by
    rw [hw, globalSectionsMap_locallyRingedSpaceMap, Algebra.algebraMap_self]
  have h := le_radical_map_of_range_eq_univ (I ^ 2) I w halg hIsq hrange
  rwa [Algebra.algebraMap_self, Ideal.map_id] at h

end NonVacuity

end FormalSpectrum

namespace AlgebraicGeometry

open FormalSpectrum

variable {R : Type u} [CommRing R] {I : Ideal R} [TopologicalSpace R] [IsAdicRing I]
variable {B : Type u} [CommRing B] [TopologicalSpace B] {J : Ideal B} [IsAdicRing J]
variable [Algebra R B]

/-- **Conservativity's affine step, over an open whose thickenings are affine.** An affine open of
`Spf I` presented by an open immersion whose range has affine thickenings is topologically of
finite type over `(R, I)`.

This is `AlgebraicGeometry.IsTopologicallyFiniteType.of_openImmersion_of_le_radical` with its
hypothesis discharged by `FormalSpectrum.le_radical_map_of_hasAffineThickenings`. -/
theorem IsTopologicallyFiniteType.of_openImmersion_of_hasAffineThickenings (hI : I.FG) (hJ : J.FG)
    (m : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    [LocallyRingedSpace.IsOpenImmersion m]
    (halg : algebraMap R B = globalSectionsMap I J m)
    (hU : HasAffineThickenings I (LocallyRingedSpace.IsOpenImmersion.opensRange m)) :
    IsTopologicallyFiniteType R I B (I.map (algebraMap R B)) :=
  IsTopologicallyFiniteType.of_openImmersion_of_le_radical hI hJ m halg
    (le_radical_map_of_hasAffineThickenings I J m halg hI hU)

/-- **Unconditionally, for an open immersion that is onto.**

**Now a special case** of `AlgebraicGeometry.IsTopologicallyFiniteType.of_openImmersion`
(`FormalSchemes.AffineThickeningsOpenImmersion`), which does not use `hrange`. Kept because it is
upstream of that file and cannot cite it. -/
theorem IsTopologicallyFiniteType.of_openImmersion_range_eq_univ (hI : I.FG) (hJ : J.FG)
    (m : locallyRingedSpaceObj J ⟶ locallyRingedSpaceObj I)
    [LocallyRingedSpace.IsOpenImmersion m]
    (halg : algebraMap R B = globalSectionsMap I J m)
    (hrange : Set.range m.base = Set.univ) :
    IsTopologicallyFiniteType R I B (I.map (algebraMap R B)) :=
  IsTopologicallyFiniteType.of_openImmersion_of_le_radical hI hJ m halg
    (le_radical_map_of_range_eq_univ I J m halg hI hrange)

end AlgebraicGeometry
