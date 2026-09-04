import FormalSchemes.AdicCompletionCongrLevel
import FormalSchemes.AssociatedGradedCompletion
import FormalSchemes.BasicOpenChart

set_option linter.style.header false

/-!
# The canonical `R{1/f} →+* R{1/g}` attached to an inclusion `D(g) ⊆ D(f)` of `Spf R`

For an inclusion of basic opens `D(g) ⊆ D(f)` of an *affine scheme* `Spec R` there is a ring map
`R_f → R_g`, because the inclusion says `g ∈ √(f)` and hence `f` becomes a unit in
`Localization.Away g`. In `Spf (R, I)` the corresponding statement is **false**:
`FormalSpectrum.basicOpen I f` is the basic open of the residue `f mod I` in `Spec (R ⧸ I)`, so
`D(g) ⊆ D(f)` says `ḡ ∈ √(f̄)` in `R ⧸ I`, and `f` need not become a unit in
`Localization.Away g` at all. `FormalSchemes.CofinalSheafComparisonNaturality` records that
obstruction in as many words, and it is the stated reason the basis-restriction naturality of that
file is settled only in the case `f = 1`.

The obstruction disappears after completing. `D(g) ⊆ D(f)` gives `g ^ n - f * a ∈ I` for some `n`
and `a`, so `f` becomes a unit in `R_g ⧸ I·R_g` — where `g` is already invertible — and therefore in
every thickening, and therefore in the completion `R{1/g}`, which is adically complete. So

```
R{1/f} →+* R{1/g}
```

does exist, canonically, and this file builds it as `FormalSpectrum.awayCompletionRestrict`. The
construction is the one `RingSplit.adicAwayUnitEquiv'` (`FormalSchemes.AdicCompletionCongrLevel`)
was written for: localizing at an element that is already invertible modulo the ideal of definition
does not change the completion, so `R{1/g}` *is* the completion of `(R_g)_f`, and `R_f → (R_g)_f`
is an ordinary localization lift.

## Main results

* `FormalSpectrum.isUnit_mk_algebraMap_of_basicOpen_le`: **the crux, and it needs no
  `Ideal.FG`** — for `D(g) ≤ D(f)`, the image of `f` is a unit in `R_g ⧸ I·R_g`.
* `FormalSpectrum.isUnit_awayCompletionHom_of_basicOpen_le`: **`f` is invertible on `D(g)`** — for
  `I` finitely generated, `FormalSpectrum.awayCompletionHom I g f` is a unit of `R{1/g}`. This is
  the geometric statement, and the one a reader wants to cite.
* `FormalSpectrum.awayCompletionRestrict`: the ring map `R{1/f} →+* R{1/g}` itself.
* `FormalSpectrum.awayCompletionRestrict_comp_awayCompletionHom` and its applied form: it commutes
  with the structure maps from `R`.
* `FormalSpectrum.map_awayCompletionRestrict`: it carries the ideal of definition of `R{1/f}`
  **onto** the ideal of definition of `R{1/g}` — an equality of images, not merely `≤`, which is
  what reading it as a morphism of adic rings needs; `le_comap_awayCompletionRestrict` is the
  contracted form that `FormalSpectrum.locallyRingedSpaceMap` consumes.

## What is *not* proved here

**No declaration in this file identifies `awayCompletionRestrict` with the structure-sheaf
restriction `Γ(D(f), O_{Spf R}) ⟶ Γ(D(g), O_{Spf R})`.** That restriction is a different object:
conjugated by `FormalSpectrum.sectionsBasicOpenEquiv` it is `FormalSpectrum.basicOpenRes`
(`FormalSchemes.BasicOpenRestriction`), and the identification
`basicOpenRes I hle = awayCompletionRestrict I f g hI hle` is exactly what two independent threads
on this tree are asking for and is **not** settled by anything below. The case `f = 1` is settled,
by `FormalSpectrum.awayCompletionHom_eq_restrict` (`FormalSchemes.SpfGammaSheafComponentArbComp`).
Do not read the title of this file as that identification.

What is available towards it: both maps satisfy the same locality-free square over `R`, by
`awayCompletionRestrict_comp_awayCompletionHom` here and by
`FormalSpectrum.basicOpenRes_comp_awayCompletionHom` there. **That is enough, and the
identification is landed downstream** as `FormalSpectrum.basicOpenRes_eq_awayCompletionRestrict`
(`FormalSchemes.BasicOpenRestrictionIdentification`), for `I` finitely generated. What an earlier
version of this paragraph missed is that a map under `R` carries the ideal of definition across for
free — the ideal of definition of `R{1/f}` *is* the extension of `I` along `awayCompletionHom I f`,
by `map_awayCompletionHom` — so the continuity hypothesis that the uniqueness statement needs is
not an extra property to be proved of the sheaf-side map at all
(`FormalSpectrum.map_eq_of_comp_awayCompletionHom`, same file). Nothing below states the
identification; it is stated where both maps are in scope.

**Uniqueness of the map is not proved below, and is not open.** Two ring maps `R{1/f} → R{1/g}`
agreeing on the image of `R` agree on the image of `Localization.Away f`, since the image of `f` is
invertible in the target; but that image is only *dense*, so uniqueness needs a continuity
hypothesis. **That hypothesis is `le_comap_awayCompletionRestrict`, which this file proves**, and
the extensionality principle that consumes it is `AdicCompletion.hom_ext_of_continuous`
(`FormalSchemes.AdicExtend`). `FormalSpectrum.awayCompletion_hom_ext` and
`FormalSpectrum.awayCompletionRestrict_unique` (`FormalSchemes.AwayCompletionRestrictUnique`) put
the two together: `awayCompletionRestrict` is the unique ring map that carries the ideal of
definition across and restricts to `awayCompletionHom I g` on the image of `R`. Nothing *below* is
a uniqueness statement; that file's are.

**Transitivity** along `D(h) ⊆ D(g) ⊆ D(f)` is likewise not proved below. It does not need the
direct computation through two `RingSplit.adicAwayUnitEquiv'`s that an earlier version of this
paragraph proposed: `FormalSpectrum.awayCompletionRestrict_comp` gets it from uniqueness, together
with `awayCompletionRestrict_self` and the identification of every completed localization map under
`R` with this one.

## Implementation notes

`FormalSpectrum.awayAway f g` is `(R_g)_f`, the localization of `Localization.Away g` at the image
of `f`. It is where the two localizations meet: `RingSplit.adicAwayUnitEquiv'` presents `R{1/g}` as
its `I`-adic completion, and `FormalSpectrum.awayAwayLift` is the localization lift
`R_f → (R_g)_f` that `AdicCompletion.mapCompletion` is applied to. The `Ideal.FG` hypothesis enters
only through `AdicCompletion.mapCompletion`, whose target must be complete; the crux
`isUnit_mk_algebraMap_of_basicOpen_le` is free of it, which is why it is stated separately.

The bridge between `AdicCompletion.of` and `algebraMap` that the structure-map compatibility proof
needs is `AssociatedGraded.algebraMap_eq_of` (`FormalSchemes.AssociatedGradedCompletion`); it is
cited rather than re-proved, at a cost of two modules in the import closure.

The inclusion is spelled `basicOpen I g ≤ basicOpen I f`, matching
`FormalSpectrum.basicOpenRes`. It is **strictly weaker** than the scheme-theoretic hypothesis
`IsUnit ((algebraMap R (Localization.Away g)) f)` that `FormalSpectrum.awayCompletionAwayEquiv`
(`FormalSchemes.AwayCompletionAway`) takes, so that equivalence is not a substitute for the map
built here.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1 (10.1.4), §10.3.
* [The Stacks Project, Tag 0AI7](https://stacks.math.columbia.edu/tag/0AI7)
-/

noncomputable section

open TopologicalSpace

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (I : Ideal R) (f g : R)

/-!
### `D(g) ⊆ D(f)` makes `f` invertible on `D(g)`
-/

/-- **An inclusion of basic opens of `Spf R` is a congruence, not a divisibility.** `D(g) ≤ D(f)`
says `ḡ ∈ √(f̄)` in `R ⧸ I`, i.e. `g ^ n - f * a ∈ I` for some `n` and `a` — and *not* that `g`
lies in the radical of `f` in `R`. -/
theorem exists_pow_sub_mul_mem_of_basicOpen_le (hle : basicOpen I g ≤ basicOpen I f) :
    ∃ (n : ℕ) (a : R), g ^ n - f * a ∈ I := by
  have h : (PrimeSpectrum.basicOpen (Ideal.Quotient.mk I g) :
      Opens (PrimeSpectrum (R ⧸ I))) ≤ PrimeSpectrum.basicOpen (Ideal.Quotient.mk I f) := hle
  rw [PrimeSpectrum.basicOpen_le_basicOpen_iff] at h
  obtain ⟨n, hn⟩ := h
  rw [Ideal.mem_span_singleton] at hn
  obtain ⟨b, hb⟩ := hn
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact ⟨n, a, by rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_mul, hb, sub_self]⟩

/-- **The crux, and it carries no finiteness hypothesis.** For `D(g) ≤ D(f)` the image of `f` is a
unit in the residue ring `R_g ⧸ I·R_g`: the image of `g` is a unit there, and `g ^ n = f * a`
modulo `I`. This is where the inclusion of basic opens is spent; everything below is completion
bookkeeping. -/
theorem isUnit_mk_algebraMap_of_basicOpen_le (hle : basicOpen I g ≤ basicOpen I f) :
    IsUnit (Ideal.Quotient.mk (I.map (algebraMap R (Localization.Away g)))
      (algebraMap R (Localization.Away g) f)) := by
  obtain ⟨n, a, hna⟩ := exists_pow_sub_mul_mem_of_basicOpen_le I f g hle
  set K := I.map (algebraMap R (Localization.Away g)) with hK
  have hzero : Ideal.Quotient.mk K (algebraMap R (Localization.Away g) (g ^ n - f * a)) = 0 := by
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hna
  have hgu : IsUnit (Ideal.Quotient.mk K (algebraMap R (Localization.Away g) g)) :=
    (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away g) g).map _
  have key : (Ideal.Quotient.mk K (algebraMap R (Localization.Away g) g)) ^ n =
      Ideal.Quotient.mk K (algebraMap R (Localization.Away g) f) *
        Ideal.Quotient.mk K (algebraMap R (Localization.Away g) a) := by
    simp only [map_sub, map_pow, map_mul, sub_eq_zero] at hzero
    exact hzero
  exact isUnit_of_mul_isUnit_left (key ▸ hgu.pow n)

/-- **`f` is invertible on `D(g)`.** For `I` finitely generated and `D(g) ≤ D(f)`, the structural
image of `f` in `R{1/g}` is a unit: it is a unit modulo the ideal of definition by
`FormalSpectrum.isUnit_mk_algebraMap_of_basicOpen_le`, the ideal of definition of a complete adic
ring lies in the Jacobson radical (`IsAdicComplete.le_jacobson_bot`), and units lift along it. -/
theorem isUnit_awayCompletionHom_of_basicOpen_le (hI : I.FG)
    (hle : basicOpen I g ≤ basicOpen I f) : IsUnit (awayCompletionHom I g f) := by
  haveI : IsAdicComplete (awayCompletionIdeal I g) (awayCompletion I g) :=
    (AdicCompletion.isAdicRing_map _ (hI.map _)).toIsAdicComplete
  obtain ⟨u, hu⟩ := isUnit_mk_algebraMap_of_basicOpen_le I f g hle
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective ((u⁻¹ : (Localization.Away g ⧸
    I.map (algebraMap R (Localization.Away g)))ˣ) : Localization.Away g ⧸
      I.map (algebraMap R (Localization.Away g)))
  have hsub : algebraMap R (Localization.Away g) f * w - 1 ∈
      I.map (algebraMap R (Localization.Away g)) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_one, hw, ← hu, u.mul_inv, sub_self]
  have hmem : awayCompletionHom I g f *
      algebraMap (Localization.Away g) (awayCompletion I g) w - 1 ∈ awayCompletionIdeal I g := by
    rw [show awayCompletionHom I g f *
        algebraMap (Localization.Away g) (awayCompletion I g) w - 1 =
        algebraMap (Localization.Away g) (awayCompletion I g)
          (algebraMap R (Localization.Away g) f * w - 1) by rw [map_sub, map_mul, map_one]; rfl]
    exact Ideal.mem_map_of_mem _ hsub
  exact isUnit_of_mul_isUnit_left (Ideal.isUnit_of_sub_one_mem_jacobson_bot _
    (IsAdicComplete.le_jacobson_bot (awayCompletionIdeal I g) hmem))

/-!
### The intermediate localization `(R_g)_f`, and the map
-/

/-- **`(R_g)_f`**, the localization of `Localization.Away g` at the image of `f`. Both
localizations of `R` map to it, and `RingSplit.adicAwayUnitEquiv'` presents `R{1/g}` as its
`I`-adic completion once `f` is a unit modulo `I·R_g`. -/
abbrev awayAway : Type u := Localization.Away ((algebraMap R (Localization.Away g)) f)

/-- The structural map `R → (R_g)_f`, the composite of the two localization maps. -/
def awayAwayHom : R →+* awayAway f g :=
  (algebraMap (Localization.Away g) (awayAway f g)).comp (algebraMap R (Localization.Away g))

/-- `f` is a unit in `(R_g)_f` by construction — it is what that ring is obtained by inverting.
No hypothesis on `f` and `g` is involved. -/
theorem isUnit_awayAwayHom : IsUnit (awayAwayHom f g f) :=
  IsLocalization.Away.algebraMap_isUnit (S := awayAway f g)
    ((algebraMap R (Localization.Away g)) f)

/-- **The localization lift `R_f →+* (R_g)_f`**, the universal property of `Localization.Away f`
applied to `FormalSpectrum.isUnit_awayAwayHom`. -/
def awayAwayLift : Localization.Away f →+* awayAway f g :=
  IsLocalization.Away.lift (S := Localization.Away f) f (isUnit_awayAwayHom f g)

theorem awayAwayLift_comp :
    (awayAwayLift f g).comp (algebraMap R (Localization.Away f)) = awayAwayHom f g :=
  IsLocalization.Away.lift_comp _ _

/-- The lift carries `I·R_f` **onto** `I·(R_g)_f`: both sides are the extension of `I` along the
structural map `R → (R_g)_f`. -/
theorem map_awayAwayLift :
    (I.map (algebraMap R (Localization.Away f))).map (awayAwayLift f g) =
      RingSplit.awayUnitIdeal (I.map (algebraMap R (Localization.Away g)))
        ((algebraMap R (Localization.Away g)) f) := by
  rw [Ideal.map_map, awayAwayLift_comp, RingSplit.awayUnitIdeal, Ideal.map_map]
  rfl

/-- **The canonical `R{1/f} →+* R{1/g}` attached to `D(g) ⊆ D(f)`.** Complete the localization lift
`FormalSpectrum.awayAwayLift` to get `R{1/f} →+* (R_g)_f^`, then come back along
`RingSplit.adicAwayUnitEquiv'`, which identifies `(R_g)_f^` with `R{1/g}` because `f` is already a
unit modulo `I·R_g` (`FormalSpectrum.isUnit_mk_algebraMap_of_basicOpen_le`).

There is no ring map `R_f → R_g` underlying this — that is the point, and
`FormalSchemes.CofinalSheafComparisonNaturality` says so. `Ideal.FG` enters only through
`AdicCompletion.mapCompletion`, whose target has to be complete. -/
def awayCompletionRestrict (hI : I.FG) (hle : basicOpen I g ≤ basicOpen I f) :
    awayCompletion I f →+* awayCompletion I g :=
  (RingSplit.adicAwayUnitEquiv' (I.map (algebraMap R (Localization.Away g)))
        ((algebraMap R (Localization.Away g)) f)
        (isUnit_mk_algebraMap_of_basicOpen_le I f g hle)).symm.toRingHom.comp
    (AdicCompletion.mapCompletion (awayAwayLift f g) (map_awayAwayLift I f g).le ((hI.map _).map _))

/-- **The map is a map under `R`**: composed with the structural map `R → R{1/f}` it is the
structural map `R → R{1/g}`. Both legs send `r` to the class of its image in `(R_g)_f`, one through
`FormalSpectrum.awayAwayLift` and one through `RingSplit.adicAwayUnitEquiv'_of`. -/
theorem awayCompletionRestrict_comp_awayCompletionHom (hI : I.FG)
    (hle : basicOpen I g ≤ basicOpen I f) :
    (awayCompletionRestrict I f g hI hle).comp (awayCompletionHom I f) = awayCompletionHom I g := by
  refine RingHom.ext fun r => ?_
  rw [RingHom.comp_apply, awayCompletionRestrict, RingHom.comp_apply,
    show awayCompletionHom I f r =
      algebraMap (Localization.Away f) (awayCompletion I f)
        (algebraMap R (Localization.Away f) r) from rfl,
    AdicCompletion.mapCompletion_algebraMap, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.symm_apply_eq]
  have hlift : awayAwayLift f g (algebraMap R (Localization.Away f) r) = awayAwayHom f g r :=
    RingHom.congr_fun (awayAwayLift_comp f g) r
  rw [hlift, AssociatedGraded.algebraMap_eq_of,
    show awayCompletionHom I g r =
      AdicCompletion.of (I.map (algebraMap R (Localization.Away g))) (Localization.Away g)
        (algebraMap R (Localization.Away g) r) from AssociatedGraded.algebraMap_eq_of _ _,
    RingSplit.adicAwayUnitEquiv'_of]
  rfl

/-- The applied form of `FormalSpectrum.awayCompletionRestrict_comp_awayCompletionHom`. -/
theorem awayCompletionRestrict_awayCompletionHom (hI : I.FG)
    (hle : basicOpen I g ≤ basicOpen I f) (r : R) :
    awayCompletionRestrict I f g hI hle (awayCompletionHom I f r) = awayCompletionHom I g r :=
  RingHom.congr_fun (awayCompletionRestrict_comp_awayCompletionHom I f g hI hle) r

/-- **The map is a map of adic rings, on the nose**: it carries the ideal of definition of `R{1/f}`
*onto* that of `R{1/g}`, not merely into it. Each is the extension of `I` along the structural map
(`FormalSpectrum.map_awayCompletionHom`), and the map commutes with those. -/
theorem map_awayCompletionRestrict (hI : I.FG) (hle : basicOpen I g ≤ basicOpen I f) :
    (awayCompletionIdeal I f).map (awayCompletionRestrict I f g hI hle) =
      awayCompletionIdeal I g := by
  rw [← map_awayCompletionHom I f, Ideal.map_map,
    awayCompletionRestrict_comp_awayCompletionHom, map_awayCompletionHom]

/-- The contracted form of `FormalSpectrum.map_awayCompletionRestrict`: the continuity obligation
that `FormalSpectrum.locallyRingedSpaceMap` consumes. -/
theorem le_comap_awayCompletionRestrict (hI : I.FG) (hle : basicOpen I g ≤ basicOpen I f) :
    awayCompletionIdeal I f ≤
      (awayCompletionIdeal I g).comap (awayCompletionRestrict I f g hI hle) :=
  Ideal.map_le_iff_le_comap.mp (map_awayCompletionRestrict I f g hI hle).le

end FormalSpectrum
