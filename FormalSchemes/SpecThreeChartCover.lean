import FormalSchemes.ChartedSchemeDatumAlgebraData

set_option linter.style.header false

/-!
# The three-chart affine open cover, as a `ChartedSchemeDatum` (EGA I, 10.8)

Fix a commutative ring `A`, an ideal `I ⊆ A` and three elements `f₀, f₁, f₂ : A`. This file
assembles the `Spec`-side open-cover datum: `Spec A` presented by the three basic opens `D(f_i)`,
with chart rings `C i := A_{f_i}`, overlap elements `g i j := ` the image of `f_j` in `A_{f_i}`,
and per-chart ideals `K i := I·A_{f_i}`.

It is the `Spec`-side twin of `AlgebraicGeometry.ThreeChartCover.datumX`
(`FormalSchemes.ThreeChartCoverDatum`), and it exists for the reason that one does: it is the
**first datum on this line whose triple-overlap fields are not vacuous.**
`AlgebraicGeometry.ChartedSchemeDatum.ofTwoPatch` is on `ULift Bool`, where no triple of indices
is pairwise distinct, so its `t'`, `t_fac` and `cocycle` are `False.elim`; a construction none of
whose instances exercises its own gluing has not been tested, and this development has already been
through one round of exactly that (`AlgebraicGeometry.oneChartExposeXDatum` on `ULift Unit`).
`datum_t'_zero_one_two` below is the statement that closes that gap: at the inhabited triple
`0, 1, 2` the field is the derived transition, by `rfl`.

## Everything is a localization of `A`, and that is the whole proof strategy

Each of the rings occurring here — `A_{f_i}`, its overlap `(A_{f_i})_{g_ij}`, its double overlap
`(A_{f_i})_{g_ij·g_ik}` — is a localization of `A` itself:

* `(A_{f_i})_{g_ij}` is `A` away from `f_i · f_j`, by Mathlib's
  `IsLocalization.Away.mul'` (available as an instance);
* `(A_{f_i})_{g_ij·g_ik}` is `A` away from `f_i · (f_j · f_k)`, by the same instance after
  `overlapElt_mul` rewrites the product of the two overlap elements as the image of `f_j · f_k`.

So all the transitions are the *unique* `A`-algebra isomorphisms between two localizations of `A`
at the same submonoid (`awayComparisonAlg`), and **every one of the datum's laws is uniqueness**:
two ring maps out of a localization of `A` that both commute with the structure map from `A` are
equal (`ringHom_ext_of_away`). No computation with fractions occurs anywhere in this file.

That is why the `Spec` side is short where the completion side is not. On the completion side the
analogous transitions are maps of *completions*, whose `A`-algebra structure does not determine
them, and `FormalSchemes.ThreeChartCoverTransitions` has to build them by hand from the nested
chart identification of `FormalSchemes.AwayCompletionNestedNaturality`.

## Main definitions and results

* `AlgebraicGeometry.SpecThreeChartCover.chartRing`, `overlapElt`: the charts and their overlaps.
* `AlgebraicGeometry.SpecThreeChartCover.tauAlg`, `sigmaAlg`: the single- and double-overlap
  transitions, as `A`-algebra isomorphisms.
* `AlgebraicGeometry.SpecThreeChartCover.datum`: the `ChartedSchemeDatum`, and
  `glued` its glued locally ringed space.
* `AlgebraicGeometry.SpecThreeChartCover.datum_t'_eq` and `datum_t'_zero_one_two`: non-vacuity of
  the triple-overlap field, in general and at the inhabited triple `0, 1, 2`.
* `AlgebraicGeometry.SpecThreeChartCover.intCover` and `intCover_overlap_nonempty`: `Spec ℤ`
  covered by `D(2)`, `D(3)`, `D(5)`, with the double overlap the triple `0, 1, 2` transports shown
  non-empty — so the non-vacuity above is not a statement about empty spaces.

## `glued ≅ Spec A` is proved, one file on

**`AlgebraicGeometry.SpecThreeChartCover.gluedIsoSpec`
(`FormalSchemes.SpecThreeChartCoverToSpec`) identifies `glued` with `Spec A`** whenever
`Ideal.span (Set.range f) = ⊤`, and `gluedIsoSpec_intCover` exhibits that at `Spec ℤ` covered by
`D(2)`, `D(3)`, `D(5)`. It is the `Spec`-side twin of
`AlgebraicGeometry.ThreeChartCover.gluedXIsoSpf` (`FormalSchemes.ThreeChartCoverOpenImmersion`).

The three ingredients are the ones that file supplies: the descent of the chart inclusions
`Spec A_{f_i} ⟶ Spec A` through the colimit (`AlgebraicGeometry.SpecThreeChartCover.toSpec`, via
the datum's universal property `AlgebraicGeometry.ChartedSchemeDatum.desc` in
`FormalSchemes.ChartedSchemeDatumDesc`), `isOpenImmersion_toSpec`, and surjectivity from the span
condition. **So it does follow from the datum** — it is not extra structure, only extra work.
Nothing of it is *here*, which is why this file stops at `glued`.

## What is *not* proved

* Nothing here is stated at `AlgebraicGeometry.Scheme`; see the scope note in
  `FormalSchemes.SpecAwayOverlap`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7, §10.8.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

namespace SpecThreeChartCover

variable {A : Type u} [CommRing A] (I : Ideal A) (f : ULift.{u} (Fin 3) → A)

/-! ### Two general facts about localizations of `A` -/

section General

/-- **A localization away from an element that is the image of one downstairs.** If `S` is `A` away
from `x` and `s : S` is the image of `y : A`, then `S` away from `s` is `A` away from `x · y`. This
is Mathlib's `IsLocalization.Away.mul'` instance, transported along the equation `s = y`; the
transport is needed because the away elements of interest here are *products* `g_ij · g_ik`, equal
to but not syntactically the image of `f_j · f_k`. -/
theorem isLocalization_away_of_eq {S : Type u} [CommRing S] [Algebra A S] (x y : A) {s : S}
    [IsLocalization.Away x S] (hs : s = algebraMap A S y) :
    IsLocalization.Away (x * y) (Localization.Away s) := by
  subst hs
  infer_instance

/-- **The comparison isomorphism of two localizations of `A` at the same element**, up to an
equality of away elements. Both `S` and `T` are `A` away from `x = y`, so
`IsLocalization.algEquiv` identifies them, uniquely among `A`-algebra maps. -/
def awayComparisonAlg {S T : Type u} [CommRing S] [CommRing T] [Algebra A S] [Algebra A T]
    (x y : A) (h : x = y) [IsLocalization.Away x S] [IsLocalization.Away y T] : S ≃ₐ[A] T := by
  subst h
  exact IsLocalization.algEquiv (Submonoid.powers x) S T

/-- **Two ring maps out of a localization of `A` agree if both are maps under `A`.** This is
`IsLocalization.ringHom_ext`, and it is the only tool the laws of this file's datum need. -/
theorem ringHom_ext_of_away {S T : Type u} [CommRing S] [CommRing T] [Algebra A S] [Algebra A T]
    (x : A) [IsLocalization.Away x S] {φ ψ : S →+* T}
    (hφ : ∀ a : A, φ (algebraMap A S a) = algebraMap A T a)
    (hψ : ∀ a : A, ψ (algebraMap A S a) = algebraMap A T a) : φ = ψ :=
  IsLocalization.ringHom_ext (Submonoid.powers x)
    (RingHom.ext fun a => (hφ a).trans (hψ a).symm)

/-- **The left further localization is a map under the base ring `A`**, not merely under `S`.
Mathlib's `IsLocalization.Away.awayToAwayRight_eq` is the statement one level down, over `S`; this
is the version two levels down, over the base ring, and it is what the laws below consume. -/
theorem awayToAwayRight_algebraMap {S : Type u} [CommRing S] [Algebra A S] (u v : S) (a : A) :
    IsLocalization.Away.awayToAwayRight u v (algebraMap A (Localization.Away u) a) =
      algebraMap A (Localization.Away (u * v)) a := by
  rw [IsScalarTower.algebraMap_apply A S (Localization.Away u),
    IsScalarTower.algebraMap_apply A S (Localization.Away (u * v))]
  exact IsLocalization.Away.awayToAwayRight_eq u v _

/-- **The right further localization is a map under the base ring `A`.** The mirror of
`awayToAwayRight_algebraMap`, over `IsLocalization.Away.awayToAwayLeft`. -/
theorem awayToAwayLeft_algebraMap {S : Type u} [CommRing S] [Algebra A S] (u v : S) (a : A) :
    IsLocalization.Away.awayToAwayLeft v u (algebraMap A (Localization.Away v) a) =
      algebraMap A (Localization.Away (u * v)) a := by
  rw [IsScalarTower.algebraMap_apply A S (Localization.Away v),
    IsScalarTower.algebraMap_apply A S (Localization.Away (u * v))]
  exact IsLocalization.Away.awayToAwayLeft_eq v u _

end General

/-! ### The charts and their overlaps -/

/-- **The `i`-th chart ring** `A_{f_i}`: the sections of `O_{Spec A}` over the basic open `D(f_i)`.
-/
abbrev chartRing (i : ULift.{u} (Fin 3)) : Type u := Localization.Away (f i)

/-- **The overlap element** `g i j : A_{f_i}`, the image of `f_j`. It cuts out
`D(f_i) ∩ D(f_j)` inside the chart `Spec A_{f_i}`. Unlike the completion-side
`AlgebraicGeometry.ThreeChartCover.overlapElt`, which is the image of `f_i · f_j`, this is the
image of `f_j` alone — the two cut out the same basic open, and this spelling is the one Mathlib's
`IsLocalization.Away.mul'` instance fires on with no transport. -/
abbrev overlapElt (i j : ULift.{u} (Fin 3)) : chartRing f i :=
  algebraMap A (chartRing f i) (f j)

/-- The product of two overlap elements of the same chart is the image of the product downstairs.
-/
theorem overlapElt_mul (i j k : ULift.{u} (Fin 3)) :
    overlapElt f i j * overlapElt f i k = algebraMap A (chartRing f i) (f j * f k) :=
  (map_mul _ _ _).symm

/-- **The double overlap of the `i`-th chart is `A` away from `f_i · (f_j · f_k)`.** -/
instance instIsLocalizationDouble (i j k : ULift.{u} (Fin 3)) :
    IsLocalization.Away (f i * (f j * f k))
      (Localization.Away (overlapElt f i j * overlapElt f i k)) :=
  isLocalization_away_of_eq (f i) (f j * f k) (overlapElt_mul f i j k)

/-! ### The transitions -/

/-- **The single-overlap transition** `(A_{f_i})_{g_ij} ≃ₐ[A] (A_{f_j})_{g_ji}`: both sides are `A`
away from `f_i · f_j`, up to `mul_comm`. -/
def tauAlg (i j : ULift.{u} (Fin 3)) :
    Localization.Away (overlapElt f i j) ≃ₐ[A] Localization.Away (overlapElt f j i) :=
  awayComparisonAlg (f i * f j) (f j * f i) (mul_comm _ _)

/-- **The double-overlap transition** `(A_{f_i})_{g_ij·g_ik} ≃ₐ[A] (A_{f_j})_{g_jk·g_ji}`: both
sides are `A` away from `f_i · f_j · f_k`, up to associativity and commutativity. -/
def sigmaAlg (i j k : ULift.{u} (Fin 3)) :
    Localization.Away (overlapElt f i j * overlapElt f i k) ≃ₐ[A]
      Localization.Away (overlapElt f j k * overlapElt f j i) :=
  awayComparisonAlg (f i * (f j * f k)) (f j * (f k * f i)) (by ring)

/-! ### The laws -/

/-- `τ_ji` is the inverse of `τ_ij`: both are `A`-algebra maps out of a localization of `A`. -/
theorem tauAlg_symm (i j : ULift.{u} (Fin 3)) :
    (tauAlg f j i).toRingEquiv = ((tauAlg f i j).toRingEquiv).symm :=
  RingEquiv.ext fun x => RingHom.congr_fun
    (ringHom_ext_of_away (f j * f i)
      (φ := (tauAlg f j i).toRingEquiv.toRingHom)
      (ψ := ((tauAlg f i j).toRingEquiv).symm.toRingHom)
      (fun a => (tauAlg f j i).commutes a) (fun a => (tauAlg f i j).symm.commutes a)) x

/-- The single-overlap transition, composed down to `A`, is the structure map. -/
theorem tauAlg_comp_algebraMap (i j : ULift.{u} (Fin 3)) :
    ((tauAlg f i j).toRingEquiv.toRingHom.comp
          (algebraMap (chartRing f i) (Localization.Away (overlapElt f i j)))).comp
        (algebraMap A (chartRing f i)) =
      algebraMap A (Localization.Away (overlapElt f j i)) := by
  refine RingHom.ext fun a => ?_
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [← IsScalarTower.algebraMap_apply A (chartRing f i) (Localization.Away (overlapElt f i j))]
  exact (tauAlg f i j).commutes a

/-- **The ideal compatibility.** The transition carries `I·(A_{f_i})_{g_ij}` onto
`I·(A_{f_j})_{g_ji}`, because both are `I` extended along the structure map from `A` and the
transition is a map under `A`. -/
theorem tauAlg_map_ideal (i j : ULift.{u} (Fin 3)) :
    (((I.map (algebraMap A (chartRing f i))).map
          (algebraMap (chartRing f i) (Localization.Away (overlapElt f i j)))).map
        (tauAlg f i j).toRingEquiv.toRingHom) =
      (I.map (algebraMap A (chartRing f j))).map
        (algebraMap (chartRing f j) (Localization.Away (overlapElt f j i))) := by
  rw [Ideal.map_map, Ideal.map_map, tauAlg_comp_algebraMap, Ideal.map_map,
    ← IsScalarTower.algebraMap_eq]

/-- **The σ/τ compatibility**, the input of `ChartedSchemeDatum.specAlgDataT'_fac`. Both sides are
ring maps out of `(A_{f_j})_{g_ji}` — a localization of `A` — under `A`. -/
theorem sigmaAlg_tauAlg (i j k : ULift.{u} (Fin 3)) :
    (sigmaAlg f i j k).toRingEquiv.symm.toRingHom.comp
        (IsLocalization.Away.awayToAwayLeft (overlapElt f j i) (overlapElt f j k)) =
      (IsLocalization.Away.awayToAwayRight (overlapElt f i j) (overlapElt f i k)).comp
        (tauAlg f i j).toRingEquiv.symm.toRingHom :=
  ringHom_ext_of_away (f j * f i)
    (fun a => by
      simp only [RingHom.coe_comp, Function.comp_apply]
      rw [awayToAwayLeft_algebraMap]
      exact (sigmaAlg f i j k).symm.commutes a)
    (fun a => by
      simp only [RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
        RingEquiv.coe_toRingHom]
      rw [show (tauAlg f i j).toRingEquiv.symm (algebraMap A _ a) =
          algebraMap A (Localization.Away (overlapElt f i j)) a from
        (tauAlg f i j).symm.commutes a]
      exact awayToAwayRight_algebraMap _ _ a)

/-- **The σ cocycle.** Three double-overlap transitions around a distinct triple compose to the
identity, again by uniqueness of `A`-algebra maps out of a localization of `A`. -/
theorem sigmaAlg_cocycle (i j k : ULift.{u} (Fin 3)) :
    (sigmaAlg f i j k).toRingEquiv.trans
        (((sigmaAlg f j k i).toRingEquiv).trans ((sigmaAlg f k i j).toRingEquiv)) =
      RingEquiv.refl (Localization.Away (overlapElt f i j * overlapElt f i k)) :=
  RingEquiv.ext fun x => RingHom.congr_fun
    (ringHom_ext_of_away (f i * (f j * f k))
      (φ := ((sigmaAlg f i j k).toRingEquiv.trans
        (((sigmaAlg f j k i).toRingEquiv).trans ((sigmaAlg f k i j).toRingEquiv))).toRingHom)
      (ψ := (RingEquiv.refl (Localization.Away
        (overlapElt f i j * overlapElt f i k))).toRingHom)
      (fun a => by
        simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_ringHom_trans,
          RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom,
          AlgEquiv.coe_ringEquiv]
        rw [(sigmaAlg f i j k).commutes a, (sigmaAlg f j k i).commutes a,
          (sigmaAlg f k i j).commutes a])
      (fun _ => rfl)) x

/-! ### The datum -/

/-- **The three-chart affine open-cover datum.** `Spec A` presented by the three basic opens
`D(f_i)`, with chart rings `A_{f_i}`, per-chart ideals `I·A_{f_i}` and overlaps `D(f_i) ∩ D(f_j)`.
All three geometric triple-overlap fields are derived from `tauAlg` / `sigmaAlg` by
`ChartedSchemeDatum.ofAlgebraData` and are **not** vacuous — see `datum_t'_zero_one_two`. -/
def datum : ChartedSchemeDatum.{u} :=
  ChartedSchemeDatum.ofAlgebraData (chartRing f) (overlapElt f)
    (fun i => I.map (algebraMap A (chartRing f i)))
    (fun i j _ => (tauAlg f i j).toRingEquiv)
    (fun i j _ => tauAlg_symm f i j)
    (fun i j _ => tauAlg_map_ideal I f i j)
    (fun i j k _ _ _ => (sigmaAlg f i j k).toRingEquiv)
    (fun i j k _ _ _ => sigmaAlg_tauAlg f i j k)
    (fun i j k _ _ _ => sigmaAlg_cocycle f i j k)

/-- **The glued locally ringed space** `D(f₀) ∪ D(f₁) ∪ D(f₂)`, the three affine charts glued along
their overlaps. -/
def glued : LocallyRingedSpace.{u} :=
  (datum I f).specGlued

/-! ### Non-vacuity -/

/-! Distinct elements of `Fin 3` stay distinct after `ULift.up` because `ULift.up` is injective,
which is Mathlib's `ULift.up_injective` (`Mathlib.Data.ULift`); the triples below use
`ULift.up_injective.ne (by decide)`.

This file used to restate that fact privately, and justified doing so by an import jump: the
project's own restatement lived in `FormalSchemes.ThreeChartDatum`, behind the completion-side
chart cluster, and importing it would have taken this file's closure from 48 modules to 93. The
measurement was correct about the wrong alternative — the real alternative was never that
restatement but the upstream lemma, which is in the closure of every module on this tree and
costs no import at all. All three project restatements are gone. -/

/-- The index type of the datum is `ULift (Fin 3)`, on which triples of distinct indices exist. -/
theorem datum_J : (datum I f).J = ULift.{u} (Fin 3) := rfl

/-- **Non-vacuity of the triple-overlap field, in general.** At a pairwise distinct triple, `t'` is
the derived transition of `ChartedSchemeDatum.specAlgDataT'`, not `False.elim`. -/
theorem datum_t'_eq (i j k : ULift.{u} (Fin 3)) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (datum I f).t' i j k hij hik hjk =
      ChartedSchemeDatum.specAlgDataT' (chartRing f) (overlapElt f)
        (fun i j k _ _ _ => (sigmaAlg f i j k).toRingEquiv) i j k hij hik hjk :=
  rfl

/-- **Non-vacuity, at the inhabited triple `0, 1, 2`.** This is the statement the two-patch datum
cannot make: the triple exists, so the field is genuinely evaluated. -/
theorem datum_t'_zero_one_two :
    (datum I f).t' ⟨0⟩ ⟨1⟩ ⟨2⟩ (ULift.up_injective.ne (by decide))
        (ULift.up_injective.ne (by decide)) (ULift.up_injective.ne (by decide)) =
      ChartedSchemeDatum.specAlgDataT' (chartRing f) (overlapElt f)
        (fun i j k _ _ _ => (sigmaAlg f i j k).toRingEquiv) ⟨0⟩ ⟨1⟩ ⟨2⟩
        (ULift.up_injective.ne (by decide)) (ULift.up_injective.ne (by decide))
        (ULift.up_injective.ne (by decide)) :=
  rfl

/-! ### A worked instance: `Spec ℤ` covered by `D(2)`, `D(3)`, `D(5)` -/

/-- **Three elements of `ℤ` whose basic opens cover `Spec ℤ`**: `2`, `3` and `5` generate the unit
ideal. The datum of this file at these elements is a `ChartedSchemeDatum` on `ULift (Fin 3)` with
pairwise distinct indices and non-empty overlaps — see `intCover_overlap_nonempty`. -/
def intCover : ULift.{0} (Fin 3) → ℤ := ![2, 3, 5] ∘ ULift.down

/-- **The double overlap that `t'` transports at the triple `0, 1, 2` is not empty.** The source of
`datum_t'_zero_one_two`'s morphism is `pullback (specAwayMap g₀₁) (specAwayMap g₀₂)`, which
`AlgebraicGeometry.specAwayOverlapIso` identifies with `Spec` of `ℤ[1/2]` away from `3 · 5`; the
statement below is that identification's set-theoretic content, `D(3) ∩ D(5) ≠ ∅` inside
`Spec ℤ[1/2]`, via `AlgebraicGeometry.specAwayOverlap_nonempty_iff`.

Without it, "the triple `0, 1, 2` is inhabited" would still leave open whether the objects the
triple-overlap field maps between are empty, in which case every equation between morphisms of
them holds for want of points. They are not. -/
theorem intCover_overlap_nonempty :
    (Set.range (specAwayMap (overlapElt intCover ⟨0⟩ ⟨1⟩)).base ∩
      Set.range (specAwayMap (overlapElt intCover ⟨0⟩ ⟨2⟩)).base).Nonempty := by
  haveI : IsDomain (Localization.Away (intCover ⟨0⟩)) :=
    IsLocalization.Away.isDomain (x := intCover ⟨0⟩)
      (S := Localization.Away (intCover ⟨0⟩)) (by decide)
  have hinj : Function.Injective (algebraMap ℤ (Localization.Away (intCover ⟨0⟩))) :=
    IsLocalization.injective _
      (powers_le_nonZeroDivisors_of_noZeroDivisors (show intCover ⟨0⟩ ≠ 0 by decide))
  rw [specAwayOverlap_nonempty_iff, overlapElt_mul, isNilpotent_iff_eq_zero]
  intro h
  exact absurd (hinj (h.trans (map_zero _).symm)) (by decide)

end SpecThreeChartCover

end AlgebraicGeometry

end
