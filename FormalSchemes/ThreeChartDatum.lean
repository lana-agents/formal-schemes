import FormalSchemes.AwayCompletionCongrEquiv
import FormalSchemes.GeneralFibreProductExposeXAlgebraData

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The first genuinely three-chart affine-charted formal scheme

Every `AlgebraicGeometry.AffineChartedFibreDatum` / `AffineChartedFibreDatumX` built so far has
index type `ULift Bool`, where no triple of indices is pairwise distinct, so all six geometric
triple-overlap fields (`t'`, `t_fac`, `cocycle`, `xt'`, `xt_fac`, `xcocycle`) are discharged by
`False.elim` and the general glueing machinery of EGA I §10.7 has never been exercised on the case
it was built for. This file supplies the first datum on a three-element index type, with genuine
content in all six fields.

## The example

Fix an adic base `(R, I)` with `I` finitely generated, an `R`-algebra `A` which is adic for
`I·A`, and three elements `f₀, f₁, f₂ : A`. Take three copies of `Spf A` as charts and glue the
`i`-th to the `j`-th along the basic open `D(f_i·f_j)`, by the identity of `A`. Concretely, in the
language of `AffineChartedFibreDatum`:

* `J := ULift (Fin 3)`, `A i := A`, and `g i j := f i * f j` (note this is **symmetric**, which is
  what makes the two presentations `D(g i j) ⊆ Spf A_i` and `D(g j i) ⊆ Spf A_j` of the overlap
  identifiable);
* `τ i j : A{1/(f_i·f_j)} ≃ₐ[R] A{1/(f_j·f_i)}` is the comparison isomorphism of
  `FormalSchemes.AwayCompletionCongrEquiv` (the two elements differ by `mul_comm`, but the two
  completed localizations are *different types*, so this is not `rfl`);
* `σ i j k : A{1/(f_i f_j · f_i f_k)} ≃ₐ[R] A{1/(f_j f_k · f_j f_i)}` is again a comparison
  isomorphism: the two elements are `f_i²f_jf_k` and `f_j²f_if_k`, which divide each other's
  squares, so they cut out the same basic open `D(f_i f_j f_k)`.

Note the index order in the target of `σ`: the factors are `(j→k)·(j→i)`, *not* the mirror
`(j→i)·(j→k)` of the source. Getting this wrong makes `hσc` fail to typecheck, which is exactly the
convention this file validates.

## Why the compatibilities are free

`hστ` and `hσc` are equalities between composites of further localizations and comparison maps, and
all of these are completions of `A`-compatible localization maps. By the rigidity lemma
`CompletedTensorAwayInterchange.furtherLocAlgHom_eq_awayCongrHom` any two such composites with the
same source and target agree, so each obligation collapses to a chain of `awayCongrHom_comp`
rewrites. The only real work is exhibiting the divisibilities that produce the units.

## Main definitions and results

* `AlgebraicGeometry.ThreeChart.tau`, `AlgebraicGeometry.ThreeChart.sigma`: the algebra transition
  data, with their laws `tau_symm`, `sigma_tau` (the `hστ` of the smart constructors) and
  `sigma_cocycle` (the `hσc`).
* `AlgebraicGeometry.ThreeChart.datumX`: the `AffineChartedFibreDatumX` itself, and the glued
  objects `AlgebraicGeometry.ThreeChart.gluedX` (the formal scheme `X`) and
  `AlgebraicGeometry.ThreeChart.fibreProductX` (`X ×_{Spf R} Spf B`).
* `AlgebraicGeometry.ThreeChart.datumX_t'_eq`, `datumX_xt'_eq`, `datumX_xt'_zero_one_two`: the
  non-vacuity statements — at a pairwise distinct triple the geometric fields are the derived
  transitions `algDataT'` / `xAlgDataT'`, not `False.elim`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7, §10.15.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
open CompletedTensorAwayInterchange CompletedTensorProduct

universe u

namespace AlgebraicGeometry

namespace ThreeChart

variable {R : Type u} [CommRing R] {I : Ideal R} (hI : I.FG)
variable {A : Type u} [CommRing A] [Algebra R A]
variable (f : ULift.{u} (Fin 3) → A)

/-- **The single-overlap transition** `A{1/(f_i·f_j)} ≃ₐ[R] A{1/(f_j·f_i)}`: the two chart
presentations of the overlap `D(f_i·f_j)` of the `i`-th and `j`-th copies of `Spf A` are compared
by the canonical isomorphism, `f_i·f_j` and `f_j·f_i` being equal elements of `A` but indexing
different completed localizations. -/
def tau (i j : ULift.{u} (Fin 3)) :
    awayCompletion (I.map (algebraMap R A)) (f i * f j) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R A)) (f j * f i) :=
  awayCongrEquiv I _ _ hI
    (isUnit_algebraMap_away_of_dvd_pow 1 ⟨1, by rw [pow_one, mul_one, mul_comm]⟩)
    (isUnit_algebraMap_away_of_dvd_pow 1 ⟨1, by rw [pow_one, mul_one, mul_comm]⟩)

/-- **The double-overlap transition** `A{1/(f_i f_j · f_i f_k)} ≃ₐ[R] A{1/(f_j f_k · f_j f_i)}`,
comparing the two presentations of the triple overlap `D(f_i f_j f_k)`. The two away elements are
`f_i²f_jf_k` and `f_j²f_if_k`; neither divides the other, but each divides the square of the other,
which is what `isUnit_algebraMap_away_of_dvd_pow` consumes. -/
def sigma (i j k : ULift.{u} (Fin 3)) :
    awayCompletion (I.map (algebraMap R A)) (f i * f j * (f i * f k)) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R A)) (f j * f k * (f j * f i)) :=
  awayCongrEquiv I _ _ hI
    (isUnit_algebraMap_away_of_dvd_pow 2 ⟨f j ^ 3 * f k, by ring⟩)
    (isUnit_algebraMap_away_of_dvd_pow 2 ⟨f i ^ 3 * f k, by ring⟩)

/-- **The transitions are mutually inverse** (the `τ_symm` field): the comparison isomorphism in
the opposite direction is the inverse comparison isomorphism. -/
theorem tau_symm (i j : ULift.{u} (Fin 3)) : tau hI f j i = (tau hI f i j).symm := by
  rw [tau, tau, awayCongrEquiv_symm]

/-- **σ/τ restriction compatibility** (the `hστ` hypothesis of both smart constructors): restricting
the double-overlap transition `σ i j k` to the single overlap agrees with `τ i j`. Both sides are
completions of `A`-compatible localization maps `A_{f_j f_i} → A_{f_i f_j · f_i f_k}`, hence both
are the comparison map. -/
theorem sigma_tau (i j k : ULift.{u} (Fin 3)) :
    (sigma hI f i j k).symm.toAlgHom.comp (furtherLocSnd I (f j * f k) (f j * f i) hI) =
      (furtherLocFst I (f i * f j) (f i * f k) hI).comp (tau hI f i j).symm.toAlgHom := by
  rw [sigma, tau, awayCongrEquiv_symm_toAlgHom, awayCongrEquiv_symm_toAlgHom,
    furtherLocSnd_eq_awayCongrHom I (f j * f k) (f j * f i) hI
      (isUnit_algebraMap_away_of_dvd_pow 1 ⟨f j * f k, by ring⟩),
    furtherLocFst_eq_awayCongrHom I (f i * f j) (f i * f k) hI
      (isUnit_algebraMap_away_of_dvd_pow 1 ⟨f i * f k, by ring⟩),
    awayCongrHom_comp, awayCongrHom_comp]

/-- **The algebra triple cocycle** (the `hσc` hypothesis of both smart constructors): going round
the three double overlaps of a distinct triple returns the identity. Again both sides are
comparison maps `A{1/(f_i f_j · f_i f_k)} → A{1/(f_i f_j · f_i f_k)}`, and the only such map is the
identity. -/
theorem sigma_cocycle (i j k : ULift.{u} (Fin 3)) :
    (sigma hI f i j k).trans ((sigma hI f j k i).trans (sigma hI f k i j)) =
      AlgEquiv.refl (R := R)
        (A₁ := awayCompletion (I.map (algebraMap R A)) (f i * f j * (f i * f k))) := by
  have h : ((sigma hI f k i j).toAlgHom.comp
      ((sigma hI f j k i).toAlgHom.comp (sigma hI f i j k).toAlgHom)) =
      AlgHom.id R (awayCompletion (I.map (algebraMap R A)) (f i * f j * (f i * f k))) := by
    simp only [sigma, awayCongrEquiv_toAlgHom]
    rw [awayCongrHom_comp, awayCongrHom_comp, awayCongrHom_self]
  refine AlgEquiv.ext fun x => ?_
  simpa using AlgHom.congr_fun h x

section Datum

variable [TopologicalSpace A] [IsAdicRing (I.map (algebraMap R A))]

/-- **The three-chart affine-charted fibre datum.** Three copies of `Spf A`, glued along the basic
opens `D(f_i·f_j)` by the identity of `A`, over the affine base change `Spf B`. All six geometric
triple-overlap fields are derived from `tau` / `sigma` by the smart constructor
`AffineChartedFibreDatumX.ofAlgebraData`, and — unlike every earlier datum — they are non-vacuous
(see `datumX_xt'_eq`). -/
def datumX (B : Type u) [CommRing B] [Algebra R B] : AffineChartedFibreDatumX R I hI B :=
  AffineChartedFibreDatumX.ofAlgebraData hI
    (A := fun _ : ULift.{u} (Fin 3) => A)
    (g := fun i j => f i * f j)
    (topology := fun _ => (inferInstance : TopologicalSpace A))
    (isAdic := fun _ => (inferInstance : IsAdicRing (I.map (algebraMap R A))))
    (τ := fun i j _ => tau hI f i j)
    (τ_symm := fun i j _ => tau_symm hI f i j)
    (σ := fun i j k _ _ _ => sigma hI f i j k)
    (hστ := fun i j k _ _ _ => sigma_tau hI f i j k)
    (hσc := fun i j k _ _ _ => sigma_cocycle hI f i j k)

/-- **The glued three-chart formal scheme** `X`: three copies of `Spf A` glued along `D(f_i·f_j)`.
For `f₀ = f₁ = f₂ = 1` this is `Spf A` again; in general it is a genuinely non-affine (and
non-separated) formal scheme. -/
def gluedX (B : Type u) [CommRing B] [Algebra R B] : FormalScheme.{u} :=
  (datumX hI f B).xGlued

/-- **The fibre product** `X ×_{Spf R} Spf B` of the three-chart formal scheme with the affine base
change, assembled by the general construction of `FormalSchemes.GeneralFibreProductAffineBase`. -/
def fibreProductX (B : Type u) [CommRing B] [Algebra R B] : FormalScheme.{u} :=
  (datumX hI f B).fibreProduct

end Datum

/-! ### Non-vacuity of the geometric fields -/

section Vacuity

variable [TopologicalSpace A] [IsAdicRing (I.map (algebraMap R A))]
variable (B : Type u) [CommRing B] [Algebra R B]

/-! Distinctness in the index type `ULift (Fin 3)` is `ULift.up_injective.ne`, from Mathlib's
`Mathlib.Data.ULift`, applied to a `Fin 3` disequality decided by `decide`. This file used to
restate that upstream fact as a theorem of its own; two other files restated it privately. -/

/-- **The index type has a pairwise distinct triple** — unlike `ULift Bool`, so the geometric
triple-overlap fields below are not vacuously discharged. -/
theorem exists_pairwise_distinct :
    ∃ i j k : ULift.{u} (Fin 3), i ≠ j ∧ i ≠ k ∧ j ≠ k :=
  ⟨⟨0⟩, ⟨1⟩, ⟨2⟩, ULift.up_injective.ne (by decide), ULift.up_injective.ne (by decide),
    ULift.up_injective.ne (by decide)⟩

/-- **Non-vacuity of the fibre-product triple.** At a pairwise distinct triple the geometric
transition `t'` of the datum is the derived transition `AffineChartedFibreDatum.algDataT'` built
from `sigma` — a genuine pullback-level map, not `False.elim`. -/
theorem datumX_t'_eq (i j k : ULift.{u} (Fin 3)) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (datumX hI f B).t' i j k hij hik hjk =
      AffineChartedFibreDatum.algDataT' (B := B) hI (fun _ : ULift.{u} (Fin 3) => A)
        (fun i j => f i * f j) (fun i j k _ _ _ => sigma hI f i j k) i j k hij hik hjk :=
  rfl

/-- **Non-vacuity of the `X`-side triple.** At a pairwise distinct triple the geometric transition
`xt'` of the datum is the derived transition `AffineChartedFibreDatumX.xAlgDataT'` built from
`sigma`. -/
theorem datumX_xt'_eq (i j k : ULift.{u} (Fin 3)) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (datumX hI f B).xt' i j k hij hik hjk =
      AffineChartedFibreDatumX.xAlgDataT' hI (fun _ : ULift.{u} (Fin 3) => A)
        (fun i j => f i * f j) (fun i j k _ _ _ => sigma hI f i j k) i j k hij hik hjk :=
  rfl

/-- **Non-vacuity, concretely**, at the triple `0, 1, 2` of `ULift (Fin 3)`: the hypotheses of the
geometric fields are satisfiable and the field there is the derived transition. -/
theorem datumX_xt'_zero_one_two :
    (datumX hI f B).xt' ⟨0⟩ ⟨1⟩ ⟨2⟩ (ULift.up_injective.ne (by decide))
        (ULift.up_injective.ne (by decide)) (ULift.up_injective.ne (by decide)) =
      AffineChartedFibreDatumX.xAlgDataT' hI (fun _ : ULift.{u} (Fin 3) => A)
        (fun i j => f i * f j) (fun i j k _ _ _ => sigma hI f i j k) ⟨0⟩ ⟨1⟩ ⟨2⟩
        (ULift.up_injective.ne (by decide)) (ULift.up_injective.ne (by decide))
        (ULift.up_injective.ne (by decide)) :=
  rfl

end Vacuity

end ThreeChart

end AlgebraicGeometry

end
