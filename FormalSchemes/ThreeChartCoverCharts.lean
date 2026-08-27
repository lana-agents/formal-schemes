import FormalSchemes.AwayCompletionNestedNaturality
import FormalSchemes.ThreeChartDatum

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1000000

/-!
# The charts of the three-chart open cover, and their overlaps

Fix an adic base `(R, I)` with `I` finitely generated, an `R`-algebra `A` and three elements
`f₀, f₁, f₂ : A`. This file sets up the charts of the open cover of `Spf A` by the three basic
opens `D(f_i)` — chart algebras `A i := A{1/f_i}` and overlap elements
`g i j := ` the image of `f_i · f_j` in `A{1/f_i}` — and identifies the chart-local single and
double overlaps with completed localizations of `A` itself:

```
A{1/f_i}{1/g_ij}          ≃ₐ[R]  A{1/(f_i f_j)}
A{1/f_i}{1/(g_ij·g_ik)}   ≃ₐ[R]  A{1/(f_i f_j · f_i f_k)}
```

Both are the nested basic-open chart identification of issue 607
(`FormalSpectrum.awayCompletionNestedAlgEquiv`), the second composed with the transport
`awayCongrEquivOfEq` absorbing `map_mul`. Their **naturality**
(`awayCongrHom_chartOverlapEquiv`, `awayCongrHom_chartOverlapEquiv'`) is what
`FormalSchemes.ThreeChartCoverTransitions` uses to reduce the datum's `hστ` obligation to the
corresponding statement downstairs on `A`; it rests on the naturality square of
`FormalSchemes.AwayCompletionNestedNaturality`.

Note that `A` itself is **not** required to be an adic ring: only the chart algebras `A{1/f_i}`
occur as charts, and a completed localization is adic for free
(`FormalSpectrum.isAdicRing_awayCompletionIdeal`, packaged here as `chartIsAdicRing`, which states
it at the datum's own ideal spelling `I.map (algebraMap R (A{1/f_i}))` rather than at the folded
`awayCompletionIdeal`).

## Cost note — read this before touching anything in this file

The chart-local double overlap `A{1/f_i}{1/(g_ij·g_ik)}` is a **doubly nested** completion of a
localization, and its away element is a *product* of two elements of a completion. Anything that
makes Lean reduce such a term is catastrophically expensive — but the cost is invisible to
`set_option profiler true`, because it is all **kernel type-checking**, which Lean 4.32 performs
in asynchronous tasks that the profiler does not attribute. (`set_option debug.skipKernelTC true`
takes this file from minutes to seconds. That is how the cost was located.)

Three consequences shaped the code below, and undoing any of them costs ~10 minutes of build
time or an out-of-memory kill:

1. `awayCongrEquivOfEq` transports along an *equality* of away elements by matching on `rfl`,
   rather than `awayCongrEquiv` at two mutual divisibilities. The latter drags
   `IsLocalization.Away.lift` through the multiplication of the nested completion.
   `AdicCompletion.congrIdealₐ` (`FormalSchemes.AdicCompletionCongrIdealAlg`) is `subst`-built
   for the same reason.
2. The naturality lemmas are stated with `awayCongrHom`, not `furtherLocFst`/`furtherLocSnd`, and
   are *pure applications* with no rewriting. The two families of maps are equal
   (`furtherLocFst_eq_awayCongrHom`), but that rewrite is performed in
   `FormalSchemes.ThreeChartCoverTransitions`, where the chart algebra is a variable.
3. The transitions and the three datum laws live in separate files, and the laws are proved by
   conjugation lemmas stated with the chart algebras abstract. See the module note there.
4. `chartOverlapEquiv` is **never delta-unfolded by the kernel inside a statement**. The naturality
   lemmas are stated in terms of it, as their consumers need, but proved by `congrArg` against
   `chartOverlapEquiv_apply` — a top-level `rfl` that performs the one unfolding in isolation.
   Removing that step and closing the lemmas by `exact awayCongrHom_nestedCongrOfEq …` directly
   is what the file used to do, and it cost **~160 s of kernel time per lemma**: the kernel then
   has to unfold `chartOverlapEquiv` while comparing two equations between doubly nested
   completions, instead of comparing two elements of one. Measured on issue 737: the module went
   from **368 s / 7.49 GB peak** to **10 s / 2.86 GB peak** — the whole cost of the file was those
   two unfoldings, and every other declaration in it is free.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1 (10.1.4), §10.7.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry FormalSpectrum
open CompletedTensorAwayInterchange

universe u

namespace AlgebraicGeometry

namespace ThreeChartCover

variable {R : Type u} [CommRing R] (I : Ideal R)
variable {A : Type u} [CommRing A] [Algebra R A]
variable (f : ULift.{u} (Fin 3) → A)

/-! ### The charts and their overlaps -/

/-- **The `i`-th chart algebra** `A{1/f_i}`: the sections of `O_{Spf A}` over the basic open
`D(f_i)`. Unlike the charts of `FormalSchemes.ThreeChartDatum`, these genuinely differ from one
another. -/
abbrev chartAlgebra (i : ULift.{u} (Fin 3)) : Type u :=
  awayCompletion (I.map (algebraMap R A)) (f i)

/-- **The overlap element** `g i j : A{1/f_i}`, the image of `f_i · f_j`. It cuts out
`D(f_j) ∩ D(f_i)` inside the chart `Spf A{1/f_i}` — the image of `f_j` would cut out the same
basic open, but this spelling is the one for which the nested chart identification of issue 607
applies verbatim. -/
abbrev overlapElt (i j : ULift.{u} (Fin 3)) : chartAlgebra I f i :=
  awayCompletionHom (I.map (algebraMap R A)) (f i) (f i * f j)

/-- The chart algebras are adic rings, with no hypothesis on `A`: a completed localization is
complete for the extension of its ideal, and the datum's ideal spelling
`I.map (algebraMap R (A{1/f_i}))` is that extension (`map_algebraMap_awayCompletion_eq`). -/
theorem chartIsAdicRing (hI : I.FG) (i : ULift.{u} (Fin 3)) :
    IsAdicRing (I.map (algebraMap R (chartAlgebra I f i))) := by
  rw [map_algebraMap_awayCompletion_eq]
  exact FormalSpectrum.isAdicRing_awayCompletionIdeal _ _ (hI.map (algebraMap R A))

/-! ### Units -/

/-- `f_i` becomes a unit after inverting `f_i · f_j`. -/
theorem isUnit_self_mul (i j : ULift.{u} (Fin 3)) :
    IsUnit (algebraMap A (Localization.Away (f i * f j)) (f i)) :=
  isUnit_algebraMap_away_of_dvd_pow 1 ⟨f j, by rw [pow_one]⟩

/-- `f_i` becomes a unit after inverting `f_i f_j · f_i f_k`. -/
theorem isUnit_self_triple (i j k : ULift.{u} (Fin 3)) :
    IsUnit (algebraMap A (Localization.Away (f i * f j * (f i * f k))) (f i)) :=
  isUnit_algebraMap_away_of_dvd_pow 1 ⟨f j * (f i * f k), by rw [pow_one]; ring⟩

/-- `f_i f_j` becomes a unit after inverting `f_i f_j · f_i f_k`. -/
theorem isUnit_mul_triple (i j k : ULift.{u} (Fin 3)) :
    IsUnit (algebraMap A (Localization.Away (f i * f j * (f i * f k))) (f i * f j)) :=
  isUnit_algebraMap_away_of_dvd_pow 1 ⟨f i * f k, by rw [pow_one]⟩

/-- `f_i f_j` becomes a unit after inverting `f_i f_k · f_i f_j`. -/
theorem isUnit_mul_triple' (i j k : ULift.{u} (Fin 3)) :
    IsUnit (algebraMap A (Localization.Away (f i * f k * (f i * f j))) (f i * f j)) :=
  isUnit_algebraMap_away_of_dvd_pow 1 ⟨f i * f k, by rw [pow_one]; ring⟩

/-- The image of `f_i f_j · f_i f_k` in the chart `A{1/f_i}` is the product `g_ij · g_ik` of the
two overlap elements — the chart-level away element the datum's double overlap is presented at. -/
theorem chartHom_triple (i j k : ULift.{u} (Fin 3)) :
    awayCompletionHom (I.map (algebraMap R A)) (f i) (f i * f j * (f i * f k)) =
      overlapElt I f i j * overlapElt I f i k :=
  map_mul _ _ _

/-- `g_ij` becomes a unit after inverting `g_ij · g_ik`. -/
theorem isUnit_overlapElt_mul (i j k : ULift.{u} (Fin 3)) :
    IsUnit (algebraMap (chartAlgebra I f i)
      (Localization.Away (overlapElt I f i j * overlapElt I f i k)) (overlapElt I f i j)) :=
  isUnit_algebraMap_away_of_dvd_pow 1 ⟨overlapElt I f i k, by rw [pow_one]⟩

/-- `g_ij` becomes a unit after inverting `g_ik · g_ij` — the `furtherLocSnd` orientation. -/
theorem isUnit_overlapElt_mul_right (i j k : ULift.{u} (Fin 3)) :
    IsUnit (algebraMap (chartAlgebra I f i)
      (Localization.Away (overlapElt I f i k * overlapElt I f i j)) (overlapElt I f i j)) :=
  isUnit_algebraMap_away_of_dvd_pow 1 ⟨overlapElt I f i k, by rw [pow_one]; ring⟩

/-- `g_ij` is a unit after inverting the image of the triple product. -/
theorem isUnit_overlapElt_chartHom (i j k : ULift.{u} (Fin 3)) :
    IsUnit (algebraMap (chartAlgebra I f i)
      (Localization.Away
        (awayCompletionHom (I.map (algebraMap R A)) (f i) (f i * f j * (f i * f k))))
      (overlapElt I f i j)) :=
  isUnit_algebraMap_away_of_dvd_pow 1
    ⟨overlapElt I f i k, by rw [pow_one]; exact chartHom_triple I f i j k⟩

/-- `g_ij` is a unit after inverting the image of the triple product written the other way round
(the `furtherLocSnd` orientation). -/
theorem isUnit_overlapElt_chartHom' (i j k : ULift.{u} (Fin 3)) :
    IsUnit (algebraMap (chartAlgebra I f i)
      (Localization.Away
        (awayCompletionHom (I.map (algebraMap R A)) (f i) (f i * f k * (f i * f j))))
      (overlapElt I f i j)) :=
  isUnit_algebraMap_away_of_dvd_pow 1
    ⟨overlapElt I f i k, by rw [pow_one]; exact (chartHom_triple I f i k j).trans (mul_comm _ _)⟩

/-! ### The chart identifications `N` -/

/-- **The single overlap, read downstairs.** The chart-local overlap `A{1/f_i}{1/g_ij}` of the
`i`-th and `j`-th charts is identified with the completed localization `A{1/(f_i f_j)}` of `A`
itself; this is the `g := f · g` case of issue 607's nested chart identification. -/
def chartOverlapEquiv (hI : I.FG) (i j : ULift.{u} (Fin 3)) :
    awayCompletion (I.map (algebraMap R A)) (f i * f j) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (chartAlgebra I f i))) (overlapElt I f i j) :=
  awayCompletionNestedAlgEquiv I hI (f i) (f i * f j) (isUnit_self_mul f i j)

/-- **The double overlap, read downstairs.** The chart-local double overlap
`A{1/f_i}{1/(g_ij·g_ik)}` is identified with `A{1/(f_i f_j · f_i f_k)}`: the nested chart
identification of issue 607, followed by the comparison isomorphism absorbing
`chartHom_triple` (the image of the triple product and the product of the two overlap elements are
equal elements of `A{1/f_i}`, but index different completed localizations). -/
def chartTripleEquiv (hI : I.FG) (i j k : ULift.{u} (Fin 3)) :
    awayCompletion (I.map (algebraMap R A)) (f i * f j * (f i * f k)) ≃ₐ[R]
      awayCompletion (I.map (algebraMap R (chartAlgebra I f i)))
        (overlapElt I f i j * overlapElt I f i k) :=
  (awayCompletionNestedAlgEquiv I hI (f i) (f i * f j * (f i * f k))
      (isUnit_self_triple f i j k)).trans
    (awayCongrEquivOfEq I (chartHom_triple I f i j k))

/-- **`chartOverlapEquiv` applied to an element**, spelled out as the nested chart identification
it is by definition.

This looks redundant, and it is not: it is the whole build cost of this file. Stating the
naturality lemmas below directly in terms of `chartOverlapEquiv` forces the kernel to delta-unfold
this definition *inside* an equation between doubly nested completions, and that single unfolding
costs about 160 s per lemma. Discharging it once here, at the top level where the two sides are
compared directly, costs nothing, and the naturality lemmas then close by `congrArg` against a
statement the kernel can match syntactically. Measured: 368 s → 20 s for the module (issue 737). -/
theorem chartOverlapEquiv_apply (hI : I.FG) (i j : ULift.{u} (Fin 3))
    (x : awayCompletion (I.map (algebraMap R A)) (f i * f j)) :
    chartOverlapEquiv I f hI i j x =
      awayCompletionNestedAlgEquiv I hI (f i) (f i * f j) (isUnit_self_mul f i j) x :=
  rfl

/-! ### Naturality of `N` -/

/-- **The left leg is natural.** Restricting from the single overlap `D(g_ij)` to the double
overlap `D(g_ij·g_ik)` inside the chart `Spf A{1/f_i}` agrees, through the identifications `N`,
with restricting from `D(f_i f_j)` to `D(f_i f_j · f_i f_k)` downstairs on `Spf A`.

Phrased with `awayCongrHom` rather than `furtherLocFst`: the two are the same map
(`furtherLocFst_eq_awayCongrHom`), but performing that rewrite *here*, at a doubly nested
completion, costs minutes of kernel time. It is done instead inside
`ThreeChartCover.sigma_tau_conj`, where the chart algebra is a variable. -/
theorem awayCongrHom_chartOverlapEquiv (hI : I.FG) (i j k : ULift.{u} (Fin 3))
    (x : awayCompletion (I.map (algebraMap R A)) (f i * f j)) :
    awayCongrHom I (overlapElt I f i j) (overlapElt I f i j * overlapElt I f i k) hI
        (isUnit_overlapElt_mul I f i j k) (chartOverlapEquiv I f hI i j x) =
      chartTripleEquiv I f hI i j k (awayCongrHom I (f i * f j) (f i * f j * (f i * f k)) hI
        (isUnit_mul_triple f i j k) x) :=
  (congrArg (fun y => awayCongrHom I (overlapElt I f i j)
        (overlapElt I f i j * overlapElt I f i k) hI (isUnit_overlapElt_mul I f i j k) y)
      (chartOverlapEquiv_apply I f hI i j x)).trans
    (awayCongrHom_nestedCongrOfEq I hI (f i) (f i * f j) (f i * f j * (f i * f k))
      (isUnit_self_mul f i j) (isUnit_self_triple f i j k) (isUnit_mul_triple f i j k)
      (isUnit_overlapElt_chartHom I f i j k) _ (chartHom_triple I f i j k)
      (isUnit_overlapElt_mul I f i j k) x)

/-- **The right leg is natural**, the companion of `awayCongrHom_chartOverlapEquiv` in which the
double overlap is presented as `g_ik · g_ij`. -/
theorem awayCongrHom_chartOverlapEquiv' (hI : I.FG) (i j k : ULift.{u} (Fin 3))
    (x : awayCompletion (I.map (algebraMap R A)) (f i * f j)) :
    awayCongrHom I (overlapElt I f i j) (overlapElt I f i k * overlapElt I f i j) hI
        (isUnit_overlapElt_mul_right I f i j k) (chartOverlapEquiv I f hI i j x) =
      chartTripleEquiv I f hI i k j (awayCongrHom I (f i * f j) (f i * f k * (f i * f j)) hI
        (isUnit_mul_triple' f i j k) x) :=
  (congrArg (fun y => awayCongrHom I (overlapElt I f i j)
        (overlapElt I f i k * overlapElt I f i j) hI (isUnit_overlapElt_mul_right I f i j k) y)
      (chartOverlapEquiv_apply I f hI i j x)).trans
    (awayCongrHom_nestedCongrOfEq I hI (f i) (f i * f j) (f i * f k * (f i * f j))
      (isUnit_self_mul f i j) (isUnit_self_triple f i k j) (isUnit_mul_triple' f i j k)
      (isUnit_overlapElt_chartHom' I f i j k) _ (chartHom_triple I f i k j)
      (isUnit_overlapElt_mul_right I f i j k) x)


end ThreeChartCover

end AlgebraicGeometry

end
