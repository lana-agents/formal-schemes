import FormalSchemes.TateOverlapDisjoint
import FormalSchemes.TateOverlapImmersion

set_option linter.style.header false
set_option linter.style.setOption false
set_option maxHeartbeats 3200000

/-!
# A disjoint pair of basic opens is itself a basic open, and the Tate two-chart overlap

If two elements `f`, `g` of a ring have `f · g = 0`, then the basic opens `D(f)` and `D(g)` are
disjoint and their **union is again a basic open**, namely `D(f + g)`:

```
D(f + g) = D(f) ⊔ D(g)          (when f · g = 0)
```

The inclusion `⊇` is the interesting half: if `f ∉ 𝔭` then `f · (f + g) = f² ∈ 𝔭` would force
`f ∈ 𝔭`, so `f + g ∉ 𝔭`. (Note this is *false* without the hypothesis — `D(f + g)` is not
generally contained in `D(f) ∪ D(g)`, let alone equal to it.)

## Why this matters here

On the Tate annulus `A = R{x, y}/(x·y − q)` with `q ∈ I` the relation `x · y = q` vanishes in
`A ⧸ (I·A)` (`mk_algebraMap_q_eq_zero`), so `D(x)` and `D(y)` are disjoint — that is
`annulusOverlap_basicOpen_disjoint`, the fact that makes the Tate chain a *chain*. This file
records the complementary fact: their union is the single basic open `D(x + y)`.

That matters for the general §10.15 machinery. `AlgebraicGeometry.AffineChartedFibreDatum`
(`FormalSchemes.GeneralFibreProductAffineBase`) requires, for each ordered pair of charts, a
**single** away element `g i j : A i` whose basic open is the *whole* overlap of the two charts.
The Tate curve model `𝔈_q` glues its two annulus charts along `D(x) ⊔ D(y)` — two copies of `Ĝm`,
which is exactly what makes the model circular rather than an open chain — and a coproduct of two
basic-open charts is not, on the face of it, a basic-open chart. `annulusOverlap_basicOpen_add`
below says the overlap *is* a single basic open after all, cut out by `x + y`. So the obstruction
to presenting `𝔈_q` as an `AffineChartedFibreDatumX` is not the shape of its overlap; what remains
is the ring-level splitting `A{1/(x+y)}^ ≃ A{1/x}^ × A{1/y}^`.

## Main results

* `PrimeSpectrum.basicOpen_add_of_mul_eq_zero`: `D(a + b) = D(a) ⊔ D(b)` when `a · b = 0`.
* `FormalSpectrum.basicOpen_add_of_mul_eq_zero`: the same on `Spf`, where the hypothesis is only
  that `f · g` vanishes *modulo the ideal of definition*.
* `AlgebraicGeometry.annulusOverlap_basicOpen_add`: on the Tate annulus, `D(x + y) = D(x) ⊔ D(y)`.
* `AlgebraicGeometry.range_annulusOverlapCharts_union`: the two Tate overlap charts cover exactly
  the range of the single basic-open chart at `x + y`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7, §10.15.
-/

open AlgebraicGeometry TopologicalSpace

universe u

namespace PrimeSpectrum

variable {S : Type u} [CommRing S]

/-- **A disjoint union of two basic opens is a basic open.** If `a · b = 0` then
`D(a + b) = D(a) ⊔ D(b)`.

The `⊇` half is where the hypothesis is used: if `a + b ∈ 𝔭` then `a² = a · (a + b) - a · b ∈ 𝔭`,
hence `a ∈ 𝔭` by primality. The `⊆` half is unconditional — if `a` and `b` both lie in `𝔭` so does
their sum. -/
theorem basicOpen_add_of_mul_eq_zero (a b : S) (hab : a * b = 0) :
    PrimeSpectrum.basicOpen (a + b) = PrimeSpectrum.basicOpen a ⊔ PrimeSpectrum.basicOpen b := by
  ext p
  simp only [SetLike.mem_coe, TopologicalSpace.Opens.mem_sup, mem_basicOpen]
  constructor
  · intro hp
    by_contra hc
    exact hp (add_mem (by tauto) (by tauto))
  · rintro (ha | hb)
    · intro hsum
      have h2 : a * (a + b) ∈ p.asIdeal := Ideal.mul_mem_left _ _ hsum
      rw [mul_add, hab, add_zero, ← pow_two] at h2
      exact ha (p.isPrime.mem_of_pow_mem 2 h2)
    · intro hsum
      have h2 : b * (a + b) ∈ p.asIdeal := Ideal.mul_mem_left _ _ hsum
      rw [mul_add, mul_comm b a, hab, zero_add, ← pow_two] at h2
      exact hb (p.isPrime.mem_of_pow_mem 2 h2)

end PrimeSpectrum

namespace FormalSpectrum

variable {R : Type u} [CommRing R] (I : Ideal R)

/-- **A disjoint union of two basic opens of `Spf R` is a basic open.** The underlying space of
`Spf R` is `Spec (R ⧸ I)`, so the hypothesis needed is only that `f · g` vanishes *modulo the ideal
of definition* — not in `R` itself. -/
theorem basicOpen_add_of_mul_eq_zero (f g : R) (h : Ideal.Quotient.mk I (f * g) = 0) :
    basicOpen I (f + g) = basicOpen I f ⊔ basicOpen I g := by
  have hab : Ideal.Quotient.mk I f * Ideal.Quotient.mk I g = 0 := by
    rw [← map_mul]; exact h
  rw [basicOpen, map_add]
  exact PrimeSpectrum.basicOpen_add_of_mul_eq_zero _ _ hab

end FormalSpectrum

namespace AlgebraicGeometry

open FormalSpectrum

variable (R : Type u) [CommRing R] (I : Ideal R) (q : R)

/-- **The Tate two-chart overlap is a single basic open.** On the formal annulus `A` the two
overlap loci `D(x)` and `D(y)` are disjoint (`annulusOverlap_basicOpen_disjoint`), and their union
is cut out by the single element `x + y`.

This is the companion of `annulusOverlap_basicOpen_disjoint`: that lemma says the Tate chain is a
chain, this one says the *circular* two-chart gluing of `𝔈_q` still has basic-open overlaps, so
`𝔈_q` is not excluded from the `AffineChartedFibreDatum` shape on topological grounds. -/
theorem annulusOverlap_basicOpen_add (hq : q ∈ I) :
    basicOpen (annulusIdealOfDefinition R I q) (overlapX R I q + overlapY R I q) =
      basicOpen (annulusIdealOfDefinition R I q) (overlapX R I q) ⊔
        basicOpen (annulusIdealOfDefinition R I q) (overlapY R I q) :=
  FormalSpectrum.basicOpen_add_of_mul_eq_zero _ _ _
    (by rw [overlapX_mul_overlapY]; exact mk_algebraMap_q_eq_zero R I q hq)

/-- **The two Tate overlap charts together cover exactly one basic-open chart.** The union of the
ranges of `annulusOverlapChart` (the locus `D(x)`) and `annulusOverlapChartY` (the locus `D(y)`) is
the range of the single basic-open chart at `x + y`.

Together with `annulusOverlapChart_range_disjoint` this exhibits the Tate curve model's chart
overlap — the disjoint pair of formal multiplicative groups `Spf A{1/x} ⊔ Spf A{1/y}` — as the
underlying space of the *affine* chart `Spf A{1/(x + y)}`. -/
theorem range_annulusOverlapCharts_union (hq : q ∈ I) (hI : I.FG) :
    Set.range (annulusOverlapChart R I q).base ∪
        Set.range (annulusOverlapChartY R I q).base =
      Set.range (basicOpenChart (annulusIdealOfDefinition R I q)
        (overlapX R I q + overlapY R I q)).base := by
  rw [range_basicOpenChart_base _ _ (annulusIdealOfDefinition_fg R I q hI),
    annulusOverlap_basicOpen_add R I q hq, range_annulusOverlapChart_base R I q hI,
    show annulusOverlapChartY R I q = basicOpenChart _ (overlapY R I q) from rfl,
    range_basicOpenChart_base _ _ (annulusIdealOfDefinition_fg R I q hI)]
  rfl

end AlgebraicGeometry
