import FormalSchemes.CofinalCompletion
import FormalSchemes.BasicOpenImmersion

set_option linter.style.header false

/-!
# Naturality of the cofinal comparison map

`FormalSchemes.CofinalCompletion` (issue 74, goal 1) proved that two cofinal ideals `K`, `L` of a
ring `S` have canonically isomorphic adic completions, `AdicCompletion.cofinalRingEquiv`. Applied to
the two ideals of definition `I · R_f`, `J · R_f` of a localization `R_f`, this identifies the two
descriptions of the ring of sections `Γ(D(f), O_{Spf R})` of the formal-spectrum structure sheaf on
a basic open (issues 26–30) — the *ring-level* content of the fact that `Spf R` depends only on the
topological ring `R`, not on the chosen ideal of definition (EGA I, §10.3).

To upgrade that section-level identification to an isomorphism of *structure sheaves*
`Spf_I R ≅ Spf_J R` one must know the section-level isomorphisms are **compatible with the
restriction maps** of `O_{Spf R}` between basic opens `D(g) ⊆ D(f)`. Those restriction maps are, on
sections, the completion functor `AdicCompletion.mapCompletion` of the localization `R_f → R_g`
(`FormalSchemes.BasicOpenImmersion`). This file supplies exactly that compatibility, purely at the
ring level: the cofinal comparison map `cofinalHom` is natural with respect to `mapCompletion`.

This is the "compatibility on basic opens" step that the issue-74 route names as the input to the
eventual sheaf-level gluing (the full `LocallyRingedSpace` isomorphism `Spf_I R ≅ Spf_J R`, an
isomorphism of the two towers over the homeomorphism `IsAdic.homeomorphFormalSpectrum`, remains a
follow-up — it is heavy sheaf/`PresheafedSpace` category theory over a genuine homeomorphism base).

## Main results

* `AdicCompletion.quotientMap_comp_factor`: the commuting square of quotient maps
  `quotientMap ∘ factor = factor ∘ quotientMap` induced by a ring homomorphism and two
  containments of ideals.
* `AdicCompletion.mapCompletion_comp_cofinalHom`: **naturality** of the cofinal comparison map —
  for a ring homomorphism `f : R →+* S` and cofinal ideals `K ^ b ≤ L` in `R`, `K' ^ b ≤ L'` in
  `S`, with `f` carrying `K ↦ K'`, `L ↦ L'`, one has
  `mapCompletion f ∘ cofinalHom = cofinalHom ∘ mapCompletion f`.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], §10.3.
* [The Stacks Project, Tag 0AHZ](https://stacks.math.columbia.edu/tag/0AHZ).
-/

noncomputable section

universe u

namespace AdicCompletion

variable {R S : Type u} [CommRing R] [CommRing S]

/-- The commuting square of quotient maps induced by a ring homomorphism `f : R →+* S` and two
containments `P ≤ Q` (in `R`), `P' ≤ Q'` (in `S`), compatible with `f` in the sense `P ≤ f⁻¹ P'`,
`Q ≤ f⁻¹ Q'`. Both composites send `mk r ↦ mk (f r)`. -/
theorem quotientMap_comp_factor (f : R →+* S) {P Q : Ideal R} {P' Q' : Ideal S}
    (hPQ : P ≤ Q) (hP'Q' : P' ≤ Q') (hcP : P ≤ P'.comap f) (hcQ : Q ≤ Q'.comap f) :
    (Ideal.quotientMap Q' f hcQ).comp (Ideal.Quotient.factor hPQ) =
      (Ideal.Quotient.factor hP'Q').comp (Ideal.quotientMap P' f hcP) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
  simp only [RingHom.comp_apply, Ideal.Quotient.factor_mk, Ideal.quotientMap_mk]

/-- **Naturality of the cofinal comparison map.** For a ring homomorphism `f : R →+* S`, cofinal
ideals `K ^ b ≤ L` in `R` and `K' ^ b ≤ L'` in `S`, and compatibility `K.map f ≤ K'`,
`L.map f ≤ L'`, the completion functor `mapCompletion f` commutes with the cofinal comparison maps:
```
mapCompletion f ∘ cofinalHom hb = cofinalHom hb' ∘ mapCompletion f.
```
Applied to a localization map `R_f → R_g` and the ideals of definition `I · R_f`, `J · R_f`,
`I · R_g`, `J · R_g`, this is the compatibility of the section-level `Spf`-independence isomorphism
with the restriction maps of `O_{Spf R}` between basic opens `D(g) ⊆ D(f)` — the pre-gluing input
for the structure-sheaf intertwining `Spf_I R ≅ Spf_J R`. -/
theorem mapCompletion_comp_cofinalHom (f : R →+* S) {K L : Ideal R} {K' L' : Ideal S} {b : ℕ}
    (hb : K ^ b ≤ L) (hb' : K' ^ b ≤ L') (hfK : K.map f ≤ K') (hfL : L.map f ≤ L')
    (hK : K.FG) (hK' : K'.FG) (hL : L.FG) (hL' : L'.FG) :
    (mapCompletion f hfL hL').comp (cofinalHom hb) =
      (cofinalHom hb').comp (mapCompletion f hfK hK') := by
  -- The comap compatibilities `K ^ m ≤ f⁻¹ (K' ^ m)` and `L ^ n ≤ f⁻¹ (L' ^ n)`.
  have hcK : ∀ m : ℕ, K ^ m ≤ (K' ^ m).comap f := fun m => by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hfK m
  have hcL : ∀ n : ℕ, L ^ n ≤ (L' ^ n).comap f := fun n => by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact Ideal.pow_right_mono hfL n
  -- Two adic completions agree when they agree at every truncation level.
  refine RingHom.ext fun x => AdicCompletion.ext_evalₐ fun n => ?_
  rw [RingHom.comp_apply, RingHom.comp_apply,
    evalₐ_mapCompletion f hfL hL' hL n (hcL n), evalₐ_cofinalHom, cofinalLevel_apply,
    evalₐ_cofinalHom, cofinalLevel_apply,
    evalₐ_mapCompletion f hfK hK' hK ((b + 1) * n) (hcK ((b + 1) * n))]
  -- Both sides are now `R ⧸ K ^ ((b+1)*n) → S ⧸ L' ^ n` applied to `evalₐ K ((b+1)*n) x`.
  exact RingHom.congr_fun
    (quotientMap_comp_factor f (pow_mul_le_pow hb n) (pow_mul_le_pow hb' n)
      (hcK ((b + 1) * n)) (hcL n)) _

end AdicCompletion
