import FormalSchemes.CofinalFormalSpectrumPoint
import FormalSchemes.CofinalCompletionFunctorial
import FormalSchemes.AwayCompletionRestrict

set_option linter.style.header false

/-!
# Restriction between basic opens commutes with the change of ideal of definition

`FormalSpectrum.awayCompletionRestrict` (`FormalSchemes.AwayCompletionRestrict`) is the canonical
`R{1/f} →+* R{1/g}` attached to an inclusion of basic opens `D(g) ⊆ D(f)` of `Spf (R, I)`, and
`AdicCompletion.cofinalHom` (`FormalSchemes.CofinalCompletion`) compares the completions taken at
two cofinal ideals. This file proves they commute:

```
R{1/f}_I ---- restrict ----> R{1/g}_I
   |                            |
cofinalHom                  cofinalHom
   |                            |
   v                            v
R{1/f}_J ---- restrict ----> R{1/g}_J
```

Together with the analogous square for `FormalSpectrum.awayToAtPrimeCompletion`, this is what the
invariance of `FormalSpectrum.IsStalkLimit` under a change of ideal of definition rests on.
Nothing here mentions a stalk; see `## What is *not* proved here`.

## How it is proved, and which of the two routes closed it

`awayCompletionRestrict` is by definition a composite of two maps, and **a composite commutes with
something exactly when both of its factors do**:

* the right factor is `AdicCompletion.mapCompletion` of `FormalSpectrum.awayAwayLift`, and it
  commutes with `AdicCompletion.cofinalHom` by
  `AdicCompletion.mapCompletion_comp_cofinalHom` (`FormalSchemes.CofinalCompletionFunctorial`)
  at one instantiation. Nothing is reproved here;
* the left factor is `RingSplit.adicAwayUnitEquiv'`
  (`FormalSchemes.AdicCompletionCongrLevel`), and no square for it existed on the tree. It is
  `RingSplit.cofinalHom_adicAwayUnitEquiv` below.

The second is the content of this file and it closed **level-wise**, not through the
structure-map-and-density route. `RingSplit.adicAwayUnitEquiv` is assembled from a level-`n`-to-
level-`n` family and `AdicCompletion.cofinalHom` reads level `n` of its target off level
`(b + 1) * n` of its source, so the square is not level-wise on the nose. What closes it is
`RingSplit.factor_awayUnitLevelEquiv`: `RingSplit.awayUnitLevelEquiv` commutes with
`Ideal.Quotient.factor` **between two different ideals and two different levels**, and not merely
with `Ideal.Quotient.factorPow` at one ideal, which is all
`RingSplit.factorPow_awayUnitLevelEquiv` supplies. That generalisation is one `obtain` and one
`simp only` away from the existing lemma, because both sides are computed by
`RingSplit.awayUnitLevelEquiv_mk` on a representative — the mismatch of levels never has to be
looked at.

`Ideal.Quotient.factorPow` is an `abbrev` for `Ideal.Quotient.factor` at
`Ideal.pow_le_pow_right`, so `RingSplit.factorPow_awayUnitLevelEquiv` is an *instance* of the
generalisation rather than a companion of it, and Mathlib's own `Ideal.Quotient.factorPow`
docstring asks for exactly this direction: before adding a lemma about it, check whether the lemma
generalises to `Ideal.Quotient.factor`. The generalisation is therefore a `move-lemma` question —
it belongs beside the lemma it generalises, in `FormalSchemes.AdicCompletionCongrLevel`, with the
`Ideal.Quotient.factorPow` form left as a one-line corollary. **Measured and reported, not acted
on here**, because performing it means rewriting `RingSplit.adicAwayUnitEquiv`'s definition in a
file this one only imports.

## The containment the squares are indexed by

`AdicCompletion.mapCompletion_comp_cofinalHom` is indexed by containments on the *extended* ideals,
while every consumer has one on `R`; `Ideal.pow_map_le_map` (`FormalSchemes.CofinalIdeal`) bridges
the two, with the same exponent on both sides. It is **not** stated here. It is a general fact
about `Ideal.map`, it is the step `Ideal.IsCofinal.map` is built from in that file, and the two
squares of this cluster — this one and the one for `FormalSpectrum.awayToAtPrimeCompletion` — would
otherwise each carry a copy in a different namespace, which the tree's duplicate-statement scan
cannot bucket together because the two binder orders differ.

## Main results

* `RingSplit.factor_awayUnitLevelEquiv`: the level isomorphisms of
  `RingSplit.adicAwayUnitEquiv` commute with the quotient factor maps across a change of ideal.
* `RingSplit.cofinalHom_adicAwayUnitEquiv` and its level-`1` form
  `RingSplit.cofinalHom_adicAwayUnitEquiv'`: **localizing at an already-invertible element commutes
  with the cofinal comparison.**
* `FormalSpectrum.basicOpen_le_of_isAdic` and `FormalSpectrum.basicOpen_le_congr_of_isAdic`: an
  inclusion of basic opens does not depend on the ideal of definition. This is the hypothesis the
  square below needs on the `J` side, and it is point data — it would have fitted
  `FormalSchemes.CofinalFormalSpectrumPoint`, and is here because this file is its only consumer.
* `FormalSpectrum.cofinalHom_awayCompletionRestrict`, its composed form
  `FormalSpectrum.cofinalHom_comp_awayCompletionRestrict`, and the two forms a consumer will
  actually have the hypotheses for: `..._of_pow_le`, stated at a containment `I ^ b ≤ J` in `R`
  rather than at its two extensions, and `..._of_isAdic`, which additionally derives the `J`-side
  inclusion of basic opens.

## What is *not* proved here

Nothing about `FormalSpectrum.stalkToLimit`, `FormalSpectrum.stalkToAdicCompletion` or
`FormalSpectrum.IsStalkLimit`, and nothing about `FormalSpectrum.awayToAtPrimeCompletion`, which is
the other of the two squares and is a separate file. Nothing here identifies
`FormalSpectrum.awayCompletionRestrict` with the structure-sheaf restriction either — that is the
open question `FormalSchemes.AwayCompletionRestrict`'s own `## What is *not* proved here` records,
and this square is about the map that file builds, not about the sheaf.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.1 and §10.3.
* [The Stacks Project, Tag 0AHZ](https://stacks.math.columbia.edu/tag/0AHZ).
-/

noncomputable section

universe u

namespace RingSplit

variable {B : Type u} [CommRing B] {K L : Ideal B} {s : B} {b : ℕ}

/-- **The level isomorphisms of `RingSplit.adicAwayUnitEquiv` commute with the quotient factor maps
across a change of ideal.** `RingSplit.factorPow_awayUnitLevelEquiv` is this at one ideal and two
levels; here the ideal moves too, which is what the comparison of two ideals of definition needs.

The proof does not have to look at the two levels at all: `Ideal.Quotient.mk` is surjective and
`RingSplit.awayUnitLevelEquiv_mk` computes both sides on a representative. -/
theorem factor_awayUnitLevelEquiv (hsK : ∀ n : ℕ, IsUnit (Ideal.Quotient.mk (K ^ n) s))
    (hsL : ∀ n : ℕ, IsUnit (Ideal.Quotient.mk (L ^ n) s)) {m n : ℕ}
    (h : K ^ m ≤ L ^ n) (h' : awayUnitIdeal K s ^ m ≤ awayUnitIdeal L s ^ n) (z : B ⧸ K ^ m) :
    Ideal.Quotient.factor h' (awayUnitLevelEquiv K s hsK m z) =
      awayUnitLevelEquiv L s hsL n (Ideal.Quotient.factor h z) := by
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective z
  simp only [awayUnitLevelEquiv_mk, Ideal.Quotient.factor_mk]

/-- `RingSplit.adicAwayUnitEquiv` read at level `n`: it is `RingSplit.awayUnitLevelEquiv` there.
This is `AdicCompletion.evalₐ_congrOfLevelEquiv` at the family the equivalence is built from, named
so that the square below is a rewrite rather than an unfolding. -/
theorem evalₐ_adicAwayUnitEquiv (hs : ∀ n : ℕ, IsUnit (Ideal.Quotient.mk (K ^ n) s)) (n : ℕ)
    (x : AdicCompletion K B) :
    AdicCompletion.evalₐ (awayUnitIdeal K s) n (adicAwayUnitEquiv K s hs x) =
      awayUnitLevelEquiv K s hs n (AdicCompletion.evalₐ K n x) :=
  AdicCompletion.evalₐ_congrOfLevelEquiv _ _ _ _ n x

/-- **Localizing at an already-invertible element commutes with the cofinal comparison.** For
cofinal ideals `K ^ b ≤ L` of `B` and an `s` invertible in every thickening at both, the square

```
AdicCompletion K B ------> B{1/s}^ at K·B_s
        |                        |
   cofinalHom               cofinalHom
        |                        |
        v                        v
AdicCompletion L B ------> B{1/s}^ at L·B_s
```

commutes, the horizontal maps being `RingSplit.adicAwayUnitEquiv`.

The two containments are both hypotheses rather than one being derived from the other, which is the
register of `AdicCompletion.mapCompletion_comp_cofinalHom`; `Ideal.pow_map_le_map` supplies the
second from the first at every call site. -/
theorem cofinalHom_adicAwayUnitEquiv (hb : K ^ b ≤ L)
    (hb' : awayUnitIdeal K s ^ b ≤ awayUnitIdeal L s)
    (hsK : ∀ n : ℕ, IsUnit (Ideal.Quotient.mk (K ^ n) s))
    (hsL : ∀ n : ℕ, IsUnit (Ideal.Quotient.mk (L ^ n) s)) (x : AdicCompletion K B) :
    AdicCompletion.cofinalHom hb' (adicAwayUnitEquiv K s hsK x) =
      adicAwayUnitEquiv L s hsL (AdicCompletion.cofinalHom hb x) := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  rw [AdicCompletion.evalₐ_cofinalHom, AdicCompletion.cofinalLevel_apply,
    evalₐ_adicAwayUnitEquiv, evalₐ_adicAwayUnitEquiv, AdicCompletion.evalₐ_cofinalHom,
    AdicCompletion.cofinalLevel_apply]
  exact factor_awayUnitLevelEquiv _ _ _ _ _

/-- **The level-`1` form of `RingSplit.cofinalHom_adicAwayUnitEquiv`**, matching
`RingSplit.adicAwayUnitEquiv'`: it is enough that `s` be invertible in the two residue rings
`B ⧸ K` and `B ⧸ L`. This is the form `FormalSpectrum.awayCompletionRestrict` is built from, since
`FormalSpectrum.isUnit_mk_algebraMap_of_basicOpen_le` produces exactly a level-`1` witness. -/
theorem cofinalHom_adicAwayUnitEquiv' (hb : K ^ b ≤ L)
    (hb' : awayUnitIdeal K s ^ b ≤ awayUnitIdeal L s) (hsK : IsUnit (Ideal.Quotient.mk K s))
    (hsL : IsUnit (Ideal.Quotient.mk L s)) (x : AdicCompletion K B) :
    AdicCompletion.cofinalHom hb' (adicAwayUnitEquiv' K s hsK x) =
      adicAwayUnitEquiv' L s hsL (AdicCompletion.cofinalHom hb x) :=
  cofinalHom_adicAwayUnitEquiv hb hb' _ _ x

end RingSplit

namespace FormalSpectrum

open AdicCompletion RingSplit

section

variable {R : Type u} [CommRing R] {I J : Ideal R} {f g : R} {b : ℕ}

/-- **Restriction between basic opens commutes with the cofinal comparison.** For an inclusion
`D(g) ⊆ D(f)` read at both ideals of definition, the canonical `R{1/f} →+* R{1/g}` of
`FormalSpectrum.awayCompletionRestrict` intertwines the two comparison maps
`AdicCompletion.cofinalHom`.

The two containments are on the *extended* ideals `I · R_f`, `I · R_g` and are independent
hypotheses; `FormalSpectrum.cofinalHom_comp_awayCompletionRestrict_of_pow_le` is the form stated at
a single containment in `R`, and is what a consumer will have. -/
theorem cofinalHom_awayCompletionRestrict (hI : I.FG) (hJ : J.FG)
    (hbf : (I.map (algebraMap R (Localization.Away f))) ^ b ≤
      J.map (algebraMap R (Localization.Away f)))
    (hbg : (I.map (algebraMap R (Localization.Away g))) ^ b ≤
      J.map (algebraMap R (Localization.Away g)))
    (hle : basicOpen I g ≤ basicOpen I f) (hle' : basicOpen J g ≤ basicOpen J f)
    (x : awayCompletion I f) :
    awayCompletionRestrict J f g hJ hle' (cofinalHom hbf x) =
      cofinalHom hbg (awayCompletionRestrict I f g hI hle x) := by
  have hsq := RingHom.congr_fun
    (mapCompletion_comp_cofinalHom (awayAwayLift f g) hbf
      (Ideal.pow_map_le_map hbg (algebraMap (Localization.Away g) (awayAway f g)))
      (map_awayAwayLift I f g).le (map_awayAwayLift J f g).le
      (hI.map _) ((hI.map _).map _) (hJ.map _) ((hJ.map _).map _)) x
  simp only [RingHom.comp_apply] at hsq
  rw [awayCompletionRestrict, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, hsq, awayCompletionRestrict, RingHom.comp_apply,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, RingEquiv.symm_apply_eq,
    ← cofinalHom_adicAwayUnitEquiv' hbg _ (isUnit_mk_algebraMap_of_basicOpen_le I f g hle)
      (isUnit_mk_algebraMap_of_basicOpen_le J f g hle'),
    RingEquiv.apply_symm_apply]

/-- The composed form of `FormalSpectrum.cofinalHom_awayCompletionRestrict`, in the register of
`AdicCompletion.mapCompletion_comp_cofinalHom`. -/
theorem cofinalHom_comp_awayCompletionRestrict (hI : I.FG) (hJ : J.FG)
    (hbf : (I.map (algebraMap R (Localization.Away f))) ^ b ≤
      J.map (algebraMap R (Localization.Away f)))
    (hbg : (I.map (algebraMap R (Localization.Away g))) ^ b ≤
      J.map (algebraMap R (Localization.Away g)))
    (hle : basicOpen I g ≤ basicOpen I f) (hle' : basicOpen J g ≤ basicOpen J f) :
    (awayCompletionRestrict J f g hJ hle').comp (cofinalHom hbf) =
      (cofinalHom hbg).comp (awayCompletionRestrict I f g hI hle) :=
  RingHom.ext fun x => cofinalHom_awayCompletionRestrict hI hJ hbf hbg hle hle' x

/-- **`FormalSpectrum.cofinalHom_comp_awayCompletionRestrict` at a containment in `R`.** The two
extended containments the square is indexed by both come from `I ^ b ≤ J` by
`Ideal.pow_map_le_map`, so the exponent is shared and a consumer needs only the one containment —
which is what `Ideal.IsCofinal.exists_pow_le` hands it. -/
theorem cofinalHom_comp_awayCompletionRestrict_of_pow_le (hI : I.FG) (hJ : J.FG) (hb : I ^ b ≤ J)
    (hle : basicOpen I g ≤ basicOpen I f) (hle' : basicOpen J g ≤ basicOpen J f) :
    (awayCompletionRestrict J f g hJ hle').comp (cofinalHom (Ideal.pow_map_le_map hb _)) =
      (cofinalHom (Ideal.pow_map_le_map hb _)).comp (awayCompletionRestrict I f g hI hle) :=
  cofinalHom_comp_awayCompletionRestrict hI hJ _ _ hle hle'

end

section

variable {R : Type u} [CommRing R] [TopologicalSpace R] {I J : Ideal R} {f g : R} {b : ℕ}

/-- **An inclusion of basic opens does not depend on the ideal of definition.** `D(g) ⊆ D(f)` in
`Spf_J R` gives `D(g) ⊆ D(f)` in `Spf_I R`: the two spaces are identified by
`IsAdic.homeomorphFormalSpectrum` and membership in a basic open transports along it
(`FormalSpectrum.mem_basicOpen_homeomorphFormalSpectrum`,
`FormalSchemes.CofinalFormalSpectrumPoint`).

Note the direction: no surjectivity of the homeomorphism is used, because the conclusion is
quantified over points of `Spf_I R` and the hypothesis over their images. The `Iff` is this lemma
applied twice, once each way round. -/
theorem basicOpen_le_of_isAdic (hI : IsAdic I) (hJ : IsAdic J)
    (h : basicOpen J g ≤ basicOpen J f) : basicOpen I g ≤ basicOpen I f := fun x hx =>
  (mem_basicOpen_homeomorphFormalSpectrum hI hJ x f).1
    (h ((mem_basicOpen_homeomorphFormalSpectrum hI hJ x g).2 hx))

/-- **The inclusion `D(g) ⊆ D(f)` is the same condition at the two ideals of definition.** This is
the hypothesis `FormalSpectrum.awayCompletionRestrict` takes, so it is what lets the square below
be stated with one inclusion rather than two unrelated ones. -/
theorem basicOpen_le_congr_of_isAdic (hI : IsAdic I) (hJ : IsAdic J) (f g : R) :
    basicOpen I g ≤ basicOpen I f ↔ basicOpen J g ≤ basicOpen J f :=
  ⟨basicOpen_le_of_isAdic hJ hI, basicOpen_le_of_isAdic hI hJ⟩

/-- **The square at two ideals of definition of one topological ring**, which is the form the
cofinal-invariance of the stalk-limit question consumes: one containment `I ^ b ≤ J` in `R`, one
inclusion of basic opens, and the `J`-side inclusion derived rather than assumed.

Obtain `hb` from `Ideal.IsCofinal.exists_pow_le` applied to `IsAdic.isCofinal`
(`FormalSchemes.CofinalIdeal`), which says any two ideals of definition of one topological ring are
cofinal and carries no finite-generation hypothesis; `hI` and `hJ` are needed anyway, by
`FormalSpectrum.awayCompletionRestrict`. -/
theorem cofinalHom_comp_awayCompletionRestrict_of_isAdic (hIa : IsAdic I) (hJa : IsAdic J)
    (hI : I.FG) (hJ : J.FG) (hb : I ^ b ≤ J) (hle : basicOpen I g ≤ basicOpen I f) :
    (awayCompletionRestrict J f g hJ ((basicOpen_le_congr_of_isAdic hIa hJa f g).1 hle)).comp
        (cofinalHom (Ideal.pow_map_le_map hb _)) =
      (cofinalHom (Ideal.pow_map_le_map hb _)).comp (awayCompletionRestrict I f g hI hle) :=
  cofinalHom_comp_awayCompletionRestrict_of_pow_le hI hJ hb hle _

end

end FormalSpectrum

end
