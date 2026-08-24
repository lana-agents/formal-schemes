import FormalSchemes.IndSchemeExistence

set_option linter.style.header false

/-!
# The existence half, geometrically (EGA I, 10.6.7)

`FormalSchemes/IndSchemeExistence.lean` proved that a compatible family of **ring homomorphisms**
`φ n : B →+* R ⧸ Iⁿ` comes from a unique morphism `Spf R ⟶ Spec B`. This file says the same thing
about a compatible family of **morphisms of locally ringed spaces**

```
f n : Spec (R ⧸ I ^ (n + 1)) ⟶ Spec B,   Spec (stepRingHom I n) ≫ f (n + 1) = f n,
```

which is the form "`Spf R` is the colimit of its infinitesimal thickenings" actually takes: a
reader of EGA 10.6.7 arrives holding morphisms of spaces, not ring maps. Without this step a
consumer of that shape cannot use `IndSchemeExistence.lean` at all, because producing the `φ` it
wants from `f` is exactly the missing argument.

## The argument

`Spec.toLocallyRingedSpace : CommRingCatᵒᵖ ⥤ LocallyRingedSpace` is full and faithful, so the
whole file is bookkeeping around `Functor.preimage`.

* **Fullness** turns each `f n` into a ring homomorphism `ringHomOfSpecHom I B f n : B →+* R ⧸
  I^{n+1}`. The computation rule `specMap_ringHomOfSpecHom` is a bare `Functor.map_preimage`: no
  bridging lemma is needed, because `Spec.toLocallyRingedSpace.map p` **is**
  `Spec.locallyRingedSpaceMap p.unop` and `CommRingCat.ofHom h.hom` **is** `h`.
* **Faithfulness** transports the compatibility of `f` down to the ring level. The contravariance
  of `Spec.locallyRingedSpaceMap_comp` folds `Spec (stepRingHom I n) ≫ Spec (ofHom φ_{n+1})` into
  `Spec` of a single composite, and `stepRingHom I n` is `Ideal.Quotient.factorPow I
  (Nat.le_succ (n + 1))` on the nose — `stepRingHom` is `ofHom (Ideal.Quotient.factor …)` and
  `factorPow` is an `abbrev` for that same `factor` — so no composition lemma about `factorPow`
  is needed in between.
* **The level-`0` padding.** `existsUnique_thickeningMap_comp` wants a family indexed from `0`,
  while `f` supplies levels `≥ 1`; `R ⧸ I ^ 0` is the zero ring, so level `0` constrains nothing,
  but a term still has to be produced and there is no canonical map `B →+* R` to make one from.
  Padding *from level `1`*, `φ 0 := factorPow I (Nat.le_succ 0) ∘ φ 1`, makes the `n = 0`
  compatibility obligation hold by `rfl`. This is `AdicCompletionLimit.lean`'s `towerProjFamily`
  trick.

The index shift `IndSchemeLimitComponents.lean` documents is what makes the last step free:
`ringHomOfSpecHomTower I B f (n + 1)` reduces to `ringHomOfSpecHom I B f n`, which is exactly the
level `thickeningMap I n` sees.

## Non-vacuity

`existsUnique_thickeningMap_comp_of_specHom`'s hypothesis is a compatibility condition that could
in principle be unsatisfiable, so `specMap_comp_specMap_mk_comp` records that every ring
homomorphism `ψ : B →+* R` produces a compatible geometric family, by `Spec`-ing its reductions;
the closing `example` runs the theorem on it.

The other vacuity risk — that `[IsAdicRing I]` might only ever be instantiated at `I = ⊥`, where
every thickening is `Spec R` — is settled by the `2`-adic witness in the witness sections of
`FormalSchemes/IndSchemeExistence.lean` and `FormalSchemes/IndSchemeThickening.lean`. It is
deliberately not copied here: it is `private` in three files already, and a shared witness module
is due rather than a fourth copy.

## Scope

The `Equiv` packaging — between `Hom_{LRS}(Spf R, Spec B)` and the type of compatible geometric
families — is the natural next step and is not attempted; it needs a `structure` or `Subtype` for
the families, whose shape should be settled first. Naturality in `B` and the general non-affine
target `Hom_{LRS}(Spf R, X)` are the remaining open items on this arc.

The cocone condition `Spec (stepRingHom I n) ≫ thickeningMap I (n + 1) = thickeningMap I n` is
still absent from `FormalSchemes/Thickenings.lean` — only its two components are there — and is
not needed here, compatibility being phrased on the family `f` instead.

## Main results

* `FormalSpectrum.ringHomOfSpecHom` and `FormalSpectrum.specMap_ringHomOfSpecHom`: the ring
  homomorphism behind a morphism out of a thickening, and its computation rule.
* `FormalSpectrum.ringHomOfSpecHomTower` and
  `FormalSpectrum.factorPow_comp_ringHomOfSpecHomTower`: the compatible tower it assembles into.
* `FormalSpectrum.existsUnique_thickeningMap_comp_of_specHom`: **a compatible family of morphisms
  out of the thickenings comes from a unique morphism out of `Spf R`.**
* `FormalSpectrum.specMap_comp_specMap_mk_comp`: the hypothesis is satisfiable.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6 (10.6.3, 10.6.7).
* [The Stacks Project, Tag 0AI2](https://stacks.math.columbia.edu/tag/0AI2)
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

universe u

namespace FormalSpectrum

variable {R : Type u} [CommRing R] [TopologicalSpace R] (I : Ideal R) [IsAdicRing I]
variable (B : Type u) [CommRing B]
variable (f : ∀ n : ℕ, Spec.locallyRingedSpaceObj (CommRingCat.of (R ⧸ I ^ (n + 1))) ⟶
  Spec.locallyRingedSpaceObj (CommRingCat.of B))

/-! ### Fullness: the ring map behind a morphism out of a thickening -/

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The ring homomorphism a morphism out of the `n`-th thickening comes from.** `Spec` is full,
so `f n` is `Spec` of a map `B →+* R ⧸ I ^ (n + 1)`; this is that map, extracted with
`Functor.preimage` and unopped. -/
def ringHomOfSpecHom (n : ℕ) : B →+* R ⧸ I ^ (n + 1) :=
  (Spec.toLocallyRingedSpace.preimage (f n)).unop.hom

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The computation rule for `ringHomOfSpecHom`.** It is `Functor.map_preimage` verbatim:
`Spec.toLocallyRingedSpace.map p` is `Spec.locallyRingedSpaceMap p.unop` and `CommRingCat.ofHom
h.hom` is `h`, both definitionally, so no bridging is needed. -/
theorem specMap_ringHomOfSpecHom (n : ℕ) :
    Spec.locallyRingedSpaceMap (CommRingCat.ofHom (ringHomOfSpecHom I B f n)) = f n :=
  Spec.toLocallyRingedSpace.map_preimage (f n)

/-! ### Faithfulness: compatibility, transported to the ring level -/

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **Compatibility of the family `f`, read on the ring maps behind it.** The contravariant
`Spec.locallyRingedSpaceMap_comp` folds the composite into `Spec` of a single ring map, and
faithfulness of `Spec` then compares the two ring maps directly. -/
theorem factorPow_comp_ringHomOfSpecHom
    (hf : ∀ n : ℕ, Spec.locallyRingedSpaceMap (stepRingHom I n) ≫ f (n + 1) = f n) (n : ℕ) :
    (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1))).comp (ringHomOfSpecHom I B f (n + 1)) =
      ringHomOfSpecHom I B f n := by
  have h := hf n
  rw [← specMap_ringHomOfSpecHom I B f n, ← specMap_ringHomOfSpecHom I B f (n + 1),
    ← Spec.locallyRingedSpaceMap_comp] at h
  exact congrArg CommRingCat.Hom.hom
    (Quiver.Hom.op_inj (Spec.toLocallyRingedSpace.map_injective h))

/-! ### The tower, padded at level `0` -/

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The compatible tower of ring maps `B →+* R ⧸ Iⁿ` behind a compatible family of morphisms out
of the thickenings.** Level `0` is padded from level `1`: `R ⧸ I ^ 0` is the zero ring, so it
constrains nothing, but a term is still needed and there is no canonical `B →+* R` to build one
from. Padding this way makes the `n = 0` compatibility obligation hold by `rfl`. -/
def ringHomOfSpecHomTower : ∀ n : ℕ, B →+* R ⧸ I ^ n
  | 0 => (Ideal.Quotient.factorPow I (Nat.le_succ 0)).comp (ringHomOfSpecHom I B f 0)
  | (n + 1) => ringHomOfSpecHom I B f n

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The padded tower is compatible**, which is the hypothesis
`existsUnique_thickeningMap_comp` consumes. -/
theorem factorPow_comp_ringHomOfSpecHomTower
    (hf : ∀ n : ℕ, Spec.locallyRingedSpaceMap (stepRingHom I n) ≫ f (n + 1) = f n) (n : ℕ) :
    (Ideal.Quotient.factorPow I (Nat.le_succ n)).comp (ringHomOfSpecHomTower I B f (n + 1)) =
      ringHomOfSpecHomTower I B f n := by
  cases n with
  | zero => rfl
  | succ m => exact factorPow_comp_ringHomOfSpecHom I B f hf m

/-! ### The payload -/

/-- **`Spf R` is the colimit of its infinitesimal thickenings, as far as affine targets can see**
(EGA I, 10.6.7): a compatible family of morphisms `Spec (R ⧸ I ^ (n + 1)) ⟶ Spec B` comes from a
**unique** morphism `Spf R ⟶ Spec B` restricting to it.

Existence is `ringHomOfSpecHomTower` fed to `existsUnique_thickeningMap_comp`, whose own existence
half is completeness of `R`; uniqueness is `hom_ext_thickeningMap`
(`FormalSchemes/IndSchemeThickening.lean`), whose input is Hausdorffness of the `I`-adic topology.

Note the index convention: `thickeningMap I n` sees `f n`, a morphism out of
`Spec (R ⧸ I ^ (n + 1))`. -/
theorem existsUnique_thickeningMap_comp_of_specHom
    (hf : ∀ n : ℕ, Spec.locallyRingedSpaceMap (stepRingHom I n) ≫ f (n + 1) = f n) :
    ∃! g : locallyRingedSpaceObj I ⟶ Spec.locallyRingedSpaceObj (CommRingCat.of B),
      ∀ n : ℕ, thickeningMap I n ≫ g = f n := by
  obtain ⟨g, hg, huniq⟩ := existsUnique_thickeningMap_comp I B (ringHomOfSpecHomTower I B f)
    (factorPow_comp_ringHomOfSpecHomTower I B f hf)
  refine ⟨g, fun n => ?_, fun g' hg' => huniq g' fun n => ?_⟩
  · rw [hg n]
    exact specMap_ringHomOfSpecHom I B f n
  · rw [hg' n]
    exact (specMap_ringHomOfSpecHom I B f n).symm

/-! ### The hypothesis is satisfiable

`existsUnique_thickeningMap_comp_of_specHom` quantifies over compatible families, so it would say
nothing if none existed. Every ring homomorphism `ψ : B →+* R` supplies one, by `Spec`-ing its
reductions modulo the powers of `I`; this is the geometric shadow of
`FormalSchemes/IndSchemeExistence.lean`'s `factorPow_comp_mk_comp`. -/

omit [TopologicalSpace R] [IsAdicRing I] in
/-- **The reductions of a ring homomorphism `ψ : B →+* R` form a compatible geometric family.** -/
theorem specMap_comp_specMap_mk_comp (ψ : B →+* R) (n : ℕ) :
    Spec.locallyRingedSpaceMap (stepRingHom I n) ≫
        Spec.locallyRingedSpaceMap (CommRingCat.ofHom
          ((Ideal.Quotient.mk (I ^ (n + 1 + 1))).comp ψ)) =
      Spec.locallyRingedSpaceMap
        (CommRingCat.ofHom ((Ideal.Quotient.mk (I ^ (n + 1))).comp ψ)) := by
  rw [← Spec.locallyRingedSpaceMap_comp]
  exact congrArg
    (fun u : B →+* R ⧸ I ^ (n + 1) => Spec.locallyRingedSpaceMap (CommRingCat.ofHom u))
    (factorPow_comp_mk_comp I B ψ (n + 1))

/-- **The unique morphism `Spf R ⟶ Spec B` restricting to the reductions of `ψ : B →+* R`.** The
family is supplied explicitly: higher-order unification cannot solve `?f n` against the expression
spelled out in the statement. -/
example (ψ : B →+* R) :
    ∃! g : locallyRingedSpaceObj I ⟶ Spec.locallyRingedSpaceObj (CommRingCat.of B),
      ∀ n : ℕ, thickeningMap I n ≫ g = Spec.locallyRingedSpaceMap
        (CommRingCat.ofHom ((Ideal.Quotient.mk (I ^ (n + 1))).comp ψ)) :=
  existsUnique_thickeningMap_comp_of_specHom I B
    (fun n => Spec.locallyRingedSpaceMap
      (CommRingCat.ofHom ((Ideal.Quotient.mk (I ^ (n + 1))).comp ψ)))
    (specMap_comp_specMap_mk_comp I B ψ)

end FormalSpectrum

end
