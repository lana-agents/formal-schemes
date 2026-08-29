import FormalSchemes.CofinalCompletion
import FormalSchemes.CofinalIdeal
import FormalSchemes.RestrictedPowerSeries

set_option linter.style.header false

/-!
# The cofinality isomorphism is an algebra isomorphism, and restricted power series only see the
topology

`AdicCompletion.cofinalRingEquiv` (`FormalSchemes.CofinalCompletion`) identifies the adic
completions of a ring at two cofinal ideals. It is built by the universal property of the
completion, so it arrives as a bare `RingEquiv`. This file upgrades it to an **algebra**
isomorphism over any base the ring is an algebra over, and applies that to the ring of restricted
power series: `R{X₁, …, Xₙ}` depends only on the topology of `R`, not on the ideal of definition
chosen to define it.

## The correction this file records

The naive expectation is that the resulting isomorphism carries
`RestrictedPowerSeries.idealOfDefinition R J₁ n` to the corresponding ideal for `J₂`.
**It does not, and cannot**: `idealOfDefinition R J n` is the extension of `J` itself
(`RestrictedPowerSeries.idealOfDefinition_eq_map`), so for `J₂ = J₁ ^ 2` the two ideals differ by a
square, exactly as `J₁` and `J₁ ^ 2` do. An isomorphism cannot repair that.

What is true, and what turns out to be all the transport of `IsTopologicallyFiniteType` needs, is
one degree weaker and is `Ideal.map_algebraMap_algHom` below: an `R`-algebra homomorphism carries
the extension of an ideal of `R` to the extension of *that same* ideal. Applied to
`RestrictedPowerSeries.cofinalAlgEquiv` it gives

```
Ideal.map σ.symm (J₂ · R{X}_{J₂}) = J₂ · R{X}_{J₁}
```

— the *same* ideal `J₂` of the base, extended into the *other* presenting ring. That is not
`idealOfDefinition R J₁ n`, and it does not need to be: the presentation of a tf-type algebra over
`(R, J₂)` asks for the image of `J₂ · R{X}`, and it is the base ideal that is fixed, not the ring.
See `FormalSchemes.CofinalTopFiniteType`.

## Main definitions and results

* `AdicCompletion.cofinalHom_algebraMap`: the cofinal comparison map commutes with the structural
  map out of any base of the ring. `AdicCompletion.cofinalHom_of`, the case of the ring itself,
  was already on the tree and has been moved beside `AdicCompletion.cofinalHom`.
* `AdicCompletion.cofinalAlgEquiv`: `AdicCompletion K S ≃ₐ[T] AdicCompletion L S` for cofinal `K`,
  `L`, over any base `T` of `S`.
* `Ideal.map_algebraMap_algHom`: an `R`-algebra map carries `J · A` to `J · B`, for `J` an ideal of
  the base `R`. General, and the only property of the cofinality isomorphism used downstream.
* `RestrictedPowerSeries.cofinalAlgEquiv`: `R{X₁, …, Xₙ}` for cofinal ideals of definition, as an
  `R`-algebra isomorphism.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.5, §10.13.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
-/

noncomputable section

universe u

/-! ### An `R`-algebra map fixes the base ideal it extends -/

/-- **An `R`-algebra homomorphism carries `J · A` to `J · B`.** For an ideal `J` of the base ring,
the extension of `J` to `A` maps onto the extension of `J` to `B`, because the two structural maps
agree after composing with `f` (`AlgHom.commutes`).

Elementary, and stated separately because it is the *whole* interface through which
`FormalSchemes.CofinalTopFiniteType` uses the cofinality isomorphism. Nothing about completions,
cofinality or finiteness enters. -/
theorem Ideal.map_algebraMap_algHom {R : Type u} [CommRing R] {A : Type u} [CommRing A]
    [Algebra R A] {B : Type u} [CommRing B] [Algebra R B] (f : A →ₐ[R] B) (J : Ideal R) :
    (J.map (algebraMap R A)).map f.toRingHom = J.map (algebraMap R B) := by
  rw [Ideal.map_map]
  congr 1
  exact RingHom.ext fun r => f.commutes r

namespace AdicCompletion

variable {S : Type u} [CommRing S] {K L : Ideal S}

variable {T : Type u} [CommRing T] [Algebra T S]

/-- The cofinal comparison map is a `T`-algebra map for any base `T` of `S`: the structural map
`T → AdicCompletion K S` factors through `S` (`AdicCompletion.algebraMap_apply`), and
`cofinalHom_of` handles the second leg. -/
theorem cofinalHom_algebraMap (hb : K ^ b ≤ L) (t : T) :
    cofinalHom hb (algebraMap T (AdicCompletion K S) t) = algebraMap T (AdicCompletion L S) t := by
  rw [algebraMap_apply, algebraMap_apply, cofinalHom_of]

/-- **Cofinal ideals have isomorphic adic completions, as algebras over any base of the ring.**
`AdicCompletion.cofinalRingEquiv` with its `commutes'` field supplied by
`AdicCompletion.cofinalHom_algebraMap`. -/
def cofinalAlgEquiv (hb : K ^ b ≤ L) (ha : L ^ a ≤ K) :
    AdicCompletion K S ≃ₐ[T] AdicCompletion L S :=
  AlgEquiv.ofRingEquiv (f := cofinalRingEquiv hb ha) (cofinalHom_algebraMap hb)

@[simp]
theorem cofinalAlgEquiv_apply (hb : K ^ b ≤ L) (ha : L ^ a ≤ K) (x : AdicCompletion K S) :
    (cofinalAlgEquiv (T := T) hb ha) x = cofinalHom hb x :=
  rfl

end AdicCompletion

/-! ### Restricted power series at cofinal ideals of definition -/

namespace RestrictedPowerSeries

variable (R : Type u) [CommRing R] {J₁ J₂ : Ideal R} (n : ℕ)

/-- **`R{X₁, …, Xₙ}` depends only on the topology of `R`.** For cofinal ideals `J₁`, `J₂` of `R`
the two restricted power series rings are isomorphic as `R`-algebras.

`RestrictedPowerSeries R J n` is by definition the completion of `R[X₁, …, Xₙ]` at the extension
of `J`; `Ideal.IsCofinal.map` says the two extensions are again cofinal, and
`AdicCompletion.cofinalAlgEquiv` does the rest. The exponents witnessing cofinality are chosen by
`Exists.choose`, which is why this is a `noncomputable def`; nothing downstream depends on which
witnesses are picked, since the only property used is `AlgEquiv.commutes`. -/
def cofinalAlgEquiv (h : J₁.IsCofinal J₂) :
    RestrictedPowerSeries R J₁ n ≃ₐ[R] RestrictedPowerSeries R J₂ n :=
  AdicCompletion.cofinalAlgEquiv
    (h.map (algebraMap R (MvPolynomial (Fin n) R))).1.choose_spec
    (h.map (algebraMap R (MvPolynomial (Fin n) R))).2.choose_spec

/-- **The transport of the ideal of definition, in its true form.** The inverse of the cofinality
isomorphism carries the extension of `J₂` into the `J₂`-presentation to the extension of `J₂` into
the `J₁`-presentation — the base ideal is unchanged, the presenting ring is not.

It is *not* true that `idealOfDefinition R J₂ n` maps to `idealOfDefinition R J₁ n`: those are the
extensions of two *different* ideals of `R`, and for `J₂ = J₁ ^ 2` they differ by a square. See
this file's module docstring. -/
theorem map_cofinalAlgEquiv_symm_idealOfDefinition (h : J₁.IsCofinal J₂) :
    Ideal.map (cofinalAlgEquiv R n h).symm.toAlgHom.toRingHom (idealOfDefinition R J₂ n) =
      J₂.map (algebraMap R (RestrictedPowerSeries R J₁ n)) := by
  rw [idealOfDefinition_eq_map]
  exact Ideal.map_algebraMap_algHom _ J₂

end RestrictedPowerSeries
