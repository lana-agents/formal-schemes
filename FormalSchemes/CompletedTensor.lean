import FormalSchemes.AdicExtend
import FormalSchemes.RestrictedPowerSeries
import Mathlib.RingTheory.TensorProduct.Maps

set_option linter.style.header false

/-!
# The completed tensor product of adic algebras

For adic `R`-algebras `A` and `B` over a base `(R, I)`, the **completed tensor product**
`A ⊗̂_R B` is the `I`-adic completion of the ordinary tensor product `A ⊗_R B` (Bosch,
*Lectures on Formal and Rigid Geometry*, §7; EGA I, 10.7). It is the coordinate ring of the
fibre product `Spf A ×_{Spf R} Spf B`, and is the construction needed to express group
structures on formal schemes (comultiplications land in a completed tensor product) and, more
generally, fibre products of formal schemes.

With the design used throughout this development the construction is immediate: the completion
of any ring at a finitely generated ideal is a complete adic ring
(`AdicCompletion.isAdicRing_map`), so `A ⊗̂_R B` is an adic `R`-algebra with ideal of definition
the extension of `I`, and the universal property follows from the universal property of the
tensor product composed with the continuous-extension machinery of
`FormalSchemes/AdicExtend.lean`.

## Main definitions and results

* `CompletedTensorProduct R I A B`: the completed tensor product, i.e. `AdicCompletion` of
  `A ⊗[R] B` at the extension of `I`.
* `CompletedTensorProduct.isAdicRing`: it is a complete adic ring (for `I` finitely generated),
  so its formal spectrum is an affine formal scheme.
* `CompletedTensorProduct.inl`, `inr`: the canonical `R`-algebra maps from the two factors.
* `CompletedTensorProduct.lift`: the universal property (existence direction) — a pair of
  `R`-algebra maps into a complete adic `R`-algebra, whose images of `I` land in the ideal of
  definition, induces a map from the completed tensor product; `lift_inl`, `lift_inr` compute
  it on the factors.
* `CompletedTensorProduct.hom_ext`: the universal property (uniqueness direction) — two
  continuous ring homomorphisms out of `A ⊗̂_R B` agreeing on `inl` and `inr` are equal.
* `CompletedTensorProduct.map`: functoriality — a pair of `R`-algebra maps `A →ₐ A'`, `B →ₐ B'`
  induces `A ⊗̂_R B →+* A' ⊗̂_R B'`; `map_inl`, `map_inr` compute it on the factors.
* `CompletedTensorProduct.commEquiv`: the commutativity isomorphism `A ⊗̂_R B ≃+* B ⊗̂_R A`.
* `CompletedTensorProduct.unitEquiv`: the left unitor `R ⊗̂_R A ≃+* A` for a complete adic
  `R`-algebra `A`, absorbing the first factor.

## References

* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §7.
* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.7.
-/

noncomputable section

open Ideal TensorProduct

universe u

variable (R : Type u) [CommRing R] (I : Ideal R)
variable (A B : Type u) [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- The **completed tensor product** `A ⊗̂_R B` of two `R`-algebras, relative to the ideal `I`
of the base: the `I`-adic completion of `A ⊗[R] B`. -/
abbrev CompletedTensorProduct : Type u :=
  AdicCompletion (I.map (algebraMap R (A ⊗[R] B))) (A ⊗[R] B)

namespace CompletedTensorProduct

/-- The ideal of definition of the completed tensor product: the extension of `I`. -/
abbrev idealOfDefinition : Ideal (CompletedTensorProduct R I A B) :=
  (I.map (algebraMap R (A ⊗[R] B))).map
    (algebraMap (A ⊗[R] B) (CompletedTensorProduct R I A B))

/-- The completed tensor product is a complete adic ring, for `I` finitely generated; hence its
formal spectrum is an affine formal scheme. -/
theorem isAdicRing (hI : I.FG) : IsAdicRing (idealOfDefinition R I A B) :=
  AdicCompletion.isAdicRing_map _ (hI.map _)

/-- The canonical `R`-algebra map from the first factor. -/
def inl : A →ₐ[R] CompletedTensorProduct R I A B :=
  (IsScalarTower.toAlgHom R (A ⊗[R] B) (CompletedTensorProduct R I A B)).comp
    Algebra.TensorProduct.includeLeft

/-- The canonical `R`-algebra map from the second factor. -/
def inr : B →ₐ[R] CompletedTensorProduct R I A B :=
  (IsScalarTower.toAlgHom R (A ⊗[R] B) (CompletedTensorProduct R I A B)).comp
    Algebra.TensorProduct.includeRight

/-!
### The universal property (existence direction)
-/

section Lift

variable {R I A B}
variable {S : Type u} [CommRing S] [Algebra R S] (L : Ideal S) [IsAdicComplete L S]
variable (hIL : I.map (algebraMap R S) ≤ L)
variable (f : A →ₐ[R] S) (g : B →ₐ[R] S)

/-- The universal property of the **completed** tensor product, existence direction: two
`R`-algebra maps into a complete adic `R`-algebra `S` — complete for an ideal `L` containing
`I·S` — induce a ring homomorphism from `A ⊗̂_R B`, since the tensor-product map is continuous
for the `I`-adic topologies. -/
def lift : CompletedTensorProduct R I A B →+* S :=
  AdicCompletion.extendRingHom (I.map (algebraMap R (A ⊗[R] B))) L
    (Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _)).toRingHom
    (Ideal.map_algebraMap_pow_le_comap I L hIL (Algebra.TensorProduct.lift f g
      (fun _ _ => Commute.all _ _)))

theorem lift_of (x : A ⊗[R] B) :
    lift L hIL f g (AdicCompletion.of (I.map (algebraMap R (A ⊗[R] B))) (A ⊗[R] B) x) =
      Algebra.TensorProduct.lift f g (fun _ _ => Commute.all _ _) x :=
  AdicCompletion.extendRingHom_of _ _ _ _ x

theorem lift_tmul (a : A) (b : B) :
    lift L hIL f g (AdicCompletion.of (I.map (algebraMap R (A ⊗[R] B))) (A ⊗[R] B)
      (a ⊗ₜ[R] b)) = f a * g b := by
  rw [lift_of]
  exact Algebra.TensorProduct.lift_tmul _ _ _ a b

/-- The lift restricted to the first factor is `f`. -/
theorem lift_inl (a : A) : lift L hIL f g (inl R I A B a) = f a := by
  have h : inl R I A B a =
      AdicCompletion.of (I.map (algebraMap R (A ⊗[R] B))) (A ⊗[R] B) (a ⊗ₜ[R] (1 : B)) := by
    change algebraMap (A ⊗[R] B) (CompletedTensorProduct R I A B) (a ⊗ₜ[R] (1 : B)) = _
    rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [h, lift_tmul, map_one, mul_one]

/-- The lift restricted to the second factor is `g`. -/
theorem lift_inr (b : B) : lift L hIL f g (inr R I A B b) = g b := by
  have h : inr R I A B b =
      AdicCompletion.of (I.map (algebraMap R (A ⊗[R] B))) (A ⊗[R] B) ((1 : A) ⊗ₜ[R] b) := by
    change algebraMap (A ⊗[R] B) (CompletedTensorProduct R I A B) ((1 : A) ⊗ₜ[R] b) = _
    rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rw [h, lift_tmul, map_one, one_mul]

end Lift

/-!
### The universal property (uniqueness direction) and structural filtration

Two continuous ring homomorphisms out of `A ⊗̂_R B` that agree on the two factors agree. The
continuity hypotheses are phrased with the powers of the ideal of definition; the following
lemma bridges those to the module filtration `(I·(A⊗B)) ^ m • ⊤` used by
`AdicCompletion.hom_ext_of_continuous`, and makes the continuity of `lift`, `map` and the
commutativity isomorphism compose cleanly.
-/

section HomExt

variable {R I A B}

/-- The canonical map from the first factor is the completion map of `a ⊗ₜ 1`. -/
theorem inl_apply (a : A) :
    inl R I A B a =
      algebraMap (A ⊗[R] B) (CompletedTensorProduct R I A B) (a ⊗ₜ[R] (1 : B)) :=
  rfl

/-- The canonical map from the second factor is the completion map of `1 ⊗ₜ b`. -/
theorem inr_apply (b : B) :
    inr R I A B b =
      algebraMap (A ⊗[R] B) (CompletedTensorProduct R I A B) ((1 : A) ⊗ₜ[R] b) :=
  rfl

/-- The ideal of definition of the completed tensor product is the extension of `I` itself. -/
theorem idealOfDefinition_eq_map :
    idealOfDefinition R I A B = I.map (algebraMap R (CompletedTensorProduct R I A B)) := by
  change (I.map (algebraMap R (A ⊗[R] B))).map
    (algebraMap (A ⊗[R] B) (CompletedTensorProduct R I A B)) = _
  rw [Ideal.map_map]
  congr 1

/-- Membership in the powers of the ideal of definition, expressed through the module filtration
`(I·(A⊗B)) ^ m • ⊤` used by the completion API. -/
theorem mem_idealOfDefinition_pow_iff (m : ℕ) (x : CompletedTensorProduct R I A B) :
    x ∈ (idealOfDefinition R I A B) ^ m ↔
      x ∈ ((I.map (algebraMap R (A ⊗[R] B))) ^ m • ⊤ :
        Submodule (A ⊗[R] B) (CompletedTensorProduct R I A B)) := by
  rw [← Ideal.mem_map_pow_iff_mem_smul_top (I.map (algebraMap R (A ⊗[R] B))) m x, idealOfDefinition,
    Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Algebra.algebraMap_self, Ideal.map_id]

variable {S : Type u} [CommRing S] (L : Ideal S) [IsAdicComplete L S]

/-- **The universal property of the completed tensor product, uniqueness direction**: two
continuous ring homomorphisms out of `A ⊗̂_R B` into a complete adic ring — mapping the powers
of the ideal of definition into the powers of `L` — agreeing on the two canonical maps `inl`
and `inr` are equal (for `I` finitely generated). -/
theorem hom_ext (hI : I.FG) {F G : CompletedTensorProduct R I A B →+* S}
    (hF : ∀ (m : ℕ) (x : CompletedTensorProduct R I A B),
      x ∈ (idealOfDefinition R I A B) ^ m → F x ∈ L ^ m)
    (hG : ∀ (m : ℕ) (x : CompletedTensorProduct R I A B),
      x ∈ (idealOfDefinition R I A B) ^ m → G x ∈ L ^ m)
    (hl : ∀ a : A, F (inl R I A B a) = G (inl R I A B a))
    (hr : ∀ b : B, F (inr R I A B b) = G (inr R I A B b)) :
    F = G := by
  refine AdicCompletion.hom_ext_of_continuous _ L (hI.map _)
    (fun m x hx => hF m x ((mem_idealOfDefinition_pow_iff m x).mpr hx))
    (fun m x hx => hG m x ((mem_idealOfDefinition_pow_iff m x).mpr hx)) ?_
  intro x
  have key : F.comp (algebraMap (A ⊗[R] B) (CompletedTensorProduct R I A B)) =
      G.comp (algebraMap (A ⊗[R] B) (CompletedTensorProduct R I A B)) := by
    refine Algebra.TensorProduct.ringHom_ext ?_ ?_
    · refine RingHom.ext fun a => ?_
      simp only [RingHom.coe_comp, Function.comp_apply]
      change F (algebraMap (A ⊗[R] B) (CompletedTensorProduct R I A B) (a ⊗ₜ[R] (1 : B))) =
        G (algebraMap (A ⊗[R] B) (CompletedTensorProduct R I A B) (a ⊗ₜ[R] (1 : B)))
      rw [← inl_apply]
      exact hl a
    · refine RingHom.ext fun b => ?_
      simp only [RingHom.coe_comp, AlgHom.toRingHom_eq_coe, Function.comp_apply, RingHom.coe_coe]
      change F (algebraMap (A ⊗[R] B) (CompletedTensorProduct R I A B) ((1 : A) ⊗ₜ[R] b)) =
        G (algebraMap (A ⊗[R] B) (CompletedTensorProduct R I A B) ((1 : A) ⊗ₜ[R] b))
      rw [← inr_apply]
      exact hr b
  have hx2 := DFunLike.congr_fun key x
  simp only [RingHom.coe_comp, Function.comp_apply] at hx2
  have hconv : algebraMap (A ⊗[R] B) (CompletedTensorProduct R I A B) x =
      AdicCompletion.of (I.map (algebraMap R (A ⊗[R] B))) (A ⊗[R] B) x := by
    rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  rwa [hconv] at hx2

/-- The `lift` of the universal property is continuous: it maps the powers of the ideal of
definition into the powers of `L` (for `I` finitely generated). -/
theorem lift_mem_pow [Algebra R S] (hIL : I.map (algebraMap R S) ≤ L)
    (f : A →ₐ[R] S) (g : B →ₐ[R] S) (hI : I.FG) (m : ℕ)
    {x : CompletedTensorProduct R I A B} (hx : x ∈ (idealOfDefinition R I A B) ^ m) :
    lift L hIL f g x ∈ L ^ m := by
  rw [mem_idealOfDefinition_pow_iff] at hx
  exact AdicCompletion.extendRingHom_continuous _ L _ _ (hI.map _) m x hx

end HomExt

/-!
### Functoriality and the commutativity isomorphism
-/

section Functoriality

variable {R I A B}
variable {A' B' : Type u} [CommRing A'] [CommRing B'] [Algebra R A'] [Algebra R B']

/-- **Functoriality of the completed tensor product**: a pair of `R`-algebra homomorphisms
`f : A →ₐ[R] A'`, `g : B →ₐ[R] B'` induces a ring homomorphism `A ⊗̂_R B →+* A' ⊗̂_R B'`
(for `I` finitely generated), sending `inl a ↦ inl (f a)` and `inr b ↦ inr (g b)`. -/
def map (hI : I.FG) (f : A →ₐ[R] A') (g : B →ₐ[R] B') :
    CompletedTensorProduct R I A B →+* CompletedTensorProduct R I A' B' :=
  haveI : IsAdicComplete (idealOfDefinition R I A' B') (CompletedTensorProduct R I A' B') :=
    (isAdicRing R I A' B' hI).toIsAdicComplete
  lift (idealOfDefinition R I A' B') (le_of_eq (idealOfDefinition_eq_map).symm)
    ((inl R I A' B').comp f) ((inr R I A' B').comp g)

@[simp]
theorem map_inl (hI : I.FG) (f : A →ₐ[R] A') (g : B →ₐ[R] B') (a : A) :
    map hI f g (inl R I A B a) = inl R I A' B' (f a) := by
  haveI : IsAdicComplete (idealOfDefinition R I A' B') (CompletedTensorProduct R I A' B') :=
    (isAdicRing R I A' B' hI).toIsAdicComplete
  exact lift_inl _ _ _ _ a

@[simp]
theorem map_inr (hI : I.FG) (f : A →ₐ[R] A') (g : B →ₐ[R] B') (b : B) :
    map hI f g (inr R I A B b) = inr R I A' B' (g b) := by
  haveI : IsAdicComplete (idealOfDefinition R I A' B') (CompletedTensorProduct R I A' B') :=
    (isAdicRing R I A' B' hI).toIsAdicComplete
  exact lift_inr _ _ _ _ b

/-- The functorial map maps the powers of the ideal of definition into the powers of the ideal
of definition of the target (for `I` finitely generated) — continuity of `map`. -/
theorem map_mem_pow (hI : I.FG) (f : A →ₐ[R] A') (g : B →ₐ[R] B') (m : ℕ)
    {x : CompletedTensorProduct R I A B} (hx : x ∈ (idealOfDefinition R I A B) ^ m) :
    map hI f g x ∈ (idealOfDefinition R I A' B') ^ m := by
  haveI : IsAdicComplete (idealOfDefinition R I A' B') (CompletedTensorProduct R I A' B') :=
    (isAdicRing R I A' B' hI).toIsAdicComplete
  exact lift_mem_pow _ _ _ _ hI m hx

/-- The swap homomorphism `A ⊗̂_R B →+* B ⊗̂_R A` sending `inl a ↦ inr a` and `inr b ↦ inl b`
(for `I` finitely generated). -/
def commHom (hI : I.FG) :
    CompletedTensorProduct R I A B →+* CompletedTensorProduct R I B A :=
  haveI : IsAdicComplete (idealOfDefinition R I B A) (CompletedTensorProduct R I B A) :=
    (isAdicRing R I B A hI).toIsAdicComplete
  lift (idealOfDefinition R I B A) (le_of_eq (idealOfDefinition_eq_map).symm)
    (inr R I B A) (inl R I B A)

@[simp]
theorem commHom_inl (hI : I.FG) (a : A) :
    commHom (R := R) (I := I) (A := A) (B := B) hI (inl R I A B a) = inr R I B A a := by
  haveI : IsAdicComplete (idealOfDefinition R I B A) (CompletedTensorProduct R I B A) :=
    (isAdicRing R I B A hI).toIsAdicComplete
  exact lift_inl _ _ _ _ a

@[simp]
theorem commHom_inr (hI : I.FG) (b : B) :
    commHom (R := R) (I := I) (A := A) (B := B) hI (inr R I A B b) = inl R I B A b := by
  haveI : IsAdicComplete (idealOfDefinition R I B A) (CompletedTensorProduct R I B A) :=
    (isAdicRing R I B A hI).toIsAdicComplete
  exact lift_inr _ _ _ _ b

/-- The swap homomorphism maps the powers of the ideal of definition into the powers of the
ideal of definition of the target (for `I` finitely generated). -/
theorem commHom_mem_pow (hI : I.FG) (m : ℕ) {x : CompletedTensorProduct R I A B}
    (hx : x ∈ (idealOfDefinition R I A B) ^ m) :
    commHom (R := R) (I := I) (A := A) (B := B) hI x ∈ (idealOfDefinition R I B A) ^ m := by
  haveI : IsAdicComplete (idealOfDefinition R I B A) (CompletedTensorProduct R I B A) :=
    (isAdicRing R I B A hI).toIsAdicComplete
  exact lift_mem_pow _ _ _ _ hI m hx

/-- **The commutativity isomorphism** `A ⊗̂_R B ≃+* B ⊗̂_R A` (for `I` finitely generated),
exchanging the two factors. -/
def commEquiv (hI : I.FG) :
    CompletedTensorProduct R I A B ≃+* CompletedTensorProduct R I B A :=
  haveI hAB : IsAdicComplete (idealOfDefinition R I A B) (CompletedTensorProduct R I A B) :=
    (isAdicRing R I A B hI).toIsAdicComplete
  haveI hBA : IsAdicComplete (idealOfDefinition R I B A) (CompletedTensorProduct R I B A) :=
    (isAdicRing R I B A hI).toIsAdicComplete
  RingEquiv.ofRingHom
    (commHom (R := R) (I := I) (A := A) (B := B) hI)
    (commHom (R := R) (I := I) (A := B) (B := A) hI)
    (by
      refine hom_ext (idealOfDefinition R I B A) hI
        (fun m x hx => ?_) (fun m x hx => hx) (fun b => ?_) (fun a => ?_)
      · exact commHom_mem_pow hI m (commHom_mem_pow hI m hx)
      · simp
      · simp)
    (by
      refine hom_ext (idealOfDefinition R I A B) hI
        (fun m x hx => ?_) (fun m x hx => hx) (fun a => ?_) (fun b => ?_)
      · exact commHom_mem_pow hI m (commHom_mem_pow hI m hx)
      · simp
      · simp)

@[simp]
theorem commEquiv_inl (hI : I.FG) (a : A) :
    commEquiv (R := R) (I := I) (A := A) (B := B) hI (inl R I A B a) = inr R I B A a :=
  commHom_inl hI a

@[simp]
theorem commEquiv_inr (hI : I.FG) (b : B) :
    commEquiv (R := R) (I := I) (A := A) (B := B) hI (inr R I A B b) = inl R I B A b :=
  commHom_inr hI b

/-- The canonical map `inr` sends the powers of the ideal of definition of the second factor
`I·B` into the powers of the ideal of definition of `A ⊗̂_R B`. -/
theorem inr_mem_pow (m : ℕ) {b : B} (hb : b ∈ (I.map (algebraMap R B)) ^ m) :
    inr R I A B b ∈ (idealOfDefinition R I A B) ^ m := by
  have h1 : Ideal.map (inr R I A B).toRingHom (Ideal.map (algebraMap R B) I)
      = idealOfDefinition R I A B := by
    rw [Ideal.map_map, idealOfDefinition_eq_map]
    congr 1
    exact (inr R I A B).comp_algebraMap
  have hmem : (inr R I A B).toRingHom b
      ∈ Ideal.map (inr R I A B).toRingHom ((I.map (algebraMap R B)) ^ m) :=
    Ideal.mem_map_of_mem _ hb
  rw [Ideal.map_pow, h1] at hmem
  exact hmem

end Functoriality

/-!
### The left unitor

For a complete adic `R`-algebra `A` the first factor `R` is absorbed: `R ⊗̂_R A ≃+* A`. This is
the completed-tensor counterpart of `Algebra.TensorProduct.lid`, and is the isomorphism through
which the counit laws of a formal group (e.g. `Ĝm`, issue 67) are expressed.
-/

section Unitor

variable {R I A}
variable [IsAdicComplete (I.map (algebraMap R A)) A]

/-- The forward map of the left unitor `R ⊗̂_R A →+* A`, given by the universal property with
`R ↦ A` the structure map and `A ↦ A` the identity: `inl r ↦ algebraMap r`, `inr a ↦ a`. -/
def unitHom : CompletedTensorProduct R I R A →+* A :=
  lift (I.map (algebraMap R A)) le_rfl (Algebra.ofId R A) (AlgHom.id R A)

@[simp]
theorem unitHom_inl (r : R) : unitHom (R := R) (I := I) (A := A) (inl R I R A r)
    = algebraMap R A r :=
  lift_inl _ _ _ _ r

@[simp]
theorem unitHom_inr (a : A) : unitHom (R := R) (I := I) (A := A) (inr R I R A a) = a :=
  lift_inr _ _ _ _ a

/-- **The left unitor** `R ⊗̂_R A ≃+* A` (for `I` finitely generated and `A` complete), absorbing
the first factor `R`; the inverse is `inr`. -/
def unitEquiv (hI : I.FG) : CompletedTensorProduct R I R A ≃+* A :=
  haveI : IsAdicComplete (idealOfDefinition R I R A) (CompletedTensorProduct R I R A) :=
    (isAdicRing R I R A hI).toIsAdicComplete
  RingEquiv.ofRingHom
    unitHom
    (inr R I R A)
    (by ext a; simp)
    (by
      refine hom_ext (idealOfDefinition R I R A) hI
        (fun m x hx => inr_mem_pow m (lift_mem_pow _ _ _ _ hI m hx)) (fun m x hx => hx)
        (fun r => ?_) (fun a => ?_)
      · change inr R I R A (unitHom (inl R I R A r)) = inl R I R A r
        rw [unitHom_inl, AlgHom.commutes]
        exact ((inl R I R A).commutes r).symm
      · change inr R I R A (unitHom (inr R I R A a)) = inr R I R A a
        rw [unitHom_inr])

@[simp]
theorem unitEquiv_inl (hI : I.FG) (r : R) :
    unitEquiv (R := R) (I := I) (A := A) hI (inl R I R A r) = algebraMap R A r :=
  unitHom_inl r

@[simp]
theorem unitEquiv_inr (hI : I.FG) (a : A) :
    unitEquiv (R := R) (I := I) (A := A) hI (inr R I R A a) = a :=
  unitHom_inr a

end Unitor

end CompletedTensorProduct
