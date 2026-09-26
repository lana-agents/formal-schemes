import FormalSchemes.ChartedCompletionDatum
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.Noetherian

set_option linter.style.header false

/-!
# A scheme with a principal affine cover presents a completion datum

`AlgebraicGeometry.ChartedCompletionDatum` (`FormalSchemes.ChartedCompletionDatum`) is the input
of the arbitrary-index formal completion `..completionGlued`, and until now every value of it on
this tree was written out by hand: `..ofTwoPatch`, `projectiveLineDatum`
(`FormalSchemes.ProjectiveLineCompletion`) and `SpecThreeChartCover.completionDatum`
(`FormalSchemes.SpecThreeChartCompletion`), and nothing in the completion cluster took a `Scheme`
as input at all. This module produces a datum instead, from

* a scheme `X`, covered by affine opens whose pairwise overlaps are **basic opens of both charts**
  — `AlgebraicGeometry.PrincipalAffineCover` below, and the restriction is genuine: two affine
  opens of a scheme meet in an open that need not be a basic open of either, and the closest
  statement Mathlib has in that direction is `exists_basicOpen_le_affine_inter`, which produces a
  common basic open around **each point** of the overlap and not one cutting out the whole of it;
* an ideal sheaf on `X`, as `Scheme.IdealSheafData` — which is already *"an ideal per affine chart,
  compatible over the overlaps"*, and which a closed **subset** supplies through
  `Scheme.IdealSheafData.vanishingIdeal` and a closed **subscheme** through `Scheme.Hom.ker`.

`AlgebraicGeometry.PrincipalAffineCover.completionDatum` is the datum, and it is the first value of
`ChartedCompletionDatum` here that is not hand-built.

**Every field except `g` comes from one construction.** Two presentations of one open as a basic
open — `f` on the chart `U` and `f'` on the chart `V`, with `X.basicOpen f = X.basicOpen f'` — give
the same away localization, because each of `Localization.Away f` and `Localization.Away f'` is the
ring of sections over that one open. That is `AlgebraicGeometry.awayCongr` below, and
`AlgebraicGeometry.ChartedCompletionDatum`'s `θ`, `θ_symm`, `hθ`, `σ`, `hσθ` and `hσc` are all read
off it: `θ` and `σ` are two instances of it, at `g i j` and at `g i j * g i k`; `θ_symm` is
`..awayCongr_symm`; `hσc` is `..awayCongr_trans` and `..awayCongr_self`; `hθ` is
`Scheme.IdealSheafData.map_ideal_awayCongr`; and `hσθ` is the one field of that structure which
also needs the away-to-away maps of `IsLocalization.Away` identified with restrictions, which is
`..awayToAwayRight_eq_awayRestrict` and `..awayToAwayLeft_eq_awayRestrict`.

## Main results

* `AlgebraicGeometry.awayCongr`: the away localizations of two principal presentations of one open
  agree. Named `awayCongr` for the congruence it is; it is **not**
  `CompletedTensorAwayInterchange.awayCongrHom`, which varies the away element with the ring fixed
  and lives at the completions.
* `AlgebraicGeometry.awayRestrict`: the restriction between away localizations of nested opens,
  with `..awayRestrict_comp`. Its two identifications with `IsLocalization.Away.awayToAwayRight`
  and `IsLocalization.Away.awayToAwayLeft` are what `ChartedCompletionDatum`'s triple law `hσθ` is
  made of.
* `AlgebraicGeometry.Scheme.IdealSheafData.map_ideal_awayCongr`: an ideal sheaf's two chart-local
  ideals correspond under `awayCongr`. This is the datum's `hθ` and it is the only statement here
  about ideals.
* `AlgebraicGeometry.PrincipalAffineCover`: the input, and
  `..PrincipalAffineCover.completionDatum`: the datum.
* `AlgebraicGeometry.PrincipalAffineCover.ofSections`: a witness, for any affine `X` and any family
  of global sections whose basic opens cover it.
* `AlgebraicGeometry.PrincipalAffineCover.fg_ideal`: the datum's `hK` at a locally Noetherian `X`,
  which is the only supplier of that hypothesis on this tree.

## What is **not** proved here

* **Nothing identifies `ChartedCompletionDatum.specGlued` of `..completionDatum` with `X`.** The
  datum carries the chart rings and the away elements and nothing else, so its ambient scheme is
  glued from `Spec Γ(X, U i)` and *that it is `X`* is a theorem nobody has. The field
  `PrincipalAffineCover.covers` is **not used** by `..completionDatum` and is in the structure for
  exactly that successor: without it the object would be a principal *family* rather than a cover,
  and the comparison could not even be stated. The field is inert today.
* **So `ChartedCompletionDatum.completionGlued` of this datum is not yet `X_{/Z}`**, in the sense of
  EGA I 10.8 at a general `X`. It is the completion of the glued chart family along the ideal
  family, and the bridge to `X` is the previous bullet.
* **The general production is still refuted.** A datum cannot be produced from an arbitrary pair
  `(X, Z)`: the field `g` wants one element of `Γ(X, U i)` cutting out `U i ⊓ U j` exactly, at every
  ordered pair. `PrincipalAffineCover` **assumes** that, rather than supplying it, and whether every
  separated or quasi-projective scheme admits such a cover is open here. So the class presented is
  *pairs presented by a principal affine cover*, which is the class the three hand-built data
  already covered — what changes is that it is now witnessed by a production taking a scheme as
  input.
* **`projectiveLineDatum` is not reduced to `..completionDatum`.** It is built from abstract ring
  data through `ChartedCompletionDatum.ofTwoPatch`, not from a scheme, so the reduction needs the
  first bullet's comparison for `ℙ¹` first.
* **Nothing here says the chart ideals are independent.** `..ofSections` is a witness that the
  input is inhabited and it exercises `ChartedCompletionDatum`'s `θ`, `θ_symm` and `hθ` at distinct
  indices and that structure's `σ`, `hσθ` and `hσc` at distinct triples, but its charts are basic
  opens of one affine and its ideals all come from one `Scheme.IdealSheafData`; no witness on this
  tree has both independent chart ideals and non-vacuous triple fields.

## Placement

The file is a leaf: the reverse closure of `FormalSchemes.PrincipalCoverCompletionDatum` is **0**
and its forward closure is **52** modules. It has to be a new module rather than an addition to an
existing one, because it is the first thing under `FormalSchemes/` to use `Scheme.IdealSheafData`
outside `FormalSchemes.ThickeningTowerKernel` — which uses it for the quasi-coherence of a kernel
and is not about completions — and the first to use `Scheme.affineOpens` at all.

Two of the declarations here are general and are kept local deliberately.
`CategoryTheory.Functor.map_eq_of_isThin` says that a functor out of a thin category cannot
separate two parallel morphisms, which is what the three places in this file that compare two
restrictions of sections over one pair of opens ask for; `inf_inf_inf_swap` is the lattice identity
behind `..PrincipalAffineCover.tripleEq`. Both are stated at the hypotheses their proofs actually
use, `[Quiver.IsThin C]` and `[SemilatticeInf α]`, so each is a Mathlib-shaped statement in
Mathlib's own generality; neither has a module on this tree whose subject it is, and this tree has
no mirror directory for such statements. They are offered upward rather than defended here.

-/

universe u v u' v'

/-- **The three pairwise meets of a triple, read from two of its three corners.** -/
theorem inf_inf_inf_swap {α : Type*} [SemilatticeInf α] (a b c : α) :
    (a ⊓ b) ⊓ (a ⊓ c) = (b ⊓ c) ⊓ (b ⊓ a) := by
  simp [inf_comm, inf_left_comm]

namespace CategoryTheory.Functor

/-- **A functor out of a thin category cannot separate two parallel morphisms.** -/
theorem map_eq_of_isThin {C : Type u} [Category.{v} C] [Quiver.IsThin C] {D : Type u'}
    [Category.{v'} D] (F : C ⥤ D) {A B : C} (α β : A ⟶ B) : F.map α = F.map β := by
  congr 1
  exact Subsingleton.elim _ _

end CategoryTheory.Functor

open CategoryTheory

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### Two presentations of one open -/

/-- **Equal opens have the same sections.** -/
noncomputable def Scheme.sectionsCongr (X : Scheme.{u}) {A B : X.Opens} (h : A = B) :
    Γ(X, A) ≃+* Γ(X, B) :=
  (X.presheaf.mapIso (eqToIso h.symm).op).commRingCatIsoToRingEquiv

@[simp] theorem Scheme.sectionsCongr_rfl (X : Scheme.{u}) {A : X.Opens} :
    X.sectionsCongr (rfl : A = A) = RingEquiv.refl _ := by
  ext x
  change (X.presheaf.map (eqToHom (rfl : A = A)).op).hom x = x
  simp

theorem Scheme.sectionsCongr_trans (X : Scheme.{u}) {A B C : X.Opens} (h : A = B) (h' : B = C) :
    (X.sectionsCongr h).trans (X.sectionsCongr h') = X.sectionsCongr (h.trans h') := by
  subst h
  subst h'
  ext x
  simp

theorem Scheme.sectionsCongr_symm (X : Scheme.{u}) {A B : X.Opens} (h : A = B) :
    (X.sectionsCongr h).symm = X.sectionsCongr h.symm := by
  subst h
  ext x
  simp

/-- **`Localization.Away f` is the ring of sections over `D(f)`**, for a section `f` on an affine
open. This is `IsAffineOpen.isLocalization_basicOpen` read as a `RingEquiv`. -/
noncomputable def awaySectionsEquiv (U : X.affineOpens) (f : Γ(X, U.1)) :
    Localization.Away f ≃+* Γ(X, X.basicOpen f) :=
  letI := U.2.isLocalization_basicOpen f
  (IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f)
    Γ(X, X.basicOpen f)).toRingEquiv

theorem awaySectionsEquiv_algebraMap (U : X.affineOpens) (f x : Γ(X, U.1)) :
    awaySectionsEquiv U f (algebraMap (Γ(X, U.1) : Type u) (Localization.Away f) x) =
      (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom x := by
  letI := U.2.isLocalization_basicOpen f
  exact (IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f)
    Γ(X, X.basicOpen f)).commutes x

theorem awaySectionsEquiv_symm_algebraMap (U : X.affineOpens) (f x : Γ(X, U.1)) :
    (awaySectionsEquiv U f).symm ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom x) =
      algebraMap (Γ(X, U.1) : Type u) (Localization.Away f) x := by
  rw [← awaySectionsEquiv_algebraMap U f x, RingEquiv.symm_apply_apply]

/-- **Two principal presentations of one open have the same away localization.**

Both `Localization.Away f` and `Localization.Away f'` are the sections over that open, by
`awaySectionsEquiv`, so the two are identified with nothing to prove. This is not
`CompletedTensorAwayInterchange.awayCongrHom`, which varies the away element with the ring fixed
and lands at the completions. -/
noncomputable def awayCongr {U V : X.affineOpens} (f : Γ(X, U.1)) (f' : Γ(X, V.1))
    (h : X.basicOpen f = X.basicOpen f') :
    Localization.Away f ≃+* Localization.Away f' :=
  (awaySectionsEquiv U f).trans
    ((X.sectionsCongr h).trans (awaySectionsEquiv V f').symm)

theorem awayCongr_self (U : X.affineOpens) (f : Γ(X, U.1))
    (h : X.basicOpen f = X.basicOpen f) : awayCongr f f h = RingEquiv.refl _ := by
  ext x
  simp [awayCongr]

theorem awayCongr_trans {U V W : X.affineOpens} (f : Γ(X, U.1)) (f' : Γ(X, V.1))
    (f'' : Γ(X, W.1)) (h : X.basicOpen f = X.basicOpen f')
    (h' : X.basicOpen f' = X.basicOpen f'') :
    (awayCongr f f' h).trans (awayCongr f' f'' h') = awayCongr f f'' (h.trans h') := by
  ext x
  simp only [awayCongr, RingEquiv.trans_apply, RingEquiv.apply_symm_apply]
  rw [← X.sectionsCongr_trans h h']
  rfl

theorem awayCongr_symm {U V : X.affineOpens} (f : Γ(X, U.1)) (f' : Γ(X, V.1))
    (h : X.basicOpen f = X.basicOpen f') :
    (awayCongr f f' h).symm = awayCongr f' f h.symm := by
  refine RingEquiv.symm_bijective.injective ?_
  ext x
  simp only [RingEquiv.symm_symm, awayCongr, RingEquiv.trans_apply, RingEquiv.symm_trans_apply,
    Scheme.sectionsCongr_symm]

/-! ### The restriction between away localizations -/

/-- **The restriction `Localization.Away f ⟶ Localization.Away f'` for `D(f') ⊆ D(f)`**, read
through the sections over the two opens. -/
noncomputable def awayRestrict {U V : X.affineOpens} (f : Γ(X, U.1)) (f' : Γ(X, V.1))
    (h : X.basicOpen f' ≤ X.basicOpen f) : Localization.Away f →+* Localization.Away f' :=
  (awaySectionsEquiv V f').symm.toRingHom.comp
    ((X.presheaf.map (homOfLE h).op).hom.comp (awaySectionsEquiv U f).toRingHom)

theorem awayCongr_toRingHom {U V : X.affineOpens} (f : Γ(X, U.1)) (f' : Γ(X, V.1))
    (h : X.basicOpen f = X.basicOpen f') :
    (awayCongr f f' h).toRingHom = awayRestrict f f' h.ge := by
  change (awaySectionsEquiv V f').symm.toRingHom.comp
      ((X.presheaf.map (eqToHom h.symm).op).hom.comp (awaySectionsEquiv U f).toRingHom) = _
  rw [awayRestrict, X.presheaf.map_eq_of_isThin (eqToHom h.symm).op (homOfLE h.ge).op]

theorem awayRestrict_comp {U V W : X.affineOpens} (f : Γ(X, U.1)) (f' : Γ(X, V.1))
    (f'' : Γ(X, W.1)) (h : X.basicOpen f' ≤ X.basicOpen f)
    (h' : X.basicOpen f'' ≤ X.basicOpen f') :
    (awayRestrict f' f'' h').comp (awayRestrict f f' h) = awayRestrict f f'' (h'.trans h) := by
  ext x
  simp only [awayRestrict, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, RingEquiv.apply_symm_apply]
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp,
    X.presheaf.map_eq_of_isThin ((homOfLE h).op ≫ (homOfLE h').op) (homOfLE (h'.trans h)).op]

theorem basicOpen_mul_le_left (U : X.affineOpens) (a b : Γ(X, U.1)) :
    X.basicOpen (a * b) ≤ X.basicOpen a := by
  rw [Scheme.basicOpen_mul]
  exact inf_le_left

theorem basicOpen_mul_le_right (U : X.affineOpens) (a b : Γ(X, U.1)) :
    X.basicOpen (a * b) ≤ X.basicOpen b := by
  rw [Scheme.basicOpen_mul]
  exact inf_le_right

theorem awayToAwayRight_eq_awayRestrict (U : X.affineOpens) (a b : Γ(X, U.1)) :
    IsLocalization.Away.awayToAwayRight a b (P := Localization.Away (a * b)) =
      awayRestrict a (a * b) (basicOpen_mul_le_left U a b) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers a) (RingHom.ext fun r => ?_)
  simp only [RingHom.comp_apply, IsLocalization.Away.awayToAwayRight_eq, awayRestrict,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, awaySectionsEquiv_algebraMap,
    ← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rw [X.presheaf.map_eq_of_isThin ((homOfLE (X.basicOpen_le a)).op ≫ _)
    (homOfLE (X.basicOpen_le (a * b))).op, awaySectionsEquiv_symm_algebraMap]

theorem awayToAwayLeft_eq_awayRestrict (U : X.affineOpens) (a b : Γ(X, U.1)) :
    IsLocalization.Away.awayToAwayLeft a b (P := Localization.Away (b * a)) =
      awayRestrict a (b * a) (basicOpen_mul_le_right U b a) := by
  refine IsLocalization.ringHom_ext (Submonoid.powers a) (RingHom.ext fun r => ?_)
  simp only [RingHom.comp_apply, IsLocalization.Away.awayToAwayLeft_eq, awayRestrict,
    RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, awaySectionsEquiv_algebraMap,
    ← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rw [X.presheaf.map_eq_of_isThin ((homOfLE (X.basicOpen_le a)).op ≫ _)
    (homOfLE (X.basicOpen_le (b * a))).op, awaySectionsEquiv_symm_algebraMap]

/-! ### The chart-local ideals of an ideal sheaf -/

/-- **An ideal sheaf's two chart-local ideals correspond under `awayCongr`.**

This is the `hθ` field of `ChartedCompletionDatum`, and the only statement here about ideals. The
two outer legs are `Scheme.IdealSheafData.map_ideal_basicOpen`, which applies on the nose because
`algebraMap Γ(X, U.1) Γ(X, X.basicOpen f)` **is** the presheaf restriction; the middle leg is
`Scheme.IdealSheafData.map_ideal'`, which takes an arbitrary morphism of opens and so accepts the
one `Scheme.sectionsCongr` is built from. -/
theorem Scheme.IdealSheafData.map_ideal_awayCongr (I : X.IdealSheafData) {U V : X.affineOpens}
    (f : Γ(X, U.1)) (f' : Γ(X, V.1)) (h : X.basicOpen f = X.basicOpen f') :
    ((I.ideal U).map (algebraMap (Γ(X, U.1) : Type u) (Localization.Away f))).map
        (awayCongr f f' h).toRingHom =
      (I.ideal V).map (algebraMap (Γ(X, V.1) : Type u) (Localization.Away f')) := by
  have hsplit : (awayCongr f f' h).toRingHom =
      (awaySectionsEquiv V f').symm.toRingHom.comp
        ((X.sectionsCongr h).toRingHom.comp (awaySectionsEquiv U f).toRingHom) := rfl
  have step1 : ((I.ideal U).map (algebraMap (Γ(X, U.1) : Type u)
      (Localization.Away f))).map (awaySectionsEquiv U f).toRingHom =
      I.ideal (X.affineBasicOpen f) := by
    rw [Ideal.map_map, show (awaySectionsEquiv U f).toRingHom.comp
        (algebraMap (Γ(X, U.1) : Type u) (Localization.Away f)) =
        (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom from
      RingHom.ext fun x => awaySectionsEquiv_algebraMap U f x]
    exact I.map_ideal_basicOpen U f
  have step2 : (I.ideal (X.affineBasicOpen f)).map (X.sectionsCongr h).toRingHom =
      I.ideal (X.affineBasicOpen f') :=
    I.map_ideal' (U := X.affineBasicOpen f') (V := X.affineBasicOpen f) _
  have step3 : (I.ideal V).map (algebraMap (Γ(X, V.1) : Type u) (Localization.Away f')) =
      (I.ideal (X.affineBasicOpen f')).map (awaySectionsEquiv V f').symm.toRingHom := by
    rw [show algebraMap (Γ(X, V.1) : Type u) (Localization.Away f') =
        (awaySectionsEquiv V f').symm.toRingHom.comp
          (X.presheaf.map (homOfLE (X.basicOpen_le f')).op).hom from
      RingHom.ext fun x => (awaySectionsEquiv_symm_algebraMap V f' x).symm, ← Ideal.map_map]
    exact congrArg _ (I.map_ideal_basicOpen V f')
  rw [hsplit, ← Ideal.map_map, ← Ideal.map_map, step1, step3]
  exact congrArg _ step2

/-! ### The cover, and the datum -/

/-- **An affine open cover of `X` whose pairwise overlaps are basic opens of both charts.**

This is what `ChartedCompletionDatum` asks of a scheme and an arbitrary affine cover does not
supply: two affine opens meet in an open that need not be a basic open of either. The field
`PrincipalAffineCover.covers` is not used by `..completionDatum`; it is what an identification of
the glued ambient scheme with `X` would need, and it is what makes this a cover rather than a
family. It is spelled as the `iSup` rather than through `Scheme.AffineOpenCover` because that is
the shape `Scheme.IdealSheafData.le_of_iSup_eq_top` takes, which is how an ideal sheaf is pinned
down by its values on a cover. -/
structure PrincipalAffineCover (X : Scheme.{u}) where
  /-- The index type of the charts. -/
  J : Type u
  /-- The charts. -/
  U : J → X.affineOpens
  /-- The element of the `i`-th chart cutting out the overlap with the `j`-th. -/
  g : ∀ (i : J), J → Γ(X, (U i).1)
  /-- The overlap of the `i`-th chart with the `j`-th is cut out by `g i j`. -/
  hg : ∀ i j : J, X.basicOpen (g i j) = (U i).1 ⊓ (U j).1
  /-- The charts cover `X`. -/
  covers : ⨆ i, (U i).1 = ⊤

namespace PrincipalAffineCover

variable (D : PrincipalAffineCover X)

/-- **The two charts cut out the same overlap**, which is what `θ` needs. -/
theorem overlapEq (i j : D.J) : X.basicOpen (D.g i j) = X.basicOpen (D.g j i) := by
  rw [D.hg i j, D.hg j i, inf_comm]

/-- **The two charts cut out the same triple overlap**, which is what `σ` needs. -/
theorem tripleEq (i j k : D.J) :
    X.basicOpen (D.g i j * D.g i k) = X.basicOpen (D.g j k * D.g j i) := by
  rw [Scheme.basicOpen_mul, Scheme.basicOpen_mul, D.hg i j, D.hg i k, D.hg j k, D.hg j i,
    inf_inf_inf_swap]

/-- **The chart ideals of an ideal sheaf are finitely generated at a locally Noetherian scheme.**

This is the `hK` hypothesis of `..completionDatum`, and Mathlib has no finiteness predicate on
`Scheme.IdealSheafData` itself. -/
theorem fg_ideal [IsLocallyNoetherian X] (I : X.IdealSheafData) (i : D.J) :
    (I.ideal (D.U i)).FG :=
  (IsLocallyNoetherian.component_noetherian (D.U i)).noetherian _

/-- **A scheme with a principal affine cover and an ideal sheaf presents a completion datum.**

The first `ChartedCompletionDatum` on this tree produced from a scheme rather than written out. It
does **not** come with `ChartedCompletionDatum.specGlued ≅ X`, so `..completionGlued` of it is not
yet `X_{/Z}`; see this module's `What is not proved here`. -/
noncomputable def completionDatum (I : X.IdealSheafData)
    (hK : ∀ i, (I.ideal (D.U i)).FG) : ChartedCompletionDatum.{u} where
  J := D.J
  C := fun i => Γ(X, (D.U i).1)
  K := fun i => I.ideal (D.U i)
  hK := hK
  g := D.g
  θ := fun i j _ => awayCongr (D.g i j) (D.g j i) (D.overlapEq i j)
  θ_symm := fun i j _ => by rw [awayCongr_symm]
  hθ := fun i j _ => I.map_ideal_awayCongr (D.g i j) (D.g j i) (D.overlapEq i j)
  σ := fun i j k _ _ _ =>
    awayCongr (D.g i j * D.g i k) (D.g j k * D.g j i) (D.tripleEq i j k)
  hσθ := fun i j k _ _ _ => by
    rw [awayCongr_symm, awayCongr_symm, awayCongr_toRingHom, awayCongr_toRingHom,
      awayToAwayLeft_eq_awayRestrict (D.U j) (D.g j i) (D.g j k),
      awayToAwayRight_eq_awayRestrict (D.U i) (D.g i j) (D.g i k),
      awayRestrict_comp, awayRestrict_comp]
  hσc := fun i j k _ _ _ => by
    rw [awayCongr_trans, awayCongr_trans, awayCongr_self]

/-- **An affine scheme covered by the basic opens of a family of global sections** is a principal
affine cover, since `D(e i) ⊓ D(e j) = D(e j|_{D(e i)})`.

This is the witness that the input is inhabited. Its charts are basic opens of one affine and its
chart ideals therefore all come from one `Scheme.IdealSheafData` on that affine; it exercises
`ChartedCompletionDatum`'s `θ`, `θ_symm` and `hθ` at distinct indices, and that structure's `σ`,
`hσθ` and `hσc` at distinct triples, but it is not a witness of independent chart ideals. -/
noncomputable def ofSections (X : Scheme.{u}) [IsAffine X] {J : Type u}
    (e : J → Γ(X, (⊤ : X.Opens))) (he : ⨆ j, X.basicOpen (e j) = ⊤) :
    PrincipalAffineCover X where
  J := J
  U := fun i => ⟨X.basicOpen (e i), (isAffineOpen_top X).basicOpen (e i)⟩
  g := fun i j => (X.presheaf.map (homOfLE (X.basicOpen_le (e i))).op).hom (e j)
  hg := fun _ _ => by simp
  covers := he

end PrincipalAffineCover

end AlgebraicGeometry
