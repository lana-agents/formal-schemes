import FormalSchemes.ActionTranslates
import FormalSchemes.ActionQuotientInvariantSections
import FormalSchemes.DisjointGluing

set_option linter.style.header false

/-!
# The invariant extension of a section from a separating open

This is the geometric step of "the quotient of a formal scheme by a free, properly discontinuous
action is a formal scheme". Everything around it is built:
`FormalSchemes.ActionQuotientInvariantSections` says the sections of the quotient over `V` are the
sections of `X` over `π⁻¹ V` invariant under the action, and
`FormalSchemes.ActionQuotientFormalScheme` says the quotient is a formal scheme once the stalk maps
of `π` are isomorphisms. What was missing is the construction that produces invariant sections, and
that is what proper discontinuity is for:

> if `V ≤ U` with `U` separating, then `π⁻¹(π '' V)` is the **disjoint** union of the translates
> `(a g)⁻¹ V`, so an arbitrary section `s` of `𝒪_X` over `V` extends — uniquely — to the section of
> `𝒪_X` over `π⁻¹(π '' V)` that is `(a g)^* s` on the `g`-th translate, and that extension is
> invariant.

Disjointness is what makes the extension free of any compatibility condition
(`TopCat.Sheaf.existsUnique_gluing_of_disjoint'`), and it is also what makes it unique, which is
how invariance is proved: `(a k)^*` of the extension restricts to `(a (h*k))^* s` on the `h*k`-th
translate, so it is *another* gluing of the same family, hence equal to the extension.

## The transports, and how they are kept to one

Two opens that are equal but not definitionally so appear once: `(a k)⁻¹ ((a h)⁻¹ V)` versus
`(a (h*k))⁻¹ V`. They are equal because `(a (h*k)).hom = (a k).hom ≫ (a h).hom`, an equality of
*morphisms*, so `c_app_comp_of_eq` states the comparison with that morphism equality as a
**hypothesis binder** and discharges it by `subst`; the resulting `eqToHom` is then absorbed by
`presheaf_map_congr`, every two restriction maps between the same pair of opens being equal because
`Opens` is a thin category. This is the device recorded for `FormalSchemes.ActionQuotientSections`,
applied to a morphism rather than to an open.

## Main results

* `AlgebraicGeometry.LocallyRingedSpace.translateSection`: the section `(a g)^* s` on the `g`-th
  translate.
* `AlgebraicGeometry.LocallyRingedSpace.existsUnique_invariantExtension`: the extension exists and
  is unique.
* `AlgebraicGeometry.LocallyRingedSpace.exists_invariant_extension`: the extension restricts to `s`
  and is invariant — the form the descent criterion consumes.

## References

* [Grothendieck, *Éléments de géométrie algébrique I*][EGA1], Ch. I, §10.6.
* [Bosch, *Lectures on Formal and Rigid Geometry*, LNM 2105], §9.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace Opposite

universe v u

namespace AlgebraicGeometry

namespace LocallyRingedSpace

variable {X : LocallyRingedSpace.{u}}

/-! ### Restriction maps and comparison maps -/

/-- **Any two restriction maps between the same pair of opens agree**, `Opens` being a thin
category. Every transport in this file is discharged by this lemma. -/
theorem presheaf_map_congr {Z : TopCat.{u}} (F : (Opens Z)ᵒᵖ ⥤ CommRingCat.{u})
    {A B : (Opens Z)ᵒᵖ} (i j : A ⟶ B) : F.map i = F.map j :=
  congrArg F.map (Quiver.Hom.unop_inj (Subsingleton.elim i.unop j.unop))

/-- Two successive restrictions are the restriction along the composite. -/
theorem presheaf_map_comp_apply {Z : TopCat.{u}} (F : (Opens Z)ᵒᵖ ⥤ CommRingCat.{u})
    {A B C : (Opens Z)ᵒᵖ} (i : A ⟶ B) (j : B ⟶ C) (t : ToType (F.obj A)) :
    (F.map j) ((F.map i) t) = (F.map (i ≫ j)) t :=
  (ConcreteCategory.comp_apply _ _ t).symm.trans (by rw [← F.map_comp])

/-- **Naturality of the comparison map of a morphism of locally ringed spaces**, read on
elements: restricting downstairs and then pulling back is pulling back and then restricting. -/
theorem c_app_naturality {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) {A B : Opens Y.toTopCat}
    (i : A ⟶ B) (s : ToType (Y.presheaf.obj (op B))) :
    (f.toShHom.hom.c.app (op A)) (Y.presheaf.map i.op s) =
      X.presheaf.map ((Opens.map f.toShHom.hom.base).map i).op (f.toShHom.hom.c.app (op B) s) :=
  (ConcreteCategory.comp_apply _ _ s).symm.trans
    ((ConcreteCategory.congr_hom (f.toShHom.hom.c.naturality i.op) s).trans
      (ConcreteCategory.comp_apply _ _ s))

/-- **A morphism that factors as a composite pulls sections back in two steps.** The factorisation
is a *hypothesis*, not a definitional identity, so that `subst` discharges the `eqToHom`; this is
the one place in the file where two equal-but-not-definitionally-equal opens meet. -/
theorem c_app_comp_of_eq {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {φ : X ⟶ Z}
    (hφ : φ = f ≫ g) (V : Opens Z.toTopCat) (s : ToType (Z.presheaf.obj (op V))) :
    (φ.toShHom.hom.c.app (op V)) s =
      X.presheaf.map (eqToHom (congrArg
          (fun m : X ⟶ Z => op ((Opens.map m.toShHom.hom.base).obj V)) hφ.symm))
        (((f.toShHom.hom.c.app (op ((Opens.map g.toShHom.hom.base).obj V)))
          ((g.toShHom.hom.c.app (op V)) s) :
            ToType (X.presheaf.obj (op ((Opens.map (f ≫ g).toShHom.hom.base).obj V))))) := by
  subst hφ
  have h : (f ≫ g).toShHom.hom.c.app (op V) =
      g.toShHom.hom.c.app (op V) ≫
        f.toShHom.hom.c.app (op ((Opens.map g.toShHom.hom.base).obj V)) :=
    PresheafedSpace.comp_c_app _ _ _
  refine ((ConcreteCategory.congr_hom h s).trans (ConcreteCategory.comp_apply _ _ s)).trans ?_
  simp
  rfl

/-! ### The prescribed section on a translate -/

variable {G : Type v} [Group G] {a : G →* Aut X}

/-- **The section prescribed on the `g`-th translate**: the pullback of `s` along `a g`. -/
def translateSection (a : G →* Aut X) {V : Opens X.toTopCat}
    (s : ToType (X.presheaf.obj (op V))) (g : G) :
    ToType (X.presheaf.obj (op (translate a V g))) :=
  (a g).hom.toShHom.hom.c.app (op V) s

/-- `translateSection` unfolded, for rewriting. -/
theorem translateSection_def {V : Opens X.toTopCat} (s : ToType (X.presheaf.obj (op V)))
    (g : G) : translateSection a s g = (a g).hom.toShHom.hom.c.app (op V) s :=
  rfl

/-- On the `1`-st translate — which is `V` itself — the prescribed section is `s`, up to the
transport of opens. -/
theorem translateSection_one {V : Opens X.toTopCat} (s : ToType (X.presheaf.obj (op V))) :
    translateSection a s (1 : G) =
      X.presheaf.map (eqToHom (congrArg op (translate_one (a := a) V).symm)) s :=
  c_app_eq_of_eq_id V (φ := (a (1 : G)).hom) (by rw [map_one]; rfl)
    (translate_one (a := a) V).symm s

/-- **The prescribed sections are compatible with the action.** Pulling `translateSection a s h`
back along `a k` gives `translateSection a s (h * k)`, transported along `translate_translate`.
This is `c_app_comp_of_eq` at `(a (h * k)).hom = (a k).hom ≫ (a h).hom`. -/
theorem c_app_translateSection {V : Opens X.toTopCat} (s : ToType (X.presheaf.obj (op V)))
    (h k : G) :
    translateSection a s (h * k) =
      X.presheaf.map (eqToHom (congrArg op (translate_translate (a := a) V h k)))
        ((a k).hom.toShHom.hom.c.app (op (translate a V h)) (translateSection a s h)) := by
  refine (c_app_comp_of_eq (a k).hom (a h).hom (by rw [map_mul]; rfl) V s).trans ?_
  exact ConcreteCategory.congr_hom (presheaf_map_congr X.presheaf _ _) _

/-! ### Invariant sections -/

/-- **A section over `W` is invariant** when pulling it back along every `a k` returns it. The
equality of opens `W = (a k)⁻¹ W` is a *hypothesis binder*, not a fixed proof term, so the
predicate is discharged from whichever proof of it the caller has —
`CategoryTheory.preimage_actionQuotientπ_eq` for a saturated open, `translate_translate` for a
translate. -/
def IsInvariantSection (a : G →* Aut X) {W : Opens X.toTopCat}
    (r : ToType (X.presheaf.obj (op W))) : Prop :=
  ∀ (k : G) (hk : W = (Opens.map (a k).hom.toShHom.hom.base).obj W),
    (a k).hom.toShHom.hom.c.app (op W) r = X.presheaf.map (eqToHom (congrArg op hk)) r

/-! ### The extension -/

/-- **A section on `V ≤ U` extends uniquely to the saturation, translate by translate.** The
translates are pairwise disjoint (`disjoint_translate`), so there is no compatibility condition:
`TopCat.Sheaf.existsUnique_gluing_of_disjoint'` applies to the arbitrary family
`translateSection a s`.

The ambient open `W` is a *parameter* with `hW : W = ⨆ g, translate a V g` rather than the
supremum itself, so that a caller with `W = π⁻¹(π '' V)` in hand (`preimage_imageOpen`) can use the
lemma with no transport. -/
theorem existsUnique_invariantExtension {U : Set X} (hU : IsProperlyDiscontinuousOn a U)
    {V : Opens X.toTopCat} (hVU : (V : Set X) ⊆ U)
    {W : Opens X.toTopCat} (hW : W = ⨆ g : G, translate a V g)
    (s : ToType (X.presheaf.obj (op V))) :
    ∃! t : ToType (X.presheaf.obj (op W)),
      ∀ (g : G) (hg : translate a V g ≤ W),
        X.presheaf.map (homOfLE hg).op t = translateSection a s g := by
  have hle : ∀ g : G, translate a V g ≤ W := fun g => (le_iSup (translate a V) g).trans hW.ge
  obtain ⟨t, ht, huniq⟩ := TopCat.Sheaf.existsUnique_gluing_of_disjoint' X.𝒪
    (translate a V) W (fun g => homOfLE (hle g)) hW.le
    (fun _ _ hij => disjoint_translate hU hVU hij) (translateSection a s)
  exact ⟨t, fun g _ => ht g, fun t' ht' => huniq t' fun g => ht' g (hle g)⟩

/-- **The extension restricts to `s`, and it is invariant.** This is the geometric input to the
stalk lemma, and the only place proper discontinuity is used.

Invariance is proved by *uniqueness*, not by a computation on overlaps: `(a k)^*` of the extension,
transported back to `W`, restricts on the `(h * k)`-th translate to
`(a k)^* ((a h)^* s) = (a (h * k))^* s`, so it is another gluing of the same family and therefore
equal to the extension. -/
theorem exists_invariant_extension {U : Set X} (hU : IsProperlyDiscontinuousOn a U)
    {V : Opens X.toTopCat} (hVU : (V : Set X) ⊆ U)
    {W : Opens X.toTopCat} (hW : W = ⨆ g : G, translate a V g)
    (s : ToType (X.presheaf.obj (op V))) :
    ∃ t : ToType (X.presheaf.obj (op W)),
      (∀ hVW : V ≤ W, X.presheaf.map (homOfLE hVW).op t = s) ∧ IsInvariantSection a t := by
  have hle : ∀ g : G, translate a V g ≤ W := fun g => (le_iSup (translate a V) g).trans hW.ge
  obtain ⟨t, ht, huniq⟩ := existsUnique_invariantExtension hU hVU hW s
  refine ⟨t, fun hVW => ?_, fun k hk => ?_⟩
  · calc X.presheaf.map (homOfLE hVW).op t
        = X.presheaf.map ((homOfLE (hle (1 : G))).op ≫
            eqToHom (congrArg op (translate_one (a := a) V))) t :=
          ConcreteCategory.congr_hom (presheaf_map_congr X.presheaf _ _) t
      _ = X.presheaf.map (eqToHom (congrArg op (translate_one (a := a) V)))
            (X.presheaf.map (homOfLE (hle (1 : G))).op t) :=
          (presheaf_map_comp_apply _ _ _ t).symm
      _ = X.presheaf.map (eqToHom (congrArg op (translate_one (a := a) V)))
            (translateSection a s (1 : G)) := by rw [ht (1 : G) (hle 1)]
      _ = s := by rw [translateSection_one, presheaf_map_comp_apply]; simp
  · have key : ∀ (g : G) (hg : translate a V g ≤ W),
        X.presheaf.map (homOfLE hg).op
            (X.presheaf.map (eqToHom (congrArg op hk.symm))
              ((a k).hom.toShHom.hom.c.app (op W) t)) = translateSection a s g := by
      intro g _
      obtain ⟨h, rfl⟩ : ∃ h : G, h * k = g := ⟨g * k⁻¹, inv_mul_cancel_right g k⟩
      calc X.presheaf.map (homOfLE (hle (h * k))).op
              (X.presheaf.map (eqToHom (congrArg op hk.symm))
                ((a k).hom.toShHom.hom.c.app (op W) t))
          = X.presheaf.map (eqToHom (congrArg op hk.symm) ≫ (homOfLE (hle (h * k))).op)
              ((a k).hom.toShHom.hom.c.app (op W) t) := presheaf_map_comp_apply _ _ _ _
        _ = X.presheaf.map (((Opens.map (a k).hom.toShHom.hom.base).map
              (homOfLE (hle h))).op ≫ eqToHom (congrArg op (translate_translate (a := a) V h k)))
              ((a k).hom.toShHom.hom.c.app (op W) t) :=
            ConcreteCategory.congr_hom (presheaf_map_congr X.presheaf _ _) _
        _ = X.presheaf.map (eqToHom (congrArg op (translate_translate (a := a) V h k)))
              (X.presheaf.map (((Opens.map (a k).hom.toShHom.hom.base).map
                (homOfLE (hle h))).op) ((a k).hom.toShHom.hom.c.app (op W) t)) :=
            (presheaf_map_comp_apply _ _ _ _).symm
        _ = X.presheaf.map (eqToHom (congrArg op (translate_translate (a := a) V h k)))
              ((a k).hom.toShHom.hom.c.app (op (translate a V h))
                (X.presheaf.map (homOfLE (hle h)).op t)) := by
            rw [c_app_naturality]
            rfl
        _ = X.presheaf.map (eqToHom (congrArg op (translate_translate (a := a) V h k)))
              ((a k).hom.toShHom.hom.c.app (op (translate a V h)) (translateSection a s h)) := by
            rw [ht h (hle h)]
        _ = translateSection a s (h * k) := (c_app_translateSection s h k).symm
    have huniq' := huniq _ key
    calc (a k).hom.toShHom.hom.c.app (op W) t
        = X.presheaf.map (eqToHom (congrArg op hk))
            (X.presheaf.map (eqToHom (congrArg op hk.symm))
              ((a k).hom.toShHom.hom.c.app (op W) t)) := by
          rw [presheaf_map_comp_apply]; simp
      _ = X.presheaf.map (eqToHom (congrArg op hk)) t := by rw [huniq']

/-! ### An invariant section is determined by its restriction to `V` -/

/-- **On the `g`-th translate, an invariant section is the pullback of its restriction to `V`.**
Naturality moves the restriction across the pullback, and invariance replaces `(a g)^* r` by `r`;
the two transports that remain are restriction maps between the same pair of opens, so
`presheaf_map_congr` identifies them. -/
theorem restrict_translate_of_isInvariantSection {V W : Opens X.toTopCat} (hVW : V ≤ W)
    {r : ToType (X.presheaf.obj (op W))} (hr : IsInvariantSection a r) (g : G)
    (hg : translate a V g ≤ W)
    (hk : W = (Opens.map (a g).hom.toShHom.hom.base).obj W) :
    X.presheaf.map (homOfLE hg).op r =
      translateSection a (X.presheaf.map (homOfLE hVW).op r) g := by
  rw [translateSection_def, c_app_naturality (a g).hom (homOfLE hVW) r, hr g hk,
    presheaf_map_comp_apply]
  exact ConcreteCategory.congr_hom (presheaf_map_congr X.presheaf _ _) r

/-- **An invariant section on the saturation is determined by its restriction to `V`.** Both
sections are gluings of the same family of prescribed sections, and the gluing is unique. This is
the injectivity half of "the sections of the quotient over `π '' V` are the sections of `X` over
`V`". -/
theorem eq_of_isInvariantSection_of_restrict_eq {U : Set X}
    (hU : IsProperlyDiscontinuousOn a U) {V : Opens X.toTopCat} (hVU : (V : Set X) ⊆ U)
    {W : Opens X.toTopCat} (hW : W = ⨆ g : G, translate a V g) (hVW : V ≤ W)
    (hinvOpen : ∀ k : G, W = (Opens.map (a k).hom.toShHom.hom.base).obj W)
    {r₁ r₂ : ToType (X.presheaf.obj (op W))} (hr₁ : IsInvariantSection a r₁)
    (hr₂ : IsInvariantSection a r₂)
    (hres : X.presheaf.map (homOfLE hVW).op r₁ = X.presheaf.map (homOfLE hVW).op r₂) :
    r₁ = r₂ := by
  obtain ⟨t₀, -, huniq⟩ :=
    existsUnique_invariantExtension hU hVU hW (X.presheaf.map (homOfLE hVW).op r₁)
  refine (huniq r₁ fun g hg =>
      restrict_translate_of_isInvariantSection hVW hr₁ g hg (hinvOpen g)).trans
    (huniq r₂ fun g hg => ?_).symm
  rw [restrict_translate_of_isInvariantSection hVW hr₂ g hg (hinvOpen g), hres]


end LocallyRingedSpace

end AlgebraicGeometry
