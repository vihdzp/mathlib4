/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Cardinal.Club

/-!
# Order derivative

The ordinal derivative of a normal function `Ordinal → Ordinal` is the unique normal function which
enumerates its fixed points. In this file, we define a slightly more general notion of an "order
derivative", which is well-defined on any regular cardinal order (of cardinality other than ℵ₀).

This is called a derivative for historical reasons. The results in this file are **unrelated** to
the derivative from analysis.
-/

open Cardinal Function Order

universe u

public noncomputable section

namespace Order
variable {α : Type u} [LinearOrder α] [WellFoundedLT α] [IsRegularCardinalOrder α]

private theorem isClub_sInter_fixedPoints
    (hα : #α ≠ ℵ₀) {s : Set (α → α)} (hs : ∀ f ∈ s, IsNormal f) (hsα : #s < #α) :
    IsClub (⋂₀ (fixedPoints '' s)) := by
  rw [← cof_eq_cardinalMk (α := α)] at hα hsα
  refine .sInter hα (mk_image_le.trans_lt hsα) ?_
  rw [Set.forall_mem_image]
  exact fun f hf ↦ (hs f hf).isClub_fixedPoints hα

/-! ### Fixed points of a set of normal functions -/

/-- Given a set of normal functions, `derivSet` returns the function which enumerates their common
fixed points.

This is named after the ordinal derivative, which is **unrelated** to the `deriv` from analysis. -/
def derivSet (hα : #α ≠ ℵ₀) (s : Set (α → α)) (hs : ∀ f ∈ s, IsNormal f) (hsα : #s < #α) : α → α :=
  Subtype.val ∘ enum (⋂₀ (Function.fixedPoints '' s)) (by
    exact (isClub_sInter_fixedPoints hα hs hsα).isCofinal)

attribute [local instance]
  WellFoundedLT.toOrderBot WellFoundedLT.conditionallyCompleteLinearOrderBot in
/-- The next fixed point of a set of normal functions, i.e. the smallest common fixed point larger
than `x`. -/
def nfpSet (s : Set (α → α)) (x : α) : α :=
  have : Nonempty α := ⟨x⟩
  ⨆ i : List s, List.foldr Subtype.val x i

section derivSet
variable (hα : #α ≠ ℵ₀) {s : Set (α → α)} (hs : ∀ f ∈ s, IsNormal f) (hsα : #s < #α) {x y : α}

@[simp]
theorem range_derivSet : .range (derivSet hα s hs hsα) = ⋂ f ∈ s, fixedPoints f := by
  ext; simp [derivSet]

theorem mem_range_derivSet : x ∈ Set.range (derivSet hα s hs hsα) ↔ ∀ f ∈ s, IsFixedPt f x := by
  simp

theorem isFixedPt_derivSet {f : α → α} (hf : f ∈ s) : f.IsFixedPt (derivSet hα s hs hsα x) :=
  (mem_range_derivSet ..).1 (Set.mem_range_self x) f hf

theorem isNormal_derivSet : IsNormal (derivSet hα s hs hsα) :=
  (isClub_sInter_fixedPoints hα hs hsα).isNormal_enum

@[simp]
theorem derivSet_le_derivSet_iff : derivSet hα s hs hsα x ≤ derivSet hα s hs hsα y ↔ x ≤ y :=
  (isNormal_derivSet hα hs hsα).strictMono.le_iff_le

@[simp]
theorem derivSet_lt_derivSet_iff : derivSet hα s hs hsα x < derivSet hα s hs hsα y ↔ x < y :=
  (isNormal_derivSet hα hs hsα).strictMono.lt_iff_lt

@[simp]
theorem derivSet_inj : derivSet hα s hs hsα x = derivSet hα s hs hsα y ↔ x = y :=
  (isNormal_derivSet hα hs hsα).strictMono.injective.eq_iff

theorem derivSet_le_of_forall_lt {a o : α} (ho : ∀ f ∈ s, IsFixedPt f o)
    (hf : ∀ b < a, derivSet hα s hs hsα b < o) : derivSet hα s hs hsα a ≤ o :=
  enum_le_of_forall_lt (by simpa) (by simpa)

private theorem bddAbove_range_foldr (hα : #α ≠ ℵ₀) (hsα : #s < #α) :
    BddAbove (.range fun i : List s ↦ List.foldr Subtype.val x i) := by
  have : Nonempty α := ⟨x⟩
  cases topOrderOrNoTopOrder α with
  | inl h => exact OrderTop.bddAbove _
  | inr h =>
    rw [noTopOrder_iff_noMaxOrder] at h
    refine .of_not_isCofinal fun h ↦ (cof_le h).not_gt ?_
    grw [mk_range_le, mk_list_le_max, max_lt_iff, cof_eq_cardinalMk]
    exact ⟨(aleph0_le_mk α).lt_of_ne' hα, hsα⟩

attribute [local instance]
  WellFoundedLT.toOrderBot WellFoundedLT.conditionallyCompleteLinearOrderBot in
theorem isLUB_nfpSet (hα : #α ≠ ℵ₀) (hsα : #s < #α) :
    IsLUB (.range fun i : List s ↦ List.foldr Subtype.val x i) (nfpSet s x) :=
  have : Nonempty α := ⟨x⟩
  isLUB_csSup' (bddAbove_range_foldr hα hsα)

theorem nfpSet_eq_iSup {α : Type*} [ConditionallyCompleteLinearOrderBot α] [WellFoundedLT α]
    [IsRegularCardinalOrder α] (hα : #α ≠ ℵ₀) {s : Set (α → α)} (hsα : #s < #α) {x : α} :
    nfpSet s x = ⨆ i : List s, List.foldr Subtype.val x i :=
  (isLUB_nfpSet hα hsα).unique (isLUB_csSup' <| bddAbove_range_foldr hα hsα)

theorem le_nfpSet (hα : #α ≠ ℵ₀) (hsα : #s < #α) : x ≤ nfpSet s x :=
  (isLUB_nfpSet hα hsα).1 ⟨[], by simp⟩

attribute [local instance]
  WellFoundedLT.toOrderBot WellFoundedLT.conditionallyCompleteLinearOrderBot in
theorem isFixedPt_nfpSet (hα : #α ≠ ℵ₀) (hs : ∀ f ∈ s, IsNormal f) (hsα : #s < #α)
    {x : α} {f : α → α} (hf : f ∈ s) : f.IsFixedPt (nfpSet s x) := by
  have : Nonempty α := ⟨x⟩
  apply (hs f hf).strictMono.le_apply.antisymm'
  rw [nfpSet_eq_iSup hα hsα, (hs f hf).map_iSup (bddAbove_range_foldr hα hsα)]
  exact ciSup_le fun l ↦ le_ciSup (bddAbove_range_foldr hα hsα) (⟨f, hf⟩ :: l)

theorem nfpSet_le_of_isFixedPt (hα : #α ≠ ℵ₀) (hs : ∀ f ∈ s, IsNormal f) (hsα : #s < #α)
    (hx : x ≤ y) (hy : ∀ f ∈ s, f.IsFixedPt y) : nfpSet s x ≤ y := by
  apply (isLUB_nfpSet hα hsα).2
  rintro _ ⟨l, rfl⟩
  induction l with
  | nil => exact hx
  | cons a l IH => exact hy _ a.2 ▸ (hs _ a.2).monotone IH

theorem derivSet_bot [OrderBot α] : derivSet hα s hs hsα ⊥ = nfpSet s ⊥ := by
  apply (derivSet_le_of_forall_lt ..).antisymm
  · exact nfpSet_le_of_isFixedPt hα hs hsα bot_le fun _ ↦ isFixedPt_derivSet hα hs hsα
  · exact fun _ ↦ isFixedPt_nfpSet hα hs hsα
  · simp

theorem derivSet_succ [SuccOrder α] :
    derivSet hα s hs hsα (succ x) = nfpSet s (succ (derivSet hα s hs hsα x)) := by
  cases IsRegularCardinalOrder.subsingleton_or_noMaxOrder α
  · subsingleton
  apply (derivSet_le_of_forall_lt ..).antisymm
  · apply nfpSet_le_of_isFixedPt hα hs hsα _ fun _ ↦ isFixedPt_derivSet hα hs hsα
    simp
  · exact fun _ ↦ isFixedPt_nfpSet hα hs hsα
  · refine fun y hy ↦ (le_nfpSet hα hsα).trans_lt' ?_
    simpa using hy

end derivSet

/-! ### Fixed points of a single normal function -/

/-- Given a normal function, `deriv` returns the function which enumerates its fixed points.

This is named after the ordinal derivative, which is **unrelated** to the `deriv` from analysis. -/
def deriv (hα : #α ≠ ℵ₀) (f : α → α) (hf : IsNormal f) : α → α :=
  Subtype.val ∘ enum f.fixedPoints (hf.isClub_fixedPoints (by simpa)).isCofinal

/-- The next fixed point of a normal function, i.e. the smallest fixed point larger than `x`. -/
def nfp (f : α → α) (x : α) : α :=
  nfpSet {f} x

omit [IsRegularCardinalOrder α] in
theorem nfpSet_singleton (f : α → α) (x : α) : nfpSet {f} x = nfp f x := (rfl)

section deriv
variable (hα : #α ≠ ℵ₀) {f : α → α} (hf : IsNormal f) {x y : α}

theorem derivSet_singleton [Infinite α] :
    derivSet hα {f} (by simpa) ((aleph0_le_mk α).trans_lt' <| by simp) = deriv hα f hf := by
  unfold deriv derivSet
  rw! [Set.image_singleton, Set.sInter_singleton]
  rfl

@[simp]
theorem range_deriv : .range (deriv hα f hf) = fixedPoints f := by
  ext; simp [deriv]

theorem mem_range_deriv : x ∈ Set.range (deriv hα f hf) ↔ IsFixedPt f x := by
  simp

theorem isFixedPt_deriv : f.IsFixedPt (deriv hα f hf x) :=
  (mem_range_deriv ..).1 (Set.mem_range_self x)

theorem isNormal_deriv : IsNormal (deriv hα f hf) :=
  (hf.isClub_fixedPoints (by simpa)).isNormal_enum

@[simp]
theorem deriv_le_deriv_iff : deriv hα f hf x ≤ deriv hα f hf y ↔ x ≤ y :=
  (isNormal_deriv hα hf).strictMono.le_iff_le

@[simp]
theorem deriv_lt_deriv_iff : deriv hα f hf x < deriv hα f hf y ↔ x < y :=
  (isNormal_deriv hα hf).strictMono.lt_iff_lt

@[simp]
theorem deriv_inj : deriv hα f hf x = deriv hα f hf y ↔ x = y :=
  (isNormal_deriv hα hf).strictMono.injective.eq_iff

theorem deriv_le_of_forall_lt {a o : α} (ho : IsFixedPt f o)
    (hf' : ∀ b < a, deriv hα f hf b < o) : deriv hα f hf a ≤ o :=
  enum_le_of_forall_lt (by simpa) (by simpa)

private theorem bddAbove_range_iterate (hα : #α ≠ ℵ₀) :
    BddAbove (.range fun n : ℕ ↦ f^[n] x) := by
  have : Nonempty α := ⟨x⟩
  cases topOrderOrNoTopOrder α with
  | inl h => exact OrderTop.bddAbove _
  | inr h =>
    rw [noTopOrder_iff_noMaxOrder] at h
    refine .of_not_isCofinal fun h ↦ (cof_le h).not_gt ?_
    grw [← lift_id'.{0, u} (#_), mk_range_le_lift, mk_nat, lift_aleph0, cof_eq_cardinalMk]
    exact (aleph0_le_mk α).lt_of_ne' hα

attribute [local instance]
  WellFoundedLT.toOrderBot WellFoundedLT.conditionallyCompleteLinearOrderBot in
theorem isLUB_nfp (hα : #α ≠ ℵ₀) : IsLUB (.range fun n : ℕ ↦ f^[n] x) (nfp f x) := by
  have : Nonempty α := ⟨x⟩
  convert isLUB_csSup' (bddAbove_range_iterate hα)
  unfold nfp nfpSet iSup
  rw [← EquivLike.range_comp _ (Equiv.listUniqueEquiv ({f} : Set _)).symm]
  congr! with n
  induction n with
  | zero => rfl
  | succ n IH =>
    rw [Function.iterate_succ_apply']
    simp_all [List.replicate_succ]

theorem nfp_eq_iSup {α : Type*} [ConditionallyCompleteLinearOrderBot α] [WellFoundedLT α]
    [IsRegularCardinalOrder α] (hα : #α ≠ ℵ₀) {f : α → α} {x : α} :
    nfp f x = ⨆ n : ℕ, f^[n] x :=
  (isLUB_nfp hα).unique (isLUB_csSup' <| bddAbove_range_iterate hα)

theorem le_nfp (hα : #α ≠ ℵ₀) : x ≤ nfp f x :=
  (isLUB_nfp hα).1 ⟨0, by simp⟩

attribute [local instance]
  WellFoundedLT.toOrderBot WellFoundedLT.conditionallyCompleteLinearOrderBot in
theorem isFixedPt_nfp (hα : #α ≠ ℵ₀) (hf : IsNormal f) {x : α} : f.IsFixedPt (nfp f x) := by
  have : Nonempty α := ⟨x⟩
  apply hf.strictMono.le_apply.antisymm'
  rw [nfp_eq_iSup hα, hf.iSup_iterate_mem_fixedPoints _ (bddAbove_range_iterate hα)]

theorem nfp_le_of_isFixedPt (hα : #α ≠ ℵ₀) (hf : IsNormal f) (hx : x ≤ y) (hy : f.IsFixedPt y) :
    nfp f x ≤ y := by
  apply (isLUB_nfp hα).2
  rintro _ ⟨n, rfl⟩
  induction n with
  | zero => exact hx
  | succ n IH =>
    simp_rw [Function.iterate_succ_apply']
    exact hy ▸ hf.monotone IH

theorem deriv_bot [OrderBot α] : deriv hα f hf ⊥ = nfp f ⊥ := by
  apply (deriv_le_of_forall_lt ..).antisymm
  · exact nfp_le_of_isFixedPt hα hf bot_le (isFixedPt_deriv hα hf)
  · exact isFixedPt_nfp hα hf
  · simp

theorem deriv_succ [SuccOrder α] : deriv hα f hf (succ x) = nfp f (succ (deriv hα f hf x)) := by
  cases IsRegularCardinalOrder.subsingleton_or_noMaxOrder α
  · subsingleton
  apply (deriv_le_of_forall_lt ..).antisymm
  · apply nfp_le_of_isFixedPt hα hf _ (isFixedPt_deriv hα hf)
    simp
  · exact isFixedPt_nfp hα hf
  · refine fun y hy ↦ (le_nfp hα).trans_lt' ?_
    simpa using hy

end deriv

end Order
