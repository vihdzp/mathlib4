/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
import Mathlib.Order.Cofinal
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.SetTheory.Cardinal.Arithmetic

/-!
# Cofinality

This file contains the definition of cofinality of an order and an ordinal number.

## Main Definitions

* `Order.cof α` is the cofinality of a preorder. This is the smallest cardinality of an `IsCofinal`
  set `s : Set α`, meaning `∀ x, ∃ y ∈ s, x ≤ y`.
* `Ordinal.cof o` is the cofinality of the ordinal `o` when viewed as a linear order.

## Main Statements

* `Cardinal.lt_power_cof`: A consequence of König's theorem stating that `c < c ^ c.ord.cof` for
  `c ≥ ℵ₀`.

## Implementation Notes

* The cofinality is defined for ordinals.
  If `c` is a cardinal number, its cofinality is `c.ord.cof`.
-/

noncomputable section

open Function Cardinal Set Order
open scoped Ordinal

universe u v

variable {α ι : Type u} {β : Type v} {a o o' : Ordinal.{u}}

/-! ### Cofinality of orders -/

namespace Order

/-- The of a preorder `α` is the smallest cardinality of an `IsCofinal` subset. -/
def cof (α : Type*) [Preorder α] : Cardinal :=
  ⨅ s : { s : Set α // IsCofinal s }, #s.1

theorem IsCofinal.cof_le [Preorder α] {s : Set α} (h : IsCofinal s) : cof α ≤ #s :=
  ciInf_le' _ (Subtype.mk s h)

theorem cof_le (α : Type*) [Preorder α] : cof α ≤ #α := by
  simpa using IsCofinal.univ.cof_le

theorem le_cof_iff [Preorder α] {c : Cardinal} :
    c ≤ cof α ↔ ∀ {s : Set α}, IsCofinal s → c ≤ #s := by
  rw [cof, le_ciInf_iff', Subtype.forall]

@[deprecated le_cof_iff (since := "2024-12-02")]
alias le_cof := le_cof_iff

theorem lt_cof [Preorder α] {s : Set α} : #s < cof α → ¬ IsCofinal s := by
  simpa using not_imp_not.2 IsCofinal.cof_le

/-- Any order has a cofinal subset whose cardinality is its cofinality. -/
theorem cof_eq (α : Type*) [Preorder α] : ∃ s : Set α, IsCofinal s ∧ cof α = #s := by
  obtain ⟨⟨s, hs⟩, h⟩ := ciInf_mem fun s : { s : Set α // IsCofinal s } ↦ #s.1
  exact ⟨s, hs, h.symm⟩

/-- Any well-order has a cofinal subset whose order type is its cofinality. -/
theorem ord_cof_eq (α : Type*) [LinearOrder α] [WellFoundedLT α] :
    ∃ s : Set α, IsCofinal s ∧ (Order.cof α).ord = typeLT s := by
  obtain ⟨s, hs, hα⟩ := cof_eq α
  obtain ⟨r, _, hr⟩ := ord_eq s
  have hr' := hs.trans (isCofinal_setOf_imp_lt r)
  refine ⟨_, hr', le_antisymm ?_ ?_⟩
  · rw [ord_le]
    exact hr'.cof_le
  · rw [hα, hr, Ordinal.type_le_iff']
    refine ⟨RelEmbedding.ofMonotone (inclusion ?_) ?_⟩
    · simp
    · rintro ⟨_, ⟨x, hx, rfl⟩⟩ ⟨_, ⟨y, _, rfl⟩⟩ h
      obtain h' | h' | h' := trichotomous_of r x y
      · exact h'
      · refine (h.ne ?_).elim
        rwa [Subtype.mk_eq_mk, Subtype.val_inj]
      · cases (hx _ h').not_gt h

end Order

namespace OrderIso

private theorem cof_le_lift [Preorder α] [Preorder β] (f : α ≃o β) :
    Cardinal.lift.{v} (Order.cof α) ≤ Cardinal.lift.{u} (Order.cof β) := by
  rw [Order.cof, Order.cof, lift_iInf, lift_iInf, le_ciInf_iff']
  exact fun ⟨s, hs⟩ ↦ csInf_le' ⟨⟨_, f.symm.map_cofinal hs⟩, mk_image_eq_lift _ _ f.symm.injective⟩

theorem cof_eq_lift [Preorder α] [Preorder β] (f : α ≃o β) :
    Cardinal.lift.{v} (Order.cof α) = Cardinal.lift.{u} (Order.cof β) :=
  have := f.toRelEmbedding.isRefl
  (f.cof_le_lift).antisymm (f.symm.cof_le_lift)

theorem cof_eq {α β : Type u} [Preorder α] [Preorder β] (f : α ≃o β) : Order.cof α = Order.cof β :=
  lift_inj.1 f.cof_eq_lift

end OrderIso

namespace Order

@[simp]
theorem cof_eq_zero [Preorder α] [IsEmpty α] : cof α = 0 := by
  rw [← le_zero_iff, ← mk_emptyCollection α]
  exact (IsCofinal.of_isEmpty (∅ : Set α)).cof_le

@[simp]
theorem cof_eq_zero_iff [Preorder α] : cof α = 0 ↔ IsEmpty α := by
  refine ⟨fun h ↦ ?_, fun h ↦ cof_eq_zero⟩
  obtain ⟨s, hs, hα⟩ := cof_eq α
  rw [hα, mk_eq_zero_iff, isEmpty_subtype, ← eq_empty_iff_forall_notMem] at h
  rwa [h, isCofinal_empty_iff] at hs

@[simp]
theorem cof_ne_zero_iff [Preorder α] : cof α ≠ 0 ↔ Nonempty α := by
  simp [cof_eq_zero_iff.not]

@[simp]
theorem cof_ne_zero [Preorder α] [h : Nonempty α] : cof α ≠ 0 :=
  cof_ne_zero_iff.2 h

@[simp]
theorem cof_eq_one [Preorder α] [OrderTop α] : cof α = 1 := by
  apply le_antisymm
  · rw [← mk_singleton (⊤ : α)]
    exact IsCofinal.singleton_top.cof_le
  · rw [one_le_iff_ne_zero, cof_ne_zero_iff]
    exact top_nonempty α

theorem cof_eq_one_iff [Preorder α] : cof α = 1 ↔ ∃ a : α, IsTop a := by
  refine ⟨fun h ↦ ?_, fun ⟨a, ha⟩ ↦ ?_⟩
  · obtain ⟨s, hs, hα⟩ := cof_eq α
    rw [h, eq_comm, mk_set_eq_one_iff] at hα
    obtain ⟨x, rfl⟩ := hα
    rw [isCofinal_singleton] at hs
    use x
  · have : OrderTop α := @OrderTop.mk _ _ ⟨a⟩ ha
    exact cof_eq_one

end Order

/-! ### Cofinality of ordinals -/

namespace Ordinal

variable [LinearOrder α] [WellFoundedLT α]

/-- The cofinality of an ordinal is the `Order.cof` of any well-order with a given order type. In
particular, `cof 0 = 0` and `cof (succ o) = 1`. -/
def cof (o : Ordinal.{u}) : Cardinal.{u} :=
  o.liftOnWellOrder (fun α _ _ ↦ Order.cof α) fun _ _ _ _ _ _ h ↦ by
    obtain ⟨e⟩ := typeLT_eq.1 h
    exact e.cof_eq

@[simp]
theorem cof_type (α : Type*) [LinearOrder α] [WellFoundedLT α] : (typeLT α).cof = Order.cof α :=
  liftOnWellOrder_type ..

@[simp]
theorem _root_.Order.cof_toType (o : Ordinal) : Order.cof o.toType = o.cof := by
  rw [← cof_type, type_toType]

@[deprecated cof_toType (since := "2025-08-19")]
theorem cof_eq_cof_toType (o : Ordinal) : o.cof = Order.cof o.toType :=
  (cof_toType o).symm

@[simp]
theorem _root_.Order.cof_Iio_ordinal (o : Ordinal.{u}) :
    Order.cof (Iio o) = Cardinal.lift.{u + 1} o.cof := by
  convert (enumIsoToType o).cof_eq_lift
  · rw [Cardinal.lift_id'.{u, u + 1}]
  · rw [cof_toType]

@[simp]
theorem lift_cof (o) : Cardinal.lift.{u, v} (cof o) = cof (Ordinal.lift.{u, v} o) := by
  refine inductionOnWellOrder o fun α _ _ ↦ ?_
  rw [← typeLT_uLift, cof_type, cof_type, ← Cardinal.lift_id'.{v, u} (Order.cof (ULift _)),
    ← Cardinal.lift_umax, ← OrderIso.uLift.cof_eq_lift]

theorem cof_le_card (o : Ordinal) : cof o ≤ card o := by
  rw [← cof_toType, ← mk_toType]
  exact cof_le _

theorem cof_ord_le (c : Cardinal) : c.ord.cof ≤ c := by
  simpa using cof_le_card c.ord

theorem ord_cof_le (o : Ordinal) : o.cof.ord ≤ o :=
  (ord_le_ord.2 (cof_le_card o)).trans (ord_card_le o)

@[simp]
protected theorem _root_.Order.cof_cof (α : Type*) [LinearOrder α] [WellFoundedLT α] :
    (Order.cof α).ord.cof = Order.cof α := by
  obtain ⟨s, hs, hα⟩ := ord_cof_eq α
  obtain ⟨t, ht, hα'⟩ := cof_eq s
  apply ((hs.trans ht).cof_le.trans_eq _).antisymm'
  · apply_fun card at hα
    simpa [hα] using cof_ord_le _
  · rw [mk_image_eq Subtype.val_injective, ← hα', hα, cof_type]

@[simp]
theorem cof_cof (o : Ordinal) : o.cof.ord.cof = o.cof := by
  rw [← cof_toType o, Order.cof_cof]

@[simp]
theorem cof_zero : cof 0 = 0 := by
  rw [← cof_toType, cof_eq_zero]

@[simp]
theorem cof_eq_zero_iff : cof o = 0 ↔ o = 0 := by
  rw [← cof_toType, Order.cof_eq_zero_iff, toType_empty_iff_eq_zero]

theorem cof_ne_zero_iff : cof o ≠ 0 ↔ o ≠ 0 :=
  cof_eq_zero_iff.not

@[simp]
theorem cof_succ (o : Ordinal) : cof (succ o) = 1 := by
  rw [← cof_toType, cof_eq_one]

@[simp]
theorem cof_nat_succ (n : ℕ) : cof (n + 1) = 1 :=
  cof_succ n

@[simp]
theorem cof_eq_one_iff : cof o = 1 ↔ ¬ IsSuccPrelimit o := by
  rw [← cof_toType, not_isSuccPrelimit_iff']
  constructor
  · rw [Order.cof_eq_one_iff]
    refine fun ⟨a, ha⟩ ↦ ⟨(enumIsoToType _).symm a, le_antisymm ?_ ?_⟩
    · simp
    · refine le_of_forall_lt fun b hb ↦ ?_
      rw [lt_succ_iff]
      change ⟨b, hb⟩ ≤ o.enumIsoToType.symm a
      rw [OrderIso.le_symm_apply]
      exact ha _
  · aesop

@[simp]
theorem cof_le_one_iff : cof o ≤ 1 ↔ ¬ IsSuccLimit o := by
  rw [Cardinal.le_one_iff, cof_eq_zero_iff, cof_eq_one_iff, isSuccLimit_iff]
  tauto

@[simp]
theorem cof_lt_aleph0_iff : cof o < ℵ₀ ↔ cof o ≤ 1 := by
  refine ⟨fun h ↦ ?_, one_lt_aleph0.trans_le'⟩
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.1 h
  apply_fun cof ∘ ord at hn
  cases n
  · simp_all
  · simp_rw [comp_apply, ord_nat, Nat.cast_succ, cof_nat_succ, cof_cof] at hn
    rw [hn]

@[simp]
theorem one_lt_cof_iff : 1 < cof o ↔ ℵ₀ ≤ cof o := by
  rw [← not_lt, cof_lt_aleph0_iff, not_le]

theorem aleph0_le_cof_iff : ℵ₀ ≤ cof o ↔ IsSuccLimit o := by
  rw [← one_lt_cof_iff, ← not_iff_not, not_lt, cof_le_one_iff]

theorem _root_.Order.cof_lt_aleph0_iff : Order.cof α < ℵ₀ ↔ Order.cof α ≤ 1 := by
  rw [← cof_type, Ordinal.cof_lt_aleph0_iff]

theorem _root_.Order.one_lt_cof_iff : 1 < Order.cof α ↔ ℵ₀ ≤ Order.cof α := by
  rw [← cof_type, Ordinal.one_lt_cof_iff]

/-! ### Cofinality of suprema and least strict upper bounds -/

/-- The range of an indexed supremum is cofinal within the supremum. -/
theorem isCofinal_range_iSup {f : ι → Ordinal} (H : ∀ i, f i < ⨆ i, f i) :
    IsCofinal (range fun i ↦ enumIsoToType _ ⟨_, H i⟩) := by
  intro x
  have H' := ((enumIsoToType _).symm x).2
  rw [mem_Iio, lt_ciSup_iff'] at H'
  · obtain ⟨i, hi⟩ := H'
    use enumIsoToType _ ⟨_, H i⟩
    simpa [← (enumIsoToType _).symm.le_iff_le] using hi.le
  · use iSup f
    rintro _ ⟨i, rfl⟩
    exact (H i).le

theorem cof_iSup_le_lift {f : ι → Ordinal.{v}} (H : ∀ i, f i < ⨆ i, f i) :
    Cardinal.lift.{u} (cof (⨆ i, f i)) ≤ Cardinal.lift.{v} #ι := by
  rw [← cof_toType]
  exact (Cardinal.lift_le.2 (isCofinal_range_iSup H).cof_le).trans mk_range_le_lift

theorem cof_iSup_le {f : ι → Ordinal} (H : ∀ i, f i < ⨆ i, f i) : cof (⨆ i, f i) ≤ #ι := by
  simpa using cof_iSup_le_lift H

theorem cof_iSup_Iio_le {f : Iio a → Ordinal} (H : ∀ i, f i < ⨆ i, f i) :
    cof (⨆ i, f i) ≤ a.card := by
  convert cof_iSup_le_lift H
  rw [Cardinal.lift_id'.{u, u + 1}, mk_Iio_ordinal, Cardinal.lift_le]

theorem iSup_lt_of_lt_cof_lift {f : ι → Ordinal} {o : Ordinal.{v}} (H : ∀ i, f i < o)
    (h : Cardinal.lift.{v} #ι < Cardinal.lift.{u} o.cof) : ⨆ i, f i < o := by
  apply (ciSup_le' fun i ↦ (H i).le).lt_of_ne
  rintro rfl
  exact (cof_iSup_le_lift H).not_gt h

theorem iSup_lt_of_lt_cof {ι} {f : ι → Ordinal} (H : ∀ i, f i < o) (h : #ι < o.cof) :
    ⨆ i, f i < o := by
  apply iSup_lt_of_lt_cof_lift H
  simpa

theorem iSup_Iio_lt_of_lt_cof {f : Iio a → Ordinal} (H : ∀ i, f i < o) (h : a < o.cof.ord) :
    ⨆ i, f i < o := by
  apply iSup_lt_of_lt_cof_lift H
  rwa [Cardinal.lift_id'.{u, u + 1}, mk_Iio_ordinal, Cardinal.lift_lt, ← lt_ord]

/-! ### Fundamental sequences -/

/-- A fundamental sequence for an ordinal `a` is a strictly monotonic function from `Iio a.cof` to
`Iio a` with cofinal range. We provide `o = a.cof` explicitly to avoid type rewrites. -/
structure IsFundamentalSeq (f : Iio o → Iio a) : Prop where
  /-- This, alongside the other conditions, implies `o = a.cof.ord`. -/
  le_cof : o ≤ a.cof.ord
  /-- A fundamental sequence is strictly monotonic. -/
  strictMono : StrictMono f
  /-- A fundamental sequence has cofinal range. -/
  isCofinal_range : IsCofinal (range f)

namespace IsFundamentalSeq

variable {f : Iio o → Iio a}

theorem monotone (h : IsFundamentalSeq f) : Monotone f :=
  h.strictMono.monotone

theorem cof_eq (h : IsFundamentalSeq f) : o = a.cof.ord := by
  apply h.le_cof.antisymm
  have := h.isCofinal_range.cof_le.trans mk_range_le
  rwa [cof_Iio_ordinal, mk_Iio_ordinal, Cardinal.lift_le, ← ord_le] at this

theorem id_of_le_cof (h : o ≤ o.cof.ord) : IsFundamentalSeq (@id (Iio o)) :=
  ⟨h, strictMono_id, by simp⟩

/-- The empty sequence is a fundamental sequence for `0`. -/
protected theorem zero (f : Iio 0 → Iio 0) : IsFundamentalSeq f :=
  ⟨by simp, isEmptyElim, isEmptyElim⟩

/-- The sequence `{o}` is a fundamental sequence for `succ o`. -/
protected theorem succ : IsFundamentalSeq fun _ : Iio 1 ↦ ⟨o, lt_succ o⟩ := by
  refine ⟨?_, Subsingleton.strictMono _, ?_⟩ <;> simp [IsTop]

/-- The composition of fundamental sequences is a fundamental sequence. -/
theorem trans {g : Iio o' → Iio o} (hf : IsFundamentalSeq f) (hg : IsFundamentalSeq g) :
    IsFundamentalSeq (f ∘ g) := by
  refine ⟨?_, hf.strictMono.comp hg.strictMono, fun x ↦ ?_⟩
  · rw [hg.cof_eq, hf.cof_eq, cof_cof]
  · obtain ⟨_, ⟨y, rfl⟩, hx⟩ := hf.isCofinal_range x
    obtain ⟨_, ⟨z, rfl⟩, hy⟩ := hg.isCofinal_range y
    exact ⟨_, mem_range_self z, hx.trans (hf.monotone hy)⟩

protected theorem iSup (hf : IsFundamentalSeq f) (ho : IsSuccLimit o) : ⨆ i, (f i).1 = a := by
  apply (ciSup_le' fun i ↦ (f i).2.le).antisymm
  apply le_of_forall_lt fun x hx ↦ ?_
  rw [lt_ciSup_iff']
  · obtain ⟨_, ⟨y, rfl⟩, hy⟩ := hf.isCofinal_range ⟨x, hx⟩
    exact ⟨⟨_, ho.succ_lt y.2⟩, hy.trans_lt (hf.strictMono (lt_succ y.1))⟩
  · use a
    rintro _ ⟨i, rfl⟩
    exact (f i).2.le

end IsFundamentalSeq

/-- Every ordinal has a fundamental sequence. -/
theorem exists_isFundamentalSeq (o : Ordinal) :
    ∃ f : Iio o.cof.ord → Iio o, IsFundamentalSeq f := by
  obtain ⟨s, hs, ho⟩ := ord_cof_eq o.toType
  rw [cof_toType] at ho
  rw [ho]
  let g := OrderIso.ofRelIsoLT (enum (α := s) (· < ·))
  refine ⟨fun x ↦ (enumIsoToType _).symm (g x), ho.ge, ?_, fun x ↦ ?_⟩
  · exact (OrderIso.strictMono _).comp g.strictMono
  · obtain ⟨y, hy, hx⟩ := hs (enumIsoToType o x)
    refine ⟨(enumIsoToType o).symm y, ⟨g.symm ⟨y, hy⟩, ?_⟩, ?_⟩ <;>
      simp [← o.enumIsoToType.le_iff_le, hx]

theorem IsNormal.cof_le {f : Ordinal → Ordinal} (hf : IsNormal f) : cof o ≤ cof (f o) := by
  obtain rfl | ⟨a, rfl⟩ | ho := zero_or_succ_or_isSuccLimit o
  · simp
  · rw [cof_succ, Cardinal.one_le_iff_ne_zero, cof_ne_zero_iff]
    exact (hf.strictMono (lt_succ a)).ne_bot
  · obtain ⟨g, hg⟩ := exists_isFundamentalSeq (f o)
    have H (x : Iio (f o)) : ∃ y : Iio o, x < f y := by simpa using (hf.limit_lt ho).1 x.2
    choose s hs using H
    have hs' : ⨆ i, (s (g i)).1 = o := by
      apply (ciSup_le' fun x ↦ (s (g x)).2.le).antisymm
      apply le_of_forall_lt fun x hx ↦ ?_
      rw [lt_ciSup_iff']
      · obtain ⟨_, ⟨y, rfl⟩, h : f x ≤ g y⟩ := hg.isCofinal_range ⟨f x, hf.strictMono hx⟩
        exact ⟨y, hf.lt_iff.1 <| h.trans_lt (hs (g y))⟩
      · use o
        rintro _ ⟨x, rfl⟩
        exact (s (g x)).2.le
    convert cof_iSup_Iio_le (f := fun x ↦ s (g x)) _ using 1
    · rw [hs']
    · rw [card_ord]
    · simpa only [hs'] using fun x ↦ (s (g x)).2

/-- If `g` is a fundamental sequence for `o` and `f` is normal, then `f ∘ g` is a fundamental
sequence for `f o`. -/
protected theorem IsNormal.isFundamentalSeq {f : Ordinal → Ordinal} (hf : IsNormal f)
    (ho : IsSuccLimit o) {g : Iio a → Iio o} (hg : IsFundamentalSeq g) :
    IsFundamentalSeq fun x : Iio a ↦ ⟨f (g x), hf.strictMono (g x).2⟩ := by
  refine ⟨?_, fun x y h ↦ hf.strictMono (hg.strictMono h), fun x ↦ ?_⟩
  · rw [hg.cof_eq, ord_le_ord]
    exact hf.cof_le
  · obtain ⟨y, hy, hx⟩ := (hf.limit_lt ho).1 x.2
    obtain ⟨_, ⟨z, rfl⟩, hz⟩ := hg.isCofinal_range ⟨y, hy⟩
    exact ⟨_, mem_range_self z, hx.le.trans (hf.monotone hz)⟩

theorem IsNormal.cof_eq {f : Ordinal → Ordinal} (hf : IsNormal f) (ho : IsSuccLimit o) :
    cof (f o) = cof o := by
  obtain ⟨g, hg⟩ := exists_isFundamentalSeq o
  exact (ord_injective (hf.isFundamentalSeq ho hg).cof_eq).symm

@[simp]
theorem cof_add {b : Ordinal} (h : b ≠ 0) : cof (a + b) = cof b := by
  obtain rfl | ⟨c, rfl⟩ | hb := zero_or_succ_or_isSuccLimit b
  · contradiction
  · rw [add_succ, cof_succ, cof_succ]
  · exact (isNormal_add_right a).cof_eq hb

@[simp]
theorem cof_preOmega {o : Ordinal} (ho : IsSuccLimit o) : (preOmega o).cof = o.cof :=
  isNormal_preOmega.cof_eq ho

@[simp]
theorem cof_omega {o : Ordinal} (ho : IsSuccLimit o) : (ω_ o).cof = o.cof :=
  isNormal_omega.cof_eq ho

@[simp]
theorem cof_omega0 : cof ω = ℵ₀ := by
  apply (aleph0_le_cof_iff.2 isSuccLimit_omega0).antisymm'
  rw [← card_omega0]
  apply cof_le_card

@[simp]
theorem cof_univ : cof univ.{u, v} = Cardinal.univ.{u, v} := by
  apply le_antisymm (cof_le_card _)
  obtain ⟨s, hs, ho⟩ := cof_eq Ordinal.{u}
  rw [← not_bddAbove_iff_isCofinal, bddAbove_iff_small, small_iff_lift_mk_lt_univ,
    Cardinal.lift_id, ← ho, not_lt, ← Cardinal.lift_le.{v}, Cardinal.lift_univ,
    Cardinal.univ_umax] at hs
  rwa [card_univ, univ, ← lift_cof, cof_type]

end Ordinal

namespace Cardinal
open Ordinal

/-! ### Results on sets -/

-- TODO: these should be rewritten in terms of the `IsCofinal` predicate.

theorem mk_bounded_subset {α : Type*} (h : ∀ x < #α, 2 ^ x < #α) {r : α → α → Prop}
    [IsWellOrder α r] (hr : (#α).ord = type r) : #{ s : Set α // Bounded r s } = #α := by
  rcases eq_or_ne #α 0 with (ha | ha)
  · rw [ha]
    haveI := mk_eq_zero_iff.1 ha
    rw [mk_eq_zero_iff]
    constructor
    rintro ⟨s, hs⟩
    exact (not_unbounded_iff s).2 hs (unbounded_of_isEmpty s)
  have h' : IsStrongLimit #α := ⟨ha, @h⟩
  have ha := h'.aleph0_le
  apply le_antisymm
  · have : { s : Set α | Bounded r s } = ⋃ i, 𝒫{ j | r j i } := setOf_exists _
    rw [← coe_setOf, this]
    refine mk_iUnion_le_sum_mk.trans ((sum_le_iSup (fun i => #(𝒫{ j | r j i }))).trans
      ((mul_le_max_of_aleph0_le_left ha).trans ?_))
    rw [max_eq_left]
    apply ciSup_le' _
    intro i
    rw [mk_powerset]
    apply (h'.two_power_lt _).le
    rw [coe_setOf, card_typein, ← lt_ord, hr]
    apply typein_lt_type
  · refine @mk_le_of_injective α _ (fun x => Subtype.mk {x} ?_) ?_
    · apply bounded_singleton
      rw [← hr]
      apply isSuccLimit_ord ha
    · intro a b hab
      simpa [singleton_eq_singleton_iff] using hab

/-! ### Consequences of König's lemma -/

theorem lt_power_cof {c : Cardinal.{u}} : ℵ₀ ≤ c → c < c ^ c.ord.cof := by
  classical
  induction c using inductionOn with | h α
  intro h
  obtain ⟨r, _, hr⟩ := ord_eq α
  let := linearOrderOfSTO r
  obtain ⟨s, hs, hα⟩ := cof_eq α
  have H := sum_lt_prod (fun a : s ↦ #(Iic a.1)) (fun _ ↦ #α) fun i ↦ ?_
  · simp only [prod_const, lift_id, ← mk_sigma, ← hα, hr] at H ⊢
    refine H.trans_le' ⟨Embedding.ofSurjective (fun x ↦ x.2.1) fun a ↦ ?_⟩
    obtain ⟨b, hb, ha⟩ := hs a
    exact ⟨⟨⟨b, hb⟩, ⟨a, ha⟩⟩, rfl⟩
  · have := typein_lt_type r i
    rw [← hr, lt_ord, ← card_typein] at this
    simp_rw [← Iio_insert]
    exact mk_insert_le.trans_lt (add_lt_of_lt h this (one_lt_aleph0.trans_le h))

theorem lt_cof_power {a b : Cardinal} (ha : ℵ₀ ≤ a) (b1 : 1 < b) : a < (b ^ a).ord.cof := by
  have b0 : b ≠ 0 := (zero_lt_one.trans b1).ne'
  apply lt_imp_lt_of_le_imp_le (power_le_power_left <| power_ne_zero a b0)
  rw [← power_mul, mul_eq_self ha]
  exact lt_power_cof (ha.trans <| (cantor' _ b1).le)

end Cardinal
