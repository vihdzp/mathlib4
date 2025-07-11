/-
Copyright (c) 2023 Yaël Dillies, Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Christopher Hoskin
-/
import Mathlib.Data.Finset.Lattice.Prod
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Closure
import Mathlib.Order.ConditionallyCompleteLattice.Finset

/-!
# Sets closed under join/meet

This file defines predicates for sets closed under `⊔` and shows that each set in a join-semilattice
generates a join-closed set and that a semilattice where every directed set has a least upper bound
is automatically complete. All dually for `⊓`.

## Main declarations

* `SupClosed`: Predicate for a set to be closed under join (`a ∈ s` and `b ∈ s` imply `a ⊔ b ∈ s`).
* `InfClosed`: Predicate for a set to be closed under meet (`a ∈ s` and `b ∈ s` imply `a ⊓ b ∈ s`).
* `IsSublattice`: Predicate for a set to be closed under meet and join.
* `supClosure`: Sup-closure. Smallest sup-closed set containing a given set.
* `infClosure`: Inf-closure. Smallest inf-closed set containing a given set.
* `latticeClosure`: Smallest sublattice containing a given set.
* `SemilatticeSup.toCompleteSemilatticeSup`: A join-semilattice where every sup-closed set has a
  least upper bound is automatically complete.
* `SemilatticeInf.toCompleteSemilatticeInf`: A meet-semilattice where every inf-closed set has a
  greatest lower bound is automatically complete.
-/

variable {ι : Sort*} {F α β : Type*}

section SemilatticeSup
variable [SemilatticeSup α] [SemilatticeSup β]

section Set
variable {ι : Sort*} {S : Set (Set α)} {f : ι → Set α} {s t : Set α} {a : α}
open Set

/-- A set `s` is *sup-closed* if `a ⊔ b ∈ s` for all `a ∈ s`, `b ∈ s`. -/
def SupClosed (s : Set α) : Prop := ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a ⊔ b ∈ s

@[simp] lemma supClosed_empty : SupClosed (∅ : Set α) := by simp [SupClosed]
@[simp] lemma supClosed_singleton : SupClosed ({a} : Set α) := by simp [SupClosed]

@[simp] lemma supClosed_univ : SupClosed (univ : Set α) := by simp [SupClosed]
lemma SupClosed.inter (hs : SupClosed s) (ht : SupClosed t) : SupClosed (s ∩ t) :=
  fun _a ha _b hb ↦ ⟨hs ha.1 hb.1, ht ha.2 hb.2⟩

lemma supClosed_sInter (hS : ∀ s ∈ S, SupClosed s) : SupClosed (⋂₀ S) :=
  fun _a ha _b hb _s hs ↦ hS _ hs (ha _ hs) (hb _ hs)

lemma supClosed_iInter (hf : ∀ i, SupClosed (f i)) : SupClosed (⋂ i, f i) :=
  supClosed_sInter <| forall_mem_range.2 hf

lemma SupClosed.directedOn (hs : SupClosed s) : DirectedOn (· ≤ ·) s :=
  fun _a ha _b hb ↦ ⟨_, hs ha hb, le_sup_left, le_sup_right⟩

lemma IsUpperSet.supClosed (hs : IsUpperSet s) : SupClosed s := fun _a _ _b ↦ hs le_sup_right

lemma SupClosed.preimage [FunLike F β α] [SupHomClass F β α] (hs : SupClosed s) (f : F) :
    SupClosed (f ⁻¹' s) :=
  fun a ha b hb ↦ by simpa [map_sup] using hs ha hb

lemma SupClosed.image [FunLike F α β] [SupHomClass F α β] (hs : SupClosed s) (f : F) :
    SupClosed (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_sup]
  exact Set.mem_image_of_mem _ <| hs ha hb

lemma supClosed_range [FunLike F α β] [SupHomClass F α β] (f : F) : SupClosed (Set.range f) := by
  simpa using supClosed_univ.image f

lemma SupClosed.prod {t : Set β} (hs : SupClosed s) (ht : SupClosed t) : SupClosed (s ×ˢ t) :=
  fun _a ha _b hb ↦ ⟨hs ha.1 hb.1, ht ha.2 hb.2⟩

lemma supClosed_pi {ι : Type*} {α : ι → Type*} [∀ i, SemilatticeSup (α i)] {s : Set ι}
    {t : ∀ i, Set (α i)} (ht : ∀ i ∈ s, SupClosed (t i)) : SupClosed (s.pi t) :=
  fun _a ha _b hb _i hi ↦ ht _ hi (ha _ hi) (hb _ hi)

lemma SupClosed.insert_upperBounds {s : Set α} {a : α} (hs : SupClosed s) (ha : a ∈ upperBounds s) :
    SupClosed (insert a s) := by
  rw [SupClosed]
  aesop

lemma SupClosed.insert_lowerBounds {s : Set α} {a : α} (h : SupClosed s) (ha : a ∈ lowerBounds s) :
    SupClosed (insert a s) := by
  rw [SupClosed]
  have ha' : ∀ b ∈ s, a ≤ b := fun _ a ↦ ha a
  aesop

end Set

section Finset
variable {ι : Type*} {f : ι → α} {s : Set α} {t : Finset ι} {a : α}
open Finset

lemma SupClosed.finsetSup'_mem (hs : SupClosed s) (ht : t.Nonempty) :
    (∀ i ∈ t, f i ∈ s) → t.sup' ht f ∈ s :=
  sup'_induction _ _ hs

lemma SupClosed.finsetSup_mem [OrderBot α] (hs : SupClosed s) (ht : t.Nonempty) :
    (∀ i ∈ t, f i ∈ s) → t.sup f ∈ s :=
  sup'_eq_sup ht f ▸ hs.finsetSup'_mem ht

end Finset
end SemilatticeSup

section SemilatticeInf
variable [SemilatticeInf α] [SemilatticeInf β]

section Set
variable {ι : Sort*} {S : Set (Set α)} {f : ι → Set α} {s t : Set α} {a : α}
open Set

/-- A set `s` is *inf-closed* if `a ⊓ b ∈ s` for all `a ∈ s`, `b ∈ s`. -/
def InfClosed (s : Set α) : Prop := ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → a ⊓ b ∈ s

@[simp] lemma infClosed_empty : InfClosed (∅ : Set α) := by simp [InfClosed]
@[simp] lemma infClosed_singleton : InfClosed ({a} : Set α) := by simp [InfClosed]

@[simp] lemma infClosed_univ : InfClosed (univ : Set α) := by simp [InfClosed]
lemma InfClosed.inter (hs : InfClosed s) (ht : InfClosed t) : InfClosed (s ∩ t) :=
  fun _a ha _b hb ↦ ⟨hs ha.1 hb.1, ht ha.2 hb.2⟩

lemma infClosed_sInter (hS : ∀ s ∈ S, InfClosed s) : InfClosed (⋂₀ S) :=
  fun _a ha _b hb _s hs ↦ hS _ hs (ha _ hs) (hb _ hs)

lemma infClosed_iInter (hf : ∀ i, InfClosed (f i)) : InfClosed (⋂ i, f i) :=
  infClosed_sInter <| forall_mem_range.2 hf

lemma InfClosed.codirectedOn (hs : InfClosed s) : DirectedOn (· ≥ ·) s :=
  fun _a ha _b hb ↦ ⟨_, hs ha hb, inf_le_left, inf_le_right⟩

lemma IsLowerSet.infClosed (hs : IsLowerSet s) : InfClosed s := fun _a _ _b ↦ hs inf_le_right

lemma InfClosed.preimage [FunLike F β α] [InfHomClass F β α] (hs : InfClosed s) (f : F) :
    InfClosed (f ⁻¹' s) :=
  fun a ha b hb ↦ by simpa [map_inf] using hs ha hb

lemma InfClosed.image [FunLike F α β] [InfHomClass F α β] (hs : InfClosed s) (f : F) :
    InfClosed (f '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_inf]
  exact Set.mem_image_of_mem _ <| hs ha hb

lemma infClosed_range [FunLike F α β] [InfHomClass F α β] (f : F) : InfClosed (Set.range f) := by
  simpa using infClosed_univ.image f

lemma InfClosed.prod {t : Set β} (hs : InfClosed s) (ht : InfClosed t) : InfClosed (s ×ˢ t) :=
  fun _a ha _b hb ↦ ⟨hs ha.1 hb.1, ht ha.2 hb.2⟩

lemma infClosed_pi {ι : Type*} {α : ι → Type*} [∀ i, SemilatticeInf (α i)] {s : Set ι}
    {t : ∀ i, Set (α i)} (ht : ∀ i ∈ s, InfClosed (t i)) : InfClosed (s.pi t) :=
  fun _a ha _b hb _i hi ↦ ht _ hi (ha _ hi) (hb _ hi)

lemma InfClosed.insert_upperBounds {s : Set α} {a : α} (hs : InfClosed s) (ha : a ∈ upperBounds s) :
    InfClosed (insert a s) := by
  rw [InfClosed]
  have ha' : ∀ b ∈ s, b ≤ a := fun _ a ↦ ha a
  aesop

lemma InfClosed.insert_lowerBounds {s : Set α} {a : α} (h : InfClosed s) (ha : a ∈ lowerBounds s) :
    InfClosed (insert a s) := by
  rw [InfClosed]
  aesop

end Set

section Finset
variable {ι : Type*} {f : ι → α} {s : Set α} {t : Finset ι} {a : α}
open Finset

lemma InfClosed.finsetInf'_mem (hs : InfClosed s) (ht : t.Nonempty) :
    (∀ i ∈ t, f i ∈ s) → t.inf' ht f ∈ s :=
  inf'_induction _ _ hs

lemma InfClosed.finsetInf_mem [OrderTop α] (hs : InfClosed s) (ht : t.Nonempty) :
    (∀ i ∈ t, f i ∈ s) → t.inf f ∈ s :=
  inf'_eq_inf ht f ▸ hs.finsetInf'_mem ht

end Finset
end SemilatticeInf

open Finset OrderDual

section Lattice
variable {ι : Sort*} [Lattice α] [Lattice β] {S : Set (Set α)} {f : ι → Set α} {s t : Set α} {a : α}

open Set

/-- A set `s` is a *sublattice* if `a ⊔ b ∈ s` and `a ⊓ b ∈ s` for all `a ∈ s`, `b ∈ s`.
Note: This is not the preferred way to declare a sublattice. One should instead use `Sublattice`.
TODO: Define `Sublattice`. -/
structure IsSublattice (s : Set α) : Prop where
  supClosed : SupClosed s
  infClosed : InfClosed s

@[simp] lemma isSublattice_empty : IsSublattice (∅ : Set α) := ⟨supClosed_empty, infClosed_empty⟩
@[simp] lemma isSublattice_singleton : IsSublattice ({a} : Set α) :=
  ⟨supClosed_singleton, infClosed_singleton⟩

@[simp] lemma isSublattice_univ : IsSublattice (Set.univ : Set α) :=
  ⟨supClosed_univ, infClosed_univ⟩

lemma IsSublattice.inter (hs : IsSublattice s) (ht : IsSublattice t) : IsSublattice (s ∩ t) :=
  ⟨hs.1.inter ht.1, hs.2.inter ht.2⟩

lemma isSublattice_sInter (hS : ∀ s ∈ S, IsSublattice s) : IsSublattice (⋂₀ S) :=
  ⟨supClosed_sInter fun _s hs ↦ (hS _ hs).1, infClosed_sInter fun _s hs ↦ (hS _ hs).2⟩

lemma isSublattice_iInter (hf : ∀ i, IsSublattice (f i)) : IsSublattice (⋂ i, f i) :=
  ⟨supClosed_iInter fun _i ↦ (hf _).1, infClosed_iInter fun _i ↦ (hf _).2⟩

lemma IsSublattice.preimage [FunLike F β α] [LatticeHomClass F β α]
    (hs : IsSublattice s) (f : F) :
    IsSublattice (f ⁻¹' s) := ⟨hs.1.preimage _, hs.2.preimage _⟩

lemma IsSublattice.image [FunLike F α β] [LatticeHomClass F α β] (hs : IsSublattice s) (f : F) :
    IsSublattice (f '' s) := ⟨hs.1.image _, hs.2.image _⟩

lemma IsSublattice_range [FunLike F α β] [LatticeHomClass F α β] (f : F) :
    IsSublattice (Set.range f) :=
  ⟨supClosed_range _, infClosed_range _⟩

lemma IsSublattice.prod {t : Set β} (hs : IsSublattice s) (ht : IsSublattice t) :
    IsSublattice (s ×ˢ t) := ⟨hs.1.prod ht.1, hs.2.prod ht.2⟩

lemma isSublattice_pi {ι : Type*} {α : ι → Type*} [∀ i, Lattice (α i)] {s : Set ι}
    {t : ∀ i, Set (α i)} (ht : ∀ i ∈ s, IsSublattice (t i)) : IsSublattice (s.pi t) :=
  ⟨supClosed_pi fun _i hi ↦ (ht _ hi).1, infClosed_pi fun _i hi ↦ (ht _ hi).2⟩

@[simp] lemma supClosed_preimage_toDual {s : Set αᵒᵈ} :
    SupClosed (toDual ⁻¹' s) ↔ InfClosed s := Iff.rfl

@[simp] lemma infClosed_preimage_toDual {s : Set αᵒᵈ} :
    InfClosed (toDual ⁻¹' s) ↔ SupClosed s := Iff.rfl

@[simp] lemma supClosed_preimage_ofDual {s : Set α} :
    SupClosed (ofDual ⁻¹' s) ↔ InfClosed s := Iff.rfl

@[simp] lemma infClosed_preimage_ofDual {s : Set α} :
    InfClosed (ofDual ⁻¹' s) ↔ SupClosed s := Iff.rfl

@[simp] lemma isSublattice_preimage_toDual {s : Set αᵒᵈ} :
    IsSublattice (toDual ⁻¹' s) ↔ IsSublattice s := ⟨fun h ↦ ⟨h.2, h.1⟩, fun h ↦ ⟨h.2, h.1⟩⟩

@[simp] lemma isSublattice_preimage_ofDual :
    IsSublattice (ofDual ⁻¹' s) ↔ IsSublattice s := ⟨fun h ↦ ⟨h.2, h.1⟩, fun h ↦ ⟨h.2, h.1⟩⟩

alias ⟨_, InfClosed.dual⟩ := supClosed_preimage_ofDual
alias ⟨_, SupClosed.dual⟩ := infClosed_preimage_ofDual
alias ⟨_, IsSublattice.dual⟩ := isSublattice_preimage_ofDual
alias ⟨_, IsSublattice.of_dual⟩ := isSublattice_preimage_toDual

end Lattice

section LinearOrder
variable [LinearOrder α]

@[simp] protected lemma LinearOrder.supClosed (s : Set α) : SupClosed s :=
  fun a ha b hb ↦ by cases le_total a b <;> simp [*]

@[simp] protected lemma LinearOrder.infClosed (s : Set α) : InfClosed s :=
  fun a ha b hb ↦ by cases le_total a b <;> simp [*]

@[simp] protected lemma LinearOrder.isSublattice (s : Set α) : IsSublattice s :=
  ⟨LinearOrder.supClosed _, LinearOrder.infClosed _⟩

end LinearOrder

/-! ## Closure -/

section SemilatticeSup
variable [SemilatticeSup α] [SemilatticeSup β] {s t : Set α} {a b : α}

/-- Every set in a join-semilattice generates a set closed under join. -/
@[simps! isClosed]
def supClosure : ClosureOperator (Set α) := .ofPred
  (fun s ↦ {a | ∃ (t : Finset α) (ht : t.Nonempty), ↑t ⊆ s ∧ t.sup' ht id = a})
  SupClosed
  (fun s a ha ↦ ⟨{a}, singleton_nonempty _, by simpa⟩)
  (by
    classical
    rintro s _ ⟨t, ht, hts, rfl⟩ _ ⟨u, hu, hus, rfl⟩
    refine ⟨_, ht.mono subset_union_left, ?_, sup'_union ht hu _⟩
    rw [coe_union]
    exact Set.union_subset hts hus)
  (by rintro s₁ s₂ hs h₂ _ ⟨t, ht, hts, rfl⟩; exact h₂.finsetSup'_mem ht fun i hi ↦ hs <| hts hi)

@[simp] lemma subset_supClosure {s : Set α} : s ⊆ supClosure s := supClosure.le_closure _

@[simp] lemma supClosed_supClosure : SupClosed (supClosure s) := supClosure.isClosed_closure _

lemma supClosure_mono : Monotone (supClosure : Set α → Set α) := supClosure.monotone

@[simp] lemma supClosure_eq_self : supClosure s = s ↔ SupClosed s := supClosure.isClosed_iff.symm

alias ⟨_, SupClosed.supClosure_eq⟩ := supClosure_eq_self

lemma supClosure_idem (s : Set α) : supClosure (supClosure s) = supClosure s :=
  supClosure.idempotent _

@[simp] lemma supClosure_empty : supClosure (∅ : Set α) = ∅ := by simp
@[simp] lemma supClosure_singleton : supClosure {a} = {a} := by simp
@[simp] lemma supClosure_univ : supClosure (Set.univ : Set α) = Set.univ := by simp

@[simp] lemma upperBounds_supClosure (s : Set α) : upperBounds (supClosure s) = upperBounds s :=
  (upperBounds_mono_set subset_supClosure).antisymm <| by
    rintro a ha _ ⟨t, ht, hts, rfl⟩
    exact sup'_le _ _ fun b hb ↦ ha <| hts hb

@[simp] lemma isLUB_supClosure : IsLUB (supClosure s) a ↔ IsLUB s a := by simp [IsLUB]

lemma sup_mem_supClosure (ha : a ∈ s) (hb : b ∈ s) : a ⊔ b ∈ supClosure s :=
  supClosed_supClosure (subset_supClosure ha) (subset_supClosure hb)

lemma finsetSup'_mem_supClosure {ι : Type*} {t : Finset ι} (ht : t.Nonempty) {f : ι → α}
    (hf : ∀ i ∈ t, f i ∈ s) : t.sup' ht f ∈ supClosure s :=
  supClosed_supClosure.finsetSup'_mem _ fun _i hi ↦ subset_supClosure <| hf _ hi

lemma supClosure_min : s ⊆ t → SupClosed t → supClosure s ⊆ t := supClosure.closure_min

/-- The semilatice generated by a finite set is finite. -/
protected lemma Set.Finite.supClosure (hs : s.Finite) : (supClosure s).Finite := by
  lift s to Finset α using hs
  classical
  refine ({t ∈ s.powerset | t.Nonempty}.attach.image
    fun t ↦ t.1.sup' (mem_filter.1 t.2).2 id).finite_toSet.subset ?_
  rintro _ ⟨t, ht, hts, rfl⟩
  simp only [id_eq, coe_image, mem_image, mem_coe, mem_attach, true_and, Subtype.exists,
    Finset.mem_powerset, mem_filter]
  exact ⟨t, ⟨hts, ht⟩, rfl⟩

@[simp] lemma supClosure_prod (s : Set α) (t : Set β) :
    supClosure (s ×ˢ t) = supClosure s ×ˢ supClosure t :=
  le_antisymm (supClosure_min (Set.prod_mono subset_supClosure subset_supClosure) <|
    supClosed_supClosure.prod supClosed_supClosure) <| by
      rintro ⟨_, _⟩ ⟨⟨u, hu, hus, rfl⟩, v, hv, hvt, rfl⟩
      refine ⟨u ×ˢ v, hu.product hv, ?_, ?_⟩
      · simpa only [coe_product] using Set.prod_mono hus hvt
      · simp [prodMk_sup'_sup']

end SemilatticeSup

section SemilatticeInf
variable [SemilatticeInf α] [SemilatticeInf β] {s t : Set α} {a b : α}

/-- Every set in a join-semilattice generates a set closed under join. -/
@[simps! isClosed]
def infClosure : ClosureOperator (Set α) := ClosureOperator.ofPred
  (fun s ↦ {a | ∃ (t : Finset α) (ht : t.Nonempty), ↑t ⊆ s ∧ t.inf' ht id = a})
  InfClosed
  (fun s a ha ↦ ⟨{a}, singleton_nonempty _, by simpa⟩)
  (by
    classical
    rintro s _ ⟨t, ht, hts, rfl⟩ _ ⟨u, hu, hus, rfl⟩
    refine ⟨_, ht.mono subset_union_left, ?_, inf'_union ht hu _⟩
    rw [coe_union]
    exact Set.union_subset hts hus)
  (by rintro s₁ s₂ hs h₂ _ ⟨t, ht, hts, rfl⟩; exact h₂.finsetInf'_mem ht fun i hi ↦ hs <| hts hi)

@[simp] lemma subset_infClosure {s : Set α} : s ⊆ infClosure s := infClosure.le_closure _

@[simp] lemma infClosed_infClosure : InfClosed (infClosure s) := infClosure.isClosed_closure _

lemma infClosure_mono : Monotone (infClosure : Set α → Set α) := infClosure.monotone

@[simp] lemma infClosure_eq_self : infClosure s = s ↔ InfClosed s := infClosure.isClosed_iff.symm

alias ⟨_, InfClosed.infClosure_eq⟩ := infClosure_eq_self

lemma infClosure_idem (s : Set α) : infClosure (infClosure s) = infClosure s :=
  infClosure.idempotent _

@[simp] lemma infClosure_empty : infClosure (∅ : Set α) = ∅ := by simp
@[simp] lemma infClosure_singleton : infClosure {a} = {a} := by simp
@[simp] lemma infClosure_univ : infClosure (Set.univ : Set α) = Set.univ := by simp

@[simp] lemma lowerBounds_infClosure (s : Set α) : lowerBounds (infClosure s) = lowerBounds s :=
  (lowerBounds_mono_set subset_infClosure).antisymm <| by
    rintro a ha _ ⟨t, ht, hts, rfl⟩
    exact le_inf' _ _ fun b hb ↦ ha <| hts hb

@[simp] lemma isGLB_infClosure : IsGLB (infClosure s) a ↔ IsGLB s a := by simp [IsGLB]

lemma inf_mem_infClosure (ha : a ∈ s) (hb : b ∈ s) : a ⊓ b ∈ infClosure s :=
  infClosed_infClosure (subset_infClosure ha) (subset_infClosure hb)

lemma finsetInf'_mem_infClosure {ι : Type*} {t : Finset ι} (ht : t.Nonempty) {f : ι → α}
    (hf : ∀ i ∈ t, f i ∈ s) : t.inf' ht f ∈ infClosure s :=
  infClosed_infClosure.finsetInf'_mem _ fun _i hi ↦ subset_infClosure <| hf _ hi

lemma infClosure_min : s ⊆ t → InfClosed t → infClosure s ⊆ t := infClosure.closure_min

/-- The semilatice generated by a finite set is finite. -/
protected lemma Set.Finite.infClosure (hs : s.Finite) : (infClosure s).Finite := by
  lift s to Finset α using hs
  classical
  refine ({t ∈ s.powerset | t.Nonempty}.attach.image
    fun t ↦ t.1.inf' (mem_filter.1 t.2).2 id).finite_toSet.subset ?_
  rintro _ ⟨t, ht, hts, rfl⟩
  simp only [id_eq, coe_image, mem_image, mem_coe, mem_attach, true_and, Subtype.exists,
    Finset.mem_powerset, mem_filter]
  exact ⟨t, ⟨hts, ht⟩, rfl⟩

@[simp] lemma infClosure_prod (s : Set α) (t : Set β) :
    infClosure (s ×ˢ t) = infClosure s ×ˢ infClosure t :=
  le_antisymm (infClosure_min (Set.prod_mono subset_infClosure subset_infClosure) <|
    infClosed_infClosure.prod infClosed_infClosure) <| by
      rintro ⟨_, _⟩ ⟨⟨u, hu, hus, rfl⟩, v, hv, hvt, rfl⟩
      refine ⟨u ×ˢ v, hu.product hv, ?_, ?_⟩
      · simpa only [coe_product] using Set.prod_mono hus hvt
      · simp [prodMk_inf'_inf']

end SemilatticeInf

section Lattice
variable [Lattice α] [Lattice β] {s t : Set α}

/-- Every set in a join-semilattice generates a set closed under join. -/
@[simps! isClosed]
def latticeClosure : ClosureOperator (Set α) :=
  .ofCompletePred IsSublattice fun _ ↦ isSublattice_sInter

@[simp] lemma subset_latticeClosure : s ⊆ latticeClosure s := latticeClosure.le_closure _

@[simp] lemma isSublattice_latticeClosure : IsSublattice (latticeClosure s) :=
  latticeClosure.isClosed_closure _

lemma latticeClosure_min : s ⊆ t → IsSublattice t → latticeClosure s ⊆ t :=
  latticeClosure.closure_min

lemma latticeClosure_sup_inf_induction (p : (a : α) → a ∈ latticeClosure s → Prop)
    (mem : ∀ (a : α) (has : a ∈ s), p a (subset_latticeClosure has))
    (sup : ∀ (a : α) (has : a ∈ latticeClosure s) (b : α) (hbs : b ∈ latticeClosure s),
      p a has → p b hbs → p (a ⊔ b) (isSublattice_latticeClosure.supClosed has hbs))
    (inf : ∀ (a : α) (has : a ∈ latticeClosure s) (b : α) (hbs : b ∈ latticeClosure s),
      p a has → p b hbs → p (a ⊓ b) (isSublattice_latticeClosure.infClosed has hbs))
    {a : α} (has : a ∈ latticeClosure s) :
    p a has := by
  have h : IsSublattice { a : α | ∃ has : a ∈ latticeClosure s, p a has } := {
    supClosed := fun a ⟨has, hpa⟩ b ⟨hbs, hpb⟩ =>
      ⟨isSublattice_latticeClosure.supClosed has hbs, sup a has b hbs hpa hpb⟩
    infClosed := fun a ⟨has, hpa⟩ b ⟨hbs, hpb⟩ =>
      ⟨isSublattice_latticeClosure.infClosed has hbs, inf a has b hbs hpa hpb⟩ }
  refine (latticeClosure_min (fun a ha ↦ ?_) h has).choose_spec
  exact ⟨subset_latticeClosure ha, mem a ha⟩

lemma latticeClosure_mono : Monotone (latticeClosure : Set α → Set α) := latticeClosure.monotone

@[simp] lemma latticeClosure_eq_self : latticeClosure s = s ↔ IsSublattice s :=
  latticeClosure.isClosed_iff.symm

alias ⟨_, IsSublattice.latticeClosure_eq⟩ := latticeClosure_eq_self

lemma latticeClosure_idem (s : Set α) : latticeClosure (latticeClosure s) = latticeClosure s :=
  latticeClosure.idempotent _

@[simp] lemma latticeClosure_empty : latticeClosure (∅ : Set α) = ∅ := by simp
@[simp] lemma latticeClosure_singleton (a : α) : latticeClosure {a} = {a} := by simp
@[simp] lemma latticeClosure_univ : latticeClosure (Set.univ : Set α) = Set.univ := by simp

lemma image_latticeClosure (s : Set α) (f : α → β)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊔ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊓ f b) :
    f '' latticeClosure s = latticeClosure (f '' s) := by
  simp only [subset_antisymm_iff, Set.image_subset_iff]
  constructor <;> apply latticeClosure_sup_inf_induction
  · exact fun a ha ↦ subset_latticeClosure <| Set.mem_image_of_mem _ ha
  · rintro a - b - ha hb
    simpa [map_sup] using isSublattice_latticeClosure.supClosed ha hb
  · rintro a - b - ha hb
    simpa [map_inf] using isSublattice_latticeClosure.infClosed ha hb
  · exact Set.image_mono subset_latticeClosure
  · rintro _ - _ - ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a ⊔ b, isSublattice_latticeClosure.supClosed ha hb, map_sup ..⟩
  · rintro _ - _ - ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a ⊓ b, isSublattice_latticeClosure.infClosed ha hb, map_inf ..⟩

lemma ofDual_preimage_latticeClosure (s : Set α) :
    ofDual ⁻¹' latticeClosure s = latticeClosure (ofDual ⁻¹' s) := by
  change ClosureOperator.ofCompletePred _ _ _ = ClosureOperator.ofCompletePred _ _ _
  congr
  ext
  exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩

lemma image_latticeClosure' (s : Set α) (f : α → β)
    (map_sup : ∀ a b, f (a ⊔ b) = f a ⊓ f b) (map_inf : ∀ a b, f (a ⊓ b) = f a ⊔ f b) :
    f '' latticeClosure s = latticeClosure (f '' s) := by
  simpa only [Set.image_comp, ← Set.preimage_equiv_eq_image_symm, ← ofDual_preimage_latticeClosure]
    using image_latticeClosure s (ofDual.symm ∘ f) map_sup map_inf

end Lattice

section DistribLattice
variable [DistribLattice α] [DistribLattice β] {s : Set α}

protected lemma SupClosed.infClosure (hs : SupClosed s) : SupClosed (infClosure s) := by
  rintro _ ⟨t, ht, hts, rfl⟩ _ ⟨u, hu, hus, rfl⟩
  rw [inf'_sup_inf']
  exact finsetInf'_mem_infClosure _
    fun i hi ↦ hs (hts (mem_product.1 hi).1) (hus (mem_product.1 hi).2)

protected lemma InfClosed.supClosure (hs : InfClosed s) : InfClosed (supClosure s) := by
  rintro _ ⟨t, ht, hts, rfl⟩ _ ⟨u, hu, hus, rfl⟩
  rw [sup'_inf_sup']
  exact finsetSup'_mem_supClosure _
    fun i hi ↦ hs (hts (mem_product.1 hi).1) (hus (mem_product.1 hi).2)

@[simp] lemma supClosure_infClosure (s : Set α) : supClosure (infClosure s) = latticeClosure s :=
  le_antisymm (supClosure_min (infClosure_min subset_latticeClosure isSublattice_latticeClosure.2)
    isSublattice_latticeClosure.1) <| latticeClosure_min (subset_infClosure.trans subset_supClosure)
      ⟨supClosed_supClosure, infClosed_infClosure.supClosure⟩

@[simp] lemma infClosure_supClosure (s : Set α) : infClosure (supClosure s) = latticeClosure s :=
  le_antisymm (infClosure_min (supClosure_min subset_latticeClosure isSublattice_latticeClosure.1)
    isSublattice_latticeClosure.2) <| latticeClosure_min (subset_supClosure.trans subset_infClosure)
      ⟨supClosed_supClosure.infClosure, infClosed_infClosure⟩

lemma Set.Finite.latticeClosure (hs : s.Finite) : (latticeClosure s).Finite := by
  rw [← supClosure_infClosure]; exact hs.infClosure.supClosure

@[simp] lemma latticeClosure_prod (s : Set α) (t : Set β) :
    latticeClosure (s ×ˢ t) = latticeClosure s ×ˢ latticeClosure t := by
  simp_rw [← supClosure_infClosure]; simp

end DistribLattice

/-- A join-semilattice where every sup-closed set has a least upper bound is automatically complete.
-/
def SemilatticeSup.toCompleteSemilatticeSup [SemilatticeSup α] (sSup : Set α → α)
    (h : ∀ s, SupClosed s → IsLUB s (sSup s)) : CompleteSemilatticeSup α where
  sSup := fun s => sSup (supClosure s)
  le_sSup _ _ ha := (h _ supClosed_supClosure).1 <| subset_supClosure ha
  sSup_le s a ha := (isLUB_le_iff <| h _ supClosed_supClosure).2 <| by rwa [upperBounds_supClosure]

/-- A meet-semilattice where every inf-closed set has a greatest lower bound is automatically
complete. -/
def SemilatticeInf.toCompleteSemilatticeInf [SemilatticeInf α] (sInf : Set α → α)
    (h : ∀ s, InfClosed s → IsGLB s (sInf s)) : CompleteSemilatticeInf α where
  sInf := fun s => sInf (infClosure s)
  sInf_le _ _ ha := (h _ infClosed_infClosure).1 <| subset_infClosure ha
  le_sInf s a ha := (le_isGLB_iff <| h _ infClosed_infClosure).2 <| by rwa [lowerBounds_infClosure]


section ConditionallyCompleteLattice
variable [ConditionallyCompleteLattice α] {f : ι → α} {s t : Set α}

lemma SupClosed.iSup_mem_of_nonempty [Finite ι] [Nonempty ι] (hs : SupClosed s)
    (hf : ∀ i, f i ∈ s) : ⨆ i, f i ∈ s := by
  cases nonempty_fintype (PLift ι)
  rw [← iSup_plift_down, ← Finset.sup'_univ_eq_ciSup]
  exact hs.finsetSup'_mem Finset.univ_nonempty fun _ _ ↦ hf _

lemma InfClosed.iInf_mem_of_nonempty [Finite ι] [Nonempty ι] (hs : InfClosed s)
    (hf : ∀ i, f i ∈ s) : ⨅ i, f i ∈ s := hs.dual.iSup_mem_of_nonempty hf

lemma SupClosed.sSup_mem_of_nonempty (hs : SupClosed s) (ht : t.Finite) (ht' : t.Nonempty)
    (hts : t ⊆ s) : sSup t ∈ s := by
  have := ht.to_subtype
  have := ht'.to_subtype
  rw [sSup_eq_iSup']
  exact hs.iSup_mem_of_nonempty (by simpa)

lemma InfClosed.sInf_mem_of_nonempty (hs : InfClosed s) (ht : t.Finite) (ht' : t.Nonempty)
    (hts : t ⊆ s) : sInf t ∈ s := hs.dual.sSup_mem_of_nonempty ht ht' hts

end ConditionallyCompleteLattice

section BooleanAlgebra
variable [BooleanAlgebra α] {s : Set α}

lemma compl_image_latticeClosure (s : Set α) :
    compl '' latticeClosure s = latticeClosure (compl '' s) :=
  image_latticeClosure' s _ compl_sup_distrib (fun _ _ => compl_inf)

lemma compl_image_latticeClosure_eq_of_compl_image_eq_self (hs : compl '' s = s) :
    compl '' latticeClosure s = latticeClosure s :=
  compl_image_latticeClosure s ▸ hs.symm ▸ rfl

end BooleanAlgebra

variable [CompleteLattice α] {f : ι → α} {s t : Set α}

lemma SupClosed.biSup_mem_of_nonempty {ι : Type*} {t : Set ι} {f : ι → α} (hs : SupClosed s)
    (ht : t.Finite) (ht' : t.Nonempty) (hf : ∀ i ∈ t, f i ∈ s) : ⨆ i ∈ t, f i ∈ s := by
  rw [← sSup_image]
  exact hs.sSup_mem_of_nonempty (ht.image _) (by simpa) (by simpa)

lemma InfClosed.biInf_mem_of_nonempty {ι : Type*} {t : Set ι} {f : ι → α} (hs : InfClosed s)
    (ht : t.Finite) (ht' : t.Nonempty) (hf : ∀ i ∈ t, f i ∈ s) : ⨅ i ∈ t, f i ∈ s :=
  hs.dual.biSup_mem_of_nonempty ht ht' hf

lemma SupClosed.iSup_mem [Finite ι] (hs : SupClosed s) (hbot : ⊥ ∈ s) (hf : ∀ i, f i ∈ s) :
    ⨆ i, f i ∈ s := by
  cases isEmpty_or_nonempty ι
  · simpa [iSup_of_empty]
  · exact hs.iSup_mem_of_nonempty hf

lemma InfClosed.iInf_mem [Finite ι] (hs : InfClosed s) (htop : ⊤ ∈ s) (hf : ∀ i, f i ∈ s) :
    ⨅ i, f i ∈ s := hs.dual.iSup_mem htop hf

lemma SupClosed.sSup_mem (hs : SupClosed s) (ht : t.Finite) (hbot : ⊥ ∈ s) (hts : t ⊆ s) :
    sSup t ∈ s := by
  have := ht.to_subtype
  rw [sSup_eq_iSup']
  exact hs.iSup_mem hbot (by simpa)

lemma InfClosed.sInf_mem (hs : InfClosed s) (ht : t.Finite) (htop : ⊤ ∈ s) (hts : t ⊆ s) :
    sInf t ∈ s := hs.dual.sSup_mem ht htop hts

lemma SupClosed.biSup_mem {ι : Type*} {t : Set ι} {f : ι → α} (hs : SupClosed s)
    (ht : t.Finite) (hbot : ⊥ ∈ s) (hf : ∀ i ∈ t, f i ∈ s) : ⨆ i ∈ t, f i ∈ s := by
  rw [← sSup_image]
  exact hs.sSup_mem (ht.image _) hbot (by simpa)

lemma InfClosed.biInf_mem {ι : Type*} {t : Set ι} {f : ι → α} (hs : InfClosed s)
    (ht : t.Finite) (htop : ⊤ ∈ s) (hf : ∀ i ∈ t, f i ∈ s) : ⨅ i ∈ t, f i ∈ s :=
  hs.dual.biSup_mem ht htop hf
