/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Order.Concept
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Dedekind-MacNeille completion

The Dedekind-MacNeille completion of a partial order is the smallest complete lattice into which it
embeds.

The theory of concept lattices allows for a simple construction. In fact, `DedekindCut α` is simply
an abbreviation for `Concept α α (· ≤ ·)`. This means we don't need to reprove that this is a
complete lattice; instead, the file simply proves that any order embedding into another complete
lattice factors through it.

## Todo

- Build the order isomorphism `DedekindCut ℚ ≃o ℝ`.
-/

open Concept Set

variable {α β γ : Type*} [Preorder α] [PartialOrder β] [CompleteLattice γ]

namespace DedekindCut

theorem image_fst_subset_lowerBounds {β : Type*} [Preorder β] {f : α → β} (hf : Monotone f)
    (A : DedekindCut α) : f '' A.fst ⊆ lowerBounds (f '' A.snd) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact hf <| rel_fst_snd hx hy

theorem image_snd_subset_upperBounds {β : Type*} [Preorder β] {f : α → β} (hf : Monotone f)
    (A : DedekindCut α) : f '' A.snd ⊆ upperBounds (f '' A.fst) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact hf <| rel_fst_snd hy hx

/-- Convert an element into its Dedekind cut (`Iic a`, `Ici a`). This map is order-preserving,
though it is injective only on partial orders. -/
@[simps!]
def ofElement (a : α) : DedekindCut α where
  fst := Iic a
  snd := Ici a
  closure_fst := upperBounds_Iic
  closure_snd := lowerBounds_Ici

@[simp] theorem fst_ofElement (a : α) : (ofElement a).fst = Iic a := rfl
@[simp] theorem snd_ofElement (a : α) : (ofElement a).snd = Ici a := rfl

@[simp]
theorem ofElement_le_ofElement {a b : α} : ofElement a ≤ ofElement b ↔ a ≤ b := by
  simp [← fst_subset_fst_iff]

@[simp]
theorem ofElement_lt_ofElement {a b : β} : ofElement a < ofElement b ↔ a < b := by
  simp [lt_iff_le_not_ge]

@[simp]
theorem ofElement_inj {a b : β} : ofElement a = ofElement b ↔ a = b := by
  simp [le_antisymm_iff]

/-- `DedekindCut.ofElement` as an `OrderEmbedding`. -/
@[simps!]
def ofElementEmbedding : β ↪o DedekindCut β where
  toFun := ofElement
  inj' _ _ := ofElement_inj.1
  map_rel_iff' := ofElement_le_ofElement

@[simp] theorem ofElementEmbedding_coe : ⇑(@ofElementEmbedding β _) = ofElement := rfl

/-- In a complete lattice, the map `DedekindCut.toElement` has an inverse. -/
def toElement (A : DedekindCut γ) : γ := sSup A.fst

theorem toElement_eq_sSup (A : DedekindCut γ) : toElement A = sSup A.fst := rfl
theorem toElement_eq_sInf (A : DedekindCut γ) : toElement A = sInf A.snd := by
  apply le_antisymm <;>
    simpa [toElement, sInf_le_iff, le_sSup_iff] using fun x hx y hy ↦ rel_fst_snd hy hx

@[simp]
theorem ofElement_toElement (A : DedekindCut γ) : ofElement A.toElement = A := by
  ext
  conv_rhs => rw [← lowerBounds_snd, mem_lowerBounds]
  simp [toElement, le_sSup_iff]

@[simp]
theorem toElement_ofElement (x : γ) : (ofElement x).toElement = x := by
  simp [toElement, ofElement]

/-- The **fundamental theorem of concepts**: every complete lattice is order-isomorphic to the
concept lattice of its `≤` relation. -/
@[simps!]
def _root_.dedekindCutEquiv (γ : Type*) [CompleteLattice γ] : γ ≃o DedekindCut γ where
  toFun := ofElement
  invFun := toElement
  map_rel_iff' := by simp
  left_inv _ := by simp
  right_inv _ := by simp

@[simp]
theorem toElement_le_toElement {A B : DedekindCut γ} : toElement A ≤ toElement B ↔ A ≤ B :=
  (dedekindCutEquiv γ).symm.le_iff_le

@[simp]
theorem toElement_lt_toElement {A B : DedekindCut γ} : toElement A < toElement B ↔ A < B := by
  simp [lt_iff_le_not_ge]

@[simp]
theorem toElement_inj {A B : DedekindCut γ} : toElement A = toElement B ↔ A = B := by
  simp [le_antisymm_iff]

/-- Any order embedding `β ↪o γ` into a complete lattice factors through `DedekindCut β`.

This map is defined so that `factorEmbedding f A = sSup (f '' A.fst)`. Although the construction
`factorEmbedding f A = sInf (f '' A.snd)` would also work, these do **not** in general give equal
embeddings. -/
def factorEmbedding (f : β ↪o γ) : DedekindCut β ↪o γ :=
  .ofMapLEIff (fun A ↦ sSup (f '' A.fst)) <| by
    refine fun A B ↦ ⟨fun h x hx ↦ ?_, fun h ↦ sSup_le_sSup (image_mono h)⟩
    simp_rw [← lowerBounds_snd]
    simp_rw [le_sSup_iff, sSup_le_iff, forall_mem_image] at h
    intro y hy
    rw [← f.le_iff_le]
    exact h _ (image_snd_subset_upperBounds f.monotone _ (mem_image_of_mem _ hy)) hx

theorem factorEmbedding_apply (f : β ↪o γ) (A : DedekindCut β) :
    factorEmbedding f A = sSup (f '' A.fst) :=
  rfl

@[simp]
theorem factorEmbedding_ofElement (f : β ↪o γ) (x : β) : factorEmbedding f (ofElement x) = f x := by
  rw [factorEmbedding_apply]
  apply le_antisymm (by simp)
  rw [le_sSup_iff]
  refine fun y hy ↦ hy ?_
  simp

/-- The Dedekind-MacNeille completion of a partial order is the smallest complete lattice containing
it, in the sense that any embedding into any complete lattice factors through it. -/
theorem factorEmbedding_factors (f : β ↪o γ) :
    ofElementEmbedding.trans (factorEmbedding f) = f := by
  ext; simp

end DedekindCut
