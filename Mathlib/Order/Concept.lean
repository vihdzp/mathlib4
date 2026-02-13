/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Wrenna Robson, Violeta Hernández Palacios
-/
module

public import Mathlib.Data.Set.Lattice
public import Mathlib.Order.Closure

/-!
# Formal concept analysis

This file defines concept lattices. A concept of a relation `r : α → β → Prop` is a pair of sets
`s : Set α` and `t : Set β` such that `s` is the set of all `a : α` that are related to all elements
of `t`, and `t` is the set of all `b : β` that are related to all elements of `s`.

Ordering the concepts of a relation `r` by inclusion on the first component gives rise to a
*concept lattice*. Every concept lattice is complete and in fact every complete lattice arises as
the concept lattice of its `≤`.

## Implementation notes

Concept lattices are usually defined from a *context*, that is the triple `(α, β, r)`, but the type
of `r` determines `α` and `β` already, so we do not define contexts as a separate object.

## References

* [Davey, Priestley *Introduction to Lattices and Order*][davey_priestley]
* [Birkhoff, Garrett *Lattice Theory*][birkhoff1940]

## Tags

concept, formal concept analysis, intent, extend, attribute, Dedekind-MacNeille completion
-/

@[expose] public section


open Function OrderDual Order Set

variable {ι : Sort*} {α β γ : Type*} {κ : ι → Sort*} (r : α → β → Prop) {s : Set α} {t : Set β}

/-! ### Lower and upper polars -/

/-- The upper polar of `s : Set α` along a relation `r : α → β → Prop` is the set of all elements
which `r` relates to all elements of `s`. -/
def upperPolar (s : Set α) : Set β :=
  { b | ∀ ⦃a⦄, a ∈ s → r a b }

/-- The lower polar of `t : Set β` along a relation `r : α → β → Prop` is the set of all elements
which `r` relates to all elements of `t`. -/
def lowerPolar (t : Set β) : Set α :=
  { a | ∀ ⦃b⦄, b ∈ t → r a b }

theorem upperBounds_eq_upperPolar [LE α] : upperBounds s = upperPolar (· ≤ ·) s := rfl
theorem lowerBounds_eq_lowerPolar [LE β] : lowerBounds t = lowerPolar (· ≤ ·) t := rfl

variable {r} {a : α} {b : β}

theorem mem_upperPolar_iff : b ∈ upperPolar r s ↔ ∀ ⦃a⦄, a ∈ s → r a b := .rfl
theorem mem_lowerPolar_iff : a ∈ lowerPolar r t ↔ ∀ ⦃b⦄, b ∈ t → r a b := .rfl

theorem subset_upperPolar_iff_subset_lowerPolar :
    t ⊆ upperPolar r s ↔ s ⊆ lowerPolar r t :=
  ⟨fun h _ ha _ hb => h hb ha, fun h _ hb _ ha => h ha hb⟩

variable (r)

theorem gc_upperPolar_lowerPolar :
    GaloisConnection (toDual ∘ upperPolar r) (lowerPolar r ∘ ofDual) := fun _ _ =>
  subset_upperPolar_iff_subset_lowerPolar

theorem gc_lowerPolar_upperPolar :
    GaloisConnection (toDual ∘ lowerPolar r) (upperPolar r ∘ ofDual) := fun _ _ =>
  subset_upperPolar_iff_subset_lowerPolar

theorem upperPolar_swap (t : Set β) : upperPolar (swap r) t = lowerPolar r t :=
  rfl

theorem lowerPolar_swap (s : Set α) : lowerPolar (swap r) s = upperPolar r s :=
  rfl

@[simp]
theorem upperPolar_empty : upperPolar r ∅ = univ :=
  eq_univ_of_forall fun _ _ => False.elim

@[simp]
theorem lowerPolar_empty : lowerPolar r ∅ = univ :=
  upperPolar_empty _

@[simp]
theorem mem_upperPolar_singleton_iff : b ∈ upperPolar r {a} ↔ r a b := by
  simp_rw [mem_upperPolar_iff, mem_singleton_iff, forall_eq]

@[simp]
theorem mem_lowerPolar_singleton_iff : a ∈ lowerPolar r {b} ↔ r a b := by
  simp_rw [mem_lowerPolar_iff, mem_singleton_iff, forall_eq]

@[simp]
theorem upperPolar_union (s₁ s₂ : Set α) :
    upperPolar r (s₁ ∪ s₂) = upperPolar r s₁ ∩ upperPolar r s₂ :=
  ext fun _ => forall₂_or_left

@[simp]
theorem lowerPolar_union (t₁ t₂ : Set β) :
    lowerPolar r (t₁ ∪ t₂) = lowerPolar r t₁ ∩ lowerPolar r t₂ :=
  upperPolar_union ..

@[simp]
theorem upperPolar_iUnion (f : ι → Set α) :
    upperPolar r (⋃ i, f i) = ⋂ i, upperPolar r (f i) :=
  (gc_upperPolar_lowerPolar r).l_iSup

@[simp]
theorem lowerPolar_iUnion (f : ι → Set β) :
    lowerPolar r (⋃ i, f i) = ⋂ i, lowerPolar r (f i) :=
  upperPolar_iUnion ..

theorem upperPolar_iUnion₂ (f : ∀ i, κ i → Set α) :
    upperPolar r (⋃ (i) (j), f i j) = ⋂ (i) (j), upperPolar r (f i j) :=
  (gc_upperPolar_lowerPolar r).l_iSup₂

theorem lowerPolar_iUnion₂ (f : ∀ i, κ i → Set β) :
    lowerPolar r (⋃ (i) (j), f i j) = ⋂ (i) (j), lowerPolar r (f i j) :=
  upperPolar_iUnion₂ ..

theorem subset_lowerPolar_upperPolar (s : Set α) :
    s ⊆ lowerPolar r (upperPolar r s) :=
  (gc_upperPolar_lowerPolar r).le_u_l _

theorem subset_upperPolar_lowerPolar (t : Set β) :
    t ⊆ upperPolar r (lowerPolar r t) :=
  subset_lowerPolar_upperPolar _ t

@[simp]
theorem upperPolar_lowerPolar_upperPolar (s : Set α) :
    upperPolar r (lowerPolar r <| upperPolar r s) = upperPolar r s :=
  (gc_upperPolar_lowerPolar r).l_u_l_eq_l _

@[simp]
theorem lowerPolar_upperPolar_lowerPolar (t : Set β) :
    lowerPolar r (upperPolar r <| lowerPolar r t) = lowerPolar r t :=
  upperPolar_lowerPolar_upperPolar _ t

theorem upperPolar_anti : Antitone (upperPolar r) :=
  (gc_upperPolar_lowerPolar r).monotone_l

theorem lowerPolar_anti : Antitone (lowerPolar r) :=
  upperPolar_anti _

theorem lowerPolar_upperPolar_monotone : Monotone (lowerPolar r ∘ upperPolar r) :=
  (lowerPolar_anti r).comp (upperPolar_anti r)

theorem upperPolar_lowerPolar_monotone : Monotone (upperPolar r ∘ lowerPolar r) :=
  (upperPolar_anti r).comp (lowerPolar_anti r)

/-- The `extentClosure` of a set is the smallest extent containing it. -/
@[simps!]
def extentClosure (r : α → β → Prop) : ClosureOperator (Set α) :=
  (gc_upperPolar_lowerPolar r).closureOperator

/-- The `intentClosure` of a set is the smallest intent containing it. -/
@[simps!]
def intentClosure (r : α → β → Prop) : ClosureOperator (Set β) :=
  (gc_lowerPolar_upperPolar r).closureOperator

/-! ### `IsIntent` and `IsExtent` -/

namespace Order

variable {r}

/--
A set is an extent when either of the following equivalent definitions holds:

- The `lowerPolar` of its `upperPolar` is itself.
- The set is the `lowerPolar` of some other set.
-/
def IsExtent (r : α → β → Prop) (s : Set α) := lowerPolar r (upperPolar r s) = s

theorem IsExtent.eq (h : IsExtent r s) : lowerPolar r (upperPolar r s) = s := h

theorem isExtent_iff : IsExtent r s ↔ ∃ t, lowerPolar r t = s :=
  ⟨fun h ↦ ⟨_, h⟩, fun ⟨t, h⟩ ↦ h ▸ lowerPolar_upperPolar_lowerPolar r t⟩

theorem isExtent_lowerPolar (t : Set β) : IsExtent r (lowerPolar r t) :=
  isExtent_iff.2 ⟨_, rfl⟩

@[simp] theorem isExtent_univ : IsExtent r univ := (gc_upperPolar_lowerPolar r).u_l_top

protected theorem IsExtent.inter {s' : Set α} :
    IsExtent r s → IsExtent r s' → IsExtent r (s ∩ s') := by
  simp_rw [isExtent_iff, forall_exists_index]
  rintro t rfl t' rfl
  exact ⟨_, lowerPolar_union r t t'⟩

protected theorem IsExtent.iInter (f : ι → Set α) (hf : ∀ i, IsExtent r (f i)) :
    IsExtent r (⋂ i, f i) := by
  rw [isExtent_iff]
  exact ⟨_, (lowerPolar_iUnion ..).trans (iInter_congr hf)⟩

protected theorem IsExtent.iInter₂ (f : ∀ i, κ i → Set α) (hf : ∀ i j, IsExtent r (f i j)) :
    IsExtent r (⋂ (i) (j), f i j) := by
  rw [isExtent_iff]
  exact ⟨_, (lowerPolar_iUnion₂ ..).trans (iInter₂_congr hf)⟩

theorem IsExtent.lowerPolar_upperPolar_subset {s' : Set α} (h : IsExtent r s) (hs' : s' ⊆ s) :
    lowerPolar r (upperPolar r s') ⊆ s := by
  rw [← h.eq]
  exact lowerPolar_upperPolar_monotone r hs'

/--
A set is an intent when either of the following equivalent definitions holds:

- The `upperPolar` of its `lowerPolar` is itself.
- The set is the `upperPolar` of some other set.
-/
def IsIntent (r : α → β → Prop) (t : Set β) := upperPolar r (lowerPolar r t) = t

theorem IsIntent.eq (h : IsIntent r t) : upperPolar r (lowerPolar r t) = t := h

theorem isIntent_iff : IsIntent r t ↔ ∃ s, upperPolar r s = t := isExtent_iff

theorem isIntent_upperPolar (s : Set α) : IsIntent r (upperPolar r s) := isExtent_lowerPolar _

@[simp] theorem isIntent_univ : IsIntent r univ := isExtent_univ

protected theorem IsIntent.inter {t' : Set β} :
    IsIntent r t → IsIntent r t' → IsIntent r (t ∩ t') :=
  IsExtent.inter

protected theorem IsIntent.iInter (f : ι → Set β) (hf : ∀ i, IsIntent r (f i)) :
    IsIntent r (⋂ i, f i) :=
  IsExtent.iInter _ hf

protected theorem IsIntent.iInter₂ (f : ∀ i, κ i → Set β) (hf : ∀ i j, IsIntent r (f i j)) :
    IsIntent r (⋂ (i) (j), f i j) :=
  IsExtent.iInter₂ _ hf

theorem IsIntent.upperPolar_lowerPolar_subset {t' : Set β} (h : IsIntent r t) (ht' : t' ⊆ t) :
    upperPolar r (lowerPolar r t') ⊆ t := by
  rw [← h.eq]
  exact upperPolar_lowerPolar_monotone r ht'

end Order

/-! ### Concepts -/

variable (α β)

/-- The formal concepts of a relation. A concept of `r : α → β → Prop` is a pair of sets `s`, `t`
such that `s` is the set of all elements that are `r`-related to all of `t` and `t` is the set of
all elements that are `r`-related to all of `s`. -/
structure Concept where
  /-- The extent of a concept. -/
  extent : Set α
  /-- The intent of a concept. -/
  intent : Set β
  /-- The intent consists of all elements related to all elements of the extent. -/
  upperPolar_extent : upperPolar r extent = intent
  /-- The extent consists of all elements related to all elements of the intent. -/
  lowerPolar_intent : lowerPolar r intent = extent

namespace Concept

variable {r r' α β}
variable {c d : Concept α β r} {c' : Concept α α r'}

attribute [simp] upperPolar_extent lowerPolar_intent

/-- See `Concept.ext'` for a version using the intent. -/
@[ext]
theorem ext (h : c.extent = d.extent) : c = d := by
  obtain ⟨s₁, t₁, rfl, _⟩ := c
  obtain ⟨s₂, t₂, rfl, _⟩ := d
  substs h
  rfl

/-- See `Concept.ext` for a version using the extent. -/
theorem ext' (h : c.intent = d.intent) : c = d := by
  obtain ⟨s₁, t₁, _, rfl⟩ := c
  obtain ⟨s₂, t₂, _, rfl⟩ := d
  substs h
  rfl

theorem extent_injective : Injective (@extent α β r) := fun _ _ => ext

theorem intent_injective : Injective (@intent α β r) := fun _ _ => ext'

/-- Copy a concept, adjusting definitional equalities. -/
@[simps!]
def copy (c : Concept α β r) (e : Set α) (i : Set β) (he : e = c.extent) (hi : i = c.intent) :
    Concept α β r := ⟨e, i, he ▸ hi ▸ c.upperPolar_extent, he ▸ hi ▸ c.lowerPolar_intent⟩

theorem copy_eq (c : Concept α β r) (e : Set α) (i : Set β) (he hi) : c.copy e i he hi = c := by
  ext; simp_all

/-- Define a concept from an extent, by setting the intent to its upper polar. -/
@[simps!]
def _root_.Order.IsExtent.concept (hs : IsExtent r s) : Concept α β r :=
  ⟨s, upperPolar r s, rfl, hs⟩

theorem isExtent_extent (c : Concept α β r) : IsExtent r c.extent :=
  lowerPolar_intent c ▸ isExtent_lowerPolar c.intent

theorem isExtent_iff_exists_concept : IsExtent r s ↔ ∃ c : Concept α β r, c.extent = s :=
  ⟨fun h ↦ ⟨h.concept, rfl⟩, fun ⟨c, h⟩ ↦ h ▸ c.isExtent_extent⟩

/-- Define a concept from an intent, by setting the extent to its lower polar. -/
@[simps!]
def _root_.Order.IsIntent.concept (ht : IsIntent r t) : Concept α β r :=
  ⟨lowerPolar r t, t, ht, rfl⟩

theorem isIntent_intent (c : Concept α β r) : IsIntent r c.intent :=
  upperPolar_extent c ▸ isIntent_upperPolar c.extent

theorem isIntent_iff_exists_concept : IsIntent r t ↔ ∃ c : Concept α β r, c.intent = t :=
  ⟨fun h ↦ ⟨h.concept, rfl⟩, fun ⟨c, h⟩ ↦ h ▸ c.isIntent_intent⟩

/-- The concept generated from the upper polar of a set, i.e. the smallest concept containing the
set of objects `s`. -/
-- We don't use `simps!`, as the autogenerated lemma `ofObjects_extent` gives us a name clash.
def ofObjects (r : α → β → Prop) (s : Set α) : Concept α β r :=
  (isIntent_upperPolar s).concept

/-- The concept generated by a single object. -/
abbrev ofObject (r : α → β → Prop) (a : α) : Concept α β r := ofObjects r {a}

@[simp] theorem intent_ofObjects : (ofObjects r s).intent = upperPolar r s := rfl
@[simp] theorem extent_ofObjects : (ofObjects r s).extent = lowerPolar r (upperPolar r s) :=
  rfl

@[simp]
theorem ofObjects_extent : ofObjects r c.extent = c :=
  intent_injective c.upperPolar_extent

theorem leftInverse_ofObjects_extent : LeftInverse (ofObjects r) extent :=
  fun _ ↦ ofObjects_extent

theorem leftInvOn_extent_ofObjects : Set.LeftInvOn extent (ofObjects r) {s | IsExtent r s} :=
  fun _ ↦ id

theorem surjective_ofObjects : Surjective (ofObjects r) :=
  leftInverse_ofObjects_extent.surjective

/-- The concept generated from the lower polar of a set, i.e. the smallest concept whose set of
attributes is contained in `t`. -/
-- We don't use `simps!`, as the autogenerated lemma `ofAttributes_intent` gives us a name clash.
def ofAttributes (r : α → β → Prop) (t : Set β) : Concept α β r :=
  (isExtent_lowerPolar t).concept

/-- The concept generated by a single attribute. -/
abbrev ofAttribute (r : α → β → Prop) (b : β) : Concept α β r := ofAttributes r {b}

@[simp] theorem extent_ofAttributes : (ofAttributes r t).extent = lowerPolar r t := rfl
@[simp] theorem intent_ofAttributes : (ofAttributes r t).intent = upperPolar r (lowerPolar r t) :=
  rfl

@[simp]
theorem ofAttributes_intent : ofAttributes r c.intent = c :=
  extent_injective c.lowerPolar_intent

theorem leftInverse_ofAttributes_extent : LeftInverse (ofAttributes r) intent :=
  fun c ↦ extent_injective c.lowerPolar_intent

theorem leftInvOn_ofObjects_intent : Set.LeftInvOn intent (ofAttributes r) {s | IsIntent r s} :=
  fun _ ↦ id

theorem surjective_ofAttributes : Surjective (ofAttributes r) :=
  leftInverse_ofAttributes_extent.surjective

theorem rel_extent_intent {x y} (hx : x ∈ c.extent) (hy : y ∈ c.intent) : r x y := by
  rw [← c.upperPolar_extent] at hy
  exact hy hx

/-- Note that if `r'` is the `≤` relation, this theorem will often not be true! -/
theorem disjoint_extent_intent [Std.Irrefl r'] : Disjoint c'.extent c'.intent := by
  rw [disjoint_iff_forall_ne]
  rintro x hx _ hx' rfl
  exact irrefl x (rel_extent_intent hx hx')

theorem mem_extent_of_rel_extent [IsTrans α r'] {x y} (hy : r' y x) (hx : x ∈ c'.extent) :
    y ∈ c'.extent := by
  rw [← lowerPolar_intent]
  exact fun z hz ↦ _root_.trans hy (rel_extent_intent hx hz)

theorem mem_intent_of_intent_rel [IsTrans α r'] {x y} (hy : r' x y) (hx : x ∈ c'.intent) :
    y ∈ c'.intent := by
  rw [← upperPolar_extent]
  exact fun z hz ↦ _root_.trans (rel_extent_intent hz hx) hy

theorem codisjoint_extent_intent [Std.Trichotomous r'] [IsTrans α r'] :
    Codisjoint c'.extent c'.intent := by
  rw [codisjoint_iff_le_sup]
  refine fun x _ ↦ or_iff_not_imp_left.2 fun hx ↦ ?_
  rw [← upperPolar_extent]
  intro y hy
  apply Not.imp_symm <| Std.Trichotomous.trichotomous x y (hx <| mem_extent_of_rel_extent · hy)
  exact (hx <| · ▸ hy)

instance : PartialOrder (Concept α β r) :=
  PartialOrder.lift _ extent_injective

theorem isCompl_extent_intent [IsStrictTotalOrder α r'] (c' : Concept α α r') :
    IsCompl c'.extent c'.intent :=
  ⟨c'.disjoint_extent_intent, c'.codisjoint_extent_intent⟩

@[simp]
theorem compl_extent [IsStrictTotalOrder α r'] (c' : Concept α α r') : c'.extentᶜ = c'.intent :=
  c'.isCompl_extent_intent.compl_eq

@[simp]
theorem compl_intent [IsStrictTotalOrder α r'] (c' : Concept α α r') : c'.intentᶜ = c'.extent :=
  c'.isCompl_extent_intent.symm.compl_eq

instance : PartialOrder (Concept α β r) :=
  PartialOrder.lift _ extent_injective

@[simp]
theorem extent_subset_extent_iff : c.extent ⊆ d.extent ↔ c ≤ d :=
  Iff.rfl

@[simp]
theorem extent_ssubset_extent_iff : c.extent ⊂ d.extent ↔ c < d :=
  Iff.rfl

@[simp]
theorem intent_subset_intent_iff : c.intent ⊆ d.intent ↔ d ≤ c := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← extent_subset_extent_iff, ← c.lowerPolar_intent, ← d.lowerPolar_intent]
    exact lowerPolar_anti _ h
  · rw [← c.upperPolar_extent, ← d.upperPolar_extent]
    exact upperPolar_anti _ h

@[simp]
theorem intent_ssubset_intent_iff : c.intent ⊂ d.intent ↔ d < c := by
  rw [ssubset_iff_subset_not_subset, lt_iff_le_not_ge,
    intent_subset_intent_iff, intent_subset_intent_iff]

theorem strictMono_extent : StrictMono (@extent α β r) := fun _ _ =>
  extent_ssubset_extent_iff.2

theorem strictAnti_intent : StrictAnti (@intent α β r) := fun _ _ =>
  intent_ssubset_intent_iff.2

theorem isLowerSet_extent_le {α : Type*} [Preorder α] (c : Concept α α (· ≤ ·)) :
    IsLowerSet c.extent :=
  @mem_extent_of_rel_extent _ _ _ _

theorem isUpperSet_intent_le {α : Type*} [Preorder α] (c : Concept α α (· ≤ ·)) :
    IsUpperSet c.intent :=
  @mem_intent_of_intent_rel _ _ _ _

theorem isLowerSet_extent_lt {α : Type*} [PartialOrder α] (c : Concept α α (· < ·)) :
    IsLowerSet c.extent := by
  intro a b hb ha
  obtain rfl | hb := hb.eq_or_lt
  · assumption
  · exact mem_extent_of_rel_extent hb ha

theorem isUpperSet_intent_lt {α : Type*} [PartialOrder α] (c : Concept α α (· < ·)) :
    IsUpperSet c.intent := by
  intro a b hb ha
  obtain rfl | hb := hb.eq_or_lt
  · assumption
  · exact mem_intent_of_intent_rel hb ha

@[simps!]
instance : Max (Concept α β r) where
  max c d := (c.isIntent_intent.inter d.isIntent_intent).concept

alias sup_extent := max_extent
alias sup_intent := max_intent

@[simps!]
instance : Min (Concept α β r) where
  min c d := (c.isExtent_extent.inter d.isExtent_extent).concept

alias inf_extent := min_extent
alias inf_intent := min_intent

instance : SemilatticeInf (Concept α β r) :=
  extent_injective.semilatticeInf _ .rfl .rfl fun _ _ ↦ rfl

instance : SemilatticeSup (Concept α β r) :=
  (toDual.injective.comp intent_injective).semilatticeSup _ (by simp) (by simp) fun _ _ ↦ rfl

@[simp]
theorem ofObjects_le_iff : ofObjects r s ≤ c ↔ s ⊆ c.extent := by
  rw [← extent_subset_extent_iff]
  exact ⟨((subset_lowerPolar_upperPolar r s).trans ·),
    (isExtent_extent c).lowerPolar_upperPolar_subset⟩

theorem le_ofObjects_of_subset (h : c.extent ⊆ s) : c ≤ ofObjects r s := by
  simpa using (lowerPolar_anti r).comp (upperPolar_anti r) h

@[simp]
theorem le_ofAttributes_iff : c ≤ ofAttributes r t ↔ t ⊆ c.intent := by
  rw [← intent_subset_intent_iff]
  exact ⟨((subset_upperPolar_lowerPolar r t).trans ·),
    (isIntent_intent c).upperPolar_lowerPolar_subset⟩

theorem ofAttributes_le_of_subset (h : c.intent ⊆ t) : ofAttributes r t ≤ c := by
  rw [← intent_subset_intent_iff]
  simpa using (upperPolar_anti r).comp (lowerPolar_anti r) h

theorem ofObject_le_ofAttribute_iff {a b} : ofObject r a ≤ ofAttribute r b ↔ r a b := by
  simp

instance instLatticeConcept : Lattice (Concept α β r) where
  sup := (· ⊔ ·)
  le_sup_left _ _ := intent_subset_intent_iff.1 inter_subset_left
  le_sup_right _ _ := intent_subset_intent_iff.1 inter_subset_right
  sup_le _ _ _ := by
    simp_rw [← intent_subset_intent_iff]
    exact subset_inter

@[simps!]
instance instBoundedOrderConcept : BoundedOrder (Concept α β r) where
  top := isExtent_univ.concept
  le_top _ := subset_univ _
  bot := isIntent_univ.concept
  bot_le _ := intent_subset_intent_iff.1 <| subset_univ _

@[simps!]
instance : InfSet (Concept α β r) where
  sInf S := (IsExtent.iInter₂ _ fun c (_ : c ∈ S) => c.isExtent_extent).concept

@[simps!]
instance : SupSet (Concept α β r) where
  sSup S := (IsIntent.iInter₂ _ fun c (_ : c ∈ S) => c.isIntent_intent).concept

/-- One half of the **fundamental theorem of concept lattices**: every concept lattice is a complete
lattice. -/
instance : CompleteLattice (Concept α β r) where
  le_sSup _ _ hc := intent_subset_intent_iff.1 <| biInter_subset_of_mem hc
  sSup_le _ _ hc := intent_subset_intent_iff.1 <|
    subset_iInter₂ (intent_subset_intent_iff.2 <| hc · ·)
  sInf_le _ _ := biInter_subset_of_mem
  le_sInf _ _ := subset_iInter₂

@[simp]
theorem extent_top : (⊤ : Concept α β r).extent = univ :=
  rfl

@[simp]
theorem intent_top : (⊤ : Concept α β r).intent = upperPolar r univ :=
  rfl

@[simp]
theorem extent_bot : (⊥ : Concept α β r).extent = lowerPolar r univ :=
  rfl

@[simp]
theorem intent_bot : (⊥ : Concept α β r).intent = univ :=
  rfl

@[simp]
theorem extent_sup (c d : Concept α β r) : (c ⊔ d).extent = lowerPolar r (c.intent ∩ d.intent) :=
  rfl

@[simp]
theorem intent_sup (c d : Concept α β r) : (c ⊔ d).intent = c.intent ∩ d.intent :=
  rfl

@[simp]
theorem extent_inf (c d : Concept α β r) : (c ⊓ d).extent = c.extent ∩ d.extent :=
  rfl

@[simp]
theorem intent_inf (c d : Concept α β r) : (c ⊓ d).intent = upperPolar r (c.extent ∩ d.extent) :=
  rfl

@[simp]
theorem extent_sSup (S : Set (Concept α β r)) :
    (sSup S).extent = lowerPolar r (⋂ c ∈ S, intent c) :=
  rfl

@[simp]
theorem intent_sSup (S : Set (Concept α β r)) : (sSup S).intent = ⋂ c ∈ S, intent c :=
  rfl

@[simp]
theorem extent_sInf (S : Set (Concept α β r)) : (sInf S).extent = ⋂ c ∈ S, extent c :=
  rfl

@[simp]
theorem intent_sInf (S : Set (Concept α β r)) :
    (sInf S).intent = upperPolar r (⋂ c ∈ S, extent c) :=
  rfl

instance : Inhabited (Concept α β r) :=
  ⟨⊥⟩

/-- Swap the sets of a concept to make it a concept of the dual context. -/
@[simps]
def swap (c : Concept α β r) : Concept β α (swap r) :=
  ⟨c.intent, c.extent, c.lowerPolar_intent, c.upperPolar_extent⟩

@[simp]
theorem swap_swap (c : Concept α β r) : c.swap.swap = c :=
  ext rfl

@[simp]
theorem swap_le_swap_iff : c.swap ≤ d.swap ↔ d ≤ c :=
  intent_subset_intent_iff

@[simp]
theorem swap_lt_swap_iff : c.swap < d.swap ↔ d < c :=
  intent_ssubset_intent_iff

/-- The dual of a concept lattice is isomorphic to the concept lattice of the dual context. -/
@[simps]
def swapEquiv : (Concept α β r)ᵒᵈ ≃o Concept β α (Function.swap r) where
  toFun := swap ∘ ofDual
  invFun := toDual ∘ swap
  left_inv := swap_swap
  right_inv := swap_swap
  map_rel_iff' := swap_le_swap_iff

end Concept
