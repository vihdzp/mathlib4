/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Notation.Pi.Defs
public import Mathlib.Algebra.Notation.Prod
public import Mathlib.Order.Basic
public import Mathlib.Order.Max
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic

/-!
# Typeclass expressing `IsBot 0`
-/

public section

variable {α : Type*}

/-- A class expressing `0 ≤ x` for all `x : α`. -/
class IsBotZeroClass (α : Type*) [LE α] [Zero α] where
  isBot_zero : IsBot (0 : α)

/-- A class expressing `1 ≤ x` for all `x : α`. -/
@[to_additive existing]
class IsBotOneClass (α : Type*) [LE α] [One α] where
  isBot_one : IsBot (1 : α)

section LE
variable [LE α] [One α] [IsBotOneClass α] {a b : α}

@[to_additive]
theorem isBot_one : IsBot (1 : α) :=
  IsBotOneClass.isBot_one

@[to_additive (attr := simp)]
theorem one_le (a : α) : 1 ≤ a :=
  isBot_one a

end LE

section Preorder
variable [Preorder α] {a b : α}

section One
variable [One α] [IsBotOneClass α]

@[to_additive]
instance isEmpty_Iio_one : IsEmpty (Set.Iio (1 : α)) :=
  ⟨fun ⟨a, ha⟩ ↦ not_le_of_gt ha (isBot_one a)⟩

@[to_additive (attr := simp) not_lt_zero] lemma not_lt_one : ¬ a < 1 := (one_le a).not_gt

@[deprecated (since := "2025-12-03")] alias not_neg := not_lt_zero

@[to_additive] -- `(attr := simp)` cannot be used here because `a` cannot be inferred by `simp`.
theorem one_lt_of_gt (h : a < b) : 1 < b :=
  (one_le _).trans_lt h

alias LT.lt.pos := pos_of_gt
@[to_additive existing] alias LT.lt.one_lt := one_lt_of_gt

end One

section MulOneClass
variable [MulOneClass α] [IsBotOneClass α]

@[to_additive]
theorem Left.one_lt_mul_of_left [MulLeftMono α] (ha : 1 < a) (b : α) : 1 < a * b :=
  Left.one_lt_mul_of_lt_of_le ha (one_le b)

@[to_additive]
theorem Left.one_lt_mul_of_right [MulLeftStrictMono α] (hb : 1 < b) (a : α) : 1 < a * b :=
  Left.one_lt_mul_of_le_of_lt (one_le a) hb

@[to_additive]
theorem Right.one_lt_mul_of_left [MulRightStrictMono α] (ha : 1 < a) (b : α) : 1 < a * b :=
  Right.one_lt_mul_of_lt_of_le ha (one_le b)

@[to_additive]
theorem Right.one_lt_mul_of_right [MulRightMono α] (hb : 1 < b) (a : α) : 1 < a * b :=
  Right.one_lt_mul_of_le_of_lt (one_le a) hb

@[to_additive add_pos_of_left] alias one_lt_mul_of_left := Left.one_lt_mul_of_left
@[to_additive add_pos_of_right] alias one_lt_mul_of_right := Right.one_lt_mul_of_right

end MulOneClass
end Preorder
