/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Lemmas about rings of characteristic two

This file contains results about `CharP R 2`, in the `CharTwo` namespace.

The lemmas in this file with a `_sq` suffix are just special cases of the `_pow_char` lemmas
elsewhere, with a shorter name for ease of discovery, and no need for a `[Fact (Prime 2)]` argument.
-/

public section

assert_not_exists Algebra LinearMap

variable {R ι : Type*}

namespace CharTwo

section AddMonoidWithOne

variable [AddMonoidWithOne R]

/-- The only hypotheses required to build a `CharP R 2` instance are `1 ≠ 0` and `2 = 0`. -/
theorem of_one_ne_zero_of_two_eq_zero (h₁ : (1 : R) ≠ 0) (h₂ : (2 : R) = 0) : CharP R 2 where
  cast_eq_zero_iff n := by
    obtain hn | hn := Nat.even_or_odd n
    · simp_rw [hn.two_dvd, iff_true]
      exact natCast_eq_zero_of_even_of_two_eq_zero hn h₂
    · simp_rw [hn.not_two_dvd_nat, iff_false]
      rwa [natCast_eq_one_of_odd_of_two_eq_zero hn h₂]

variable [CharP R 2]

@[scoped simp]
theorem two_eq_zero : (2 : R) = 0 := by
  rw [← Nat.cast_two, CharP.cast_eq_zero]

theorem natCast_eq_ite (n : ℕ) : (n : R) = if Even n then 0 else 1 := by
  induction n <;> aesop (add simp [one_add_one_eq_two])

@[simp]
theorem range_natCast : Set.range ((↑) : ℕ → R) = {0, 1} := by
  rw [funext natCast_eq_ite, Set.range_if]
  · use 0; simp
  · use 1; simp

variable (R) in
theorem natCast_cases (n : ℕ) : (n : R) = 0 ∨ (n : R) = 1 :=
  (Set.ext_iff.1 range_natCast _).1 (Set.mem_range_self _)

theorem natCast_eq_mod (n : ℕ) : (n : R) = (n % 2 : ℕ) := by
  simp [natCast_eq_ite, Nat.even_iff]

@[scoped simp]
theorem ofNat_eq_mod (n : ℕ) [n.AtLeastTwo] : (ofNat(n) : R) = (ofNat(n) % 2 : ℕ) :=
  natCast_eq_mod n

end AddMonoidWithOne

section Semiring

variable [Semiring R] [CharP R 2]

@[scoped simp]
theorem add_self_eq_zero (x : R) : x + x = 0 := by rw [← two_smul R x, two_eq_zero, zero_smul]

@[scoped simp]
protected theorem two_nsmul (x : R) : 2 • x = 0 := by rw [two_smul, add_self_eq_zero]

@[scoped simp]
protected theorem add_cancel_left (a b : R) : a + (a + b) = b := by
  rw [← add_assoc, add_self_eq_zero, zero_add]

@[scoped simp]
protected theorem add_cancel_right (a b : R) : a + b + b = a := by
  rw [add_assoc, add_self_eq_zero, add_zero]

end Semiring

section Ring

variable [Ring R] [CharP R 2]

@[scoped simp]
theorem neg_eq (x : R) : -x = x := by
  rw [neg_eq_itef_add_eq_zero, add_self_eq_zero]

theorem neg_eq' : Neg.neg = (id : R → R) :=
  funext neg_eq

@[scoped simp]
theorem sub_eq_add (x y : R) : x - y = x + y := by rw [sub_eq_add_neg, neg_eq]

theorem add_eq_iff_eq_add {a b c : R} : a + b = c ↔ a = c + b := by
  rw [← sub_eq_iff_eq_add, sub_eq_add]

theorem eq_add_iff_add_eq {a b c : R} : a = b + c ↔ a + c = b := by
  rw [← eq_sub_iff_add_eq, sub_eq_add]

@[scoped simp]
protected theorem two_zsmul (x : R) : (2 : ℤ) • x = 0 := by
  rw [two_zsmul, add_self_eq_zero]

protected theorem add_eq_zero {a b : R} : a + b = 0 ↔ a = b := by
  rw [← CharTwo.sub_eq_add, sub_eq_iff_eq_add, zero_add]

theorem intCast_eq_ite (n : ℤ) : (n : R) = if Even n then 0 else 1 := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg <;> simpa using natCast_eq_ite n

@[simp]
theorem range_intCast : Set.range ((↑) : ℤ → R) = {0, 1} := by
  rw [funext intCast_eq_if, Set.range_if]
  · use 0; simp
  · use 1; simp

variable (R) in
theorem intCast_cases (n : ℤ) : (n : R) = 0 ∨ (n : R) = 1 :=
  (Set.ext_iff.1 range_intCast _).1 (Set.mem_range_self _)

theorem intCast_eq_mod (n : ℤ) : (n : R) = (n % 2 : ℤ) := by
  simp [intCast_eq_if, Int.even_iff]

end Ring

section CommSemiring

variable [CommSemiring R] [CharP R 2]

theorem add_sq (x y : R) : (x + y) ^ 2 = x ^ 2 + y ^ 2 :=
  add_pow_char _ _ _

theorem add_mul_self (x y : R) : (x + y) * (x + y) = x * x + y * y := by
  rw [← pow_two, ← pow_two, ← pow_two, add_sq]

theorem list_sum_sq (l : List R) : l.sum ^ 2 = (l.map (· ^ 2)).sum :=
  list_sum_pow_char _ _

theorem list_sum_mul_self (l : List R) : l.sum * l.sum = (List.map (fun x => x * x) l).sum := by
  simp_rw [← pow_two, list_sum_sq]

theorem multiset_sum_sq (l : Multiset R) : l.sum ^ 2 = (l.map (· ^ 2)).sum :=
  multiset_sum_pow_char _ _

theorem multiset_sum_mul_self (l : Multiset R) :
    l.sum * l.sum = (Multiset.map (fun x => x * x) l).sum := by simp_rw [← pow_two, multiset_sum_sq]

theorem sum_sq (s : Finset ι) (f : ι → R) : (∑ i ∈ s, f i) ^ 2 = ∑ i ∈ s, f i ^ 2 :=
  sum_pow_char _ _ _

theorem sum_mul_self (s : Finset ι) (f : ι → R) :
    ((∑ i ∈ s, f i) * ∑ i ∈ s, f i) = ∑ i ∈ s, f i * f i := by simp_rw [← pow_two, sum_sq]

end CommSemiring

namespace CommRing

variable [CommRing R] [CharP R 2] [NoZeroDivisors R]

theorem sq_injective : Function.Injective fun x : R ↦ x ^ 2 := by
  intro x y h
  rwa [← CharTwo.add_eq_zero, ← add_sq, pow_eq_zero_iff two_ne_zero, CharTwo.add_eq_zero] at h

@[scoped simp]
theorem sq_inj {x y : R} : x ^ 2 = y ^ 2 ↔ x = y :=
  sq_injective.eq_iff

end CommRing

section DivisionRing

variable [DivisionRing R] [CharP R 2]

theorem ratCast_eq_ite (q : ℚ) : (q : R) = if Odd q.num ∧ Odd q.den then 1 else 0 := by
  rw [DivisionRing.ratCast_def, div_eq_mul_inv, natCast_eq_if, intCast_eq_if]
  aesop

@[simp]
theorem range_ratCast : Set.range ((↑) : ℚ → R) = {0, 1} := by
  rw [funext ratCast_eq_if, Set.range_if, Set.pair_comm]
  · use 1; simp
  · use 0; simp

variable (R) in
theorem ratCast_cases (q : ℚ) : (q : R) = 0 ∨ (q : R) = 1 :=
  (Set.ext_iff.1 range_ratCast _).1 (Set.mem_range_self _)

@[scoped simp]
theorem inv_ratCast (q : ℚ) : (q : R)⁻¹ = q := by
  obtain hq | hq := ratCast_cases R q <;> simp [hq]

@[scoped simp]
theorem inv_intCast (n : ℤ) : (n : R)⁻¹ = n :=
  mod_cast inv_ratCast n

@[scoped simp]
theorem inv_natCast (n : ℕ) : (n : R)⁻¹ = n :=
  mod_cast inv_ratCast n

end DivisionRing

end CharTwo

section ringChar

variable [Ring R]

theorem neg_one_eq_one_iff [Nontrivial R] : (-1 : R) = 1 ↔ ringChar R = 2 := by
  refine ⟨fun h => ?_, fun h => @CharTwo.neg_eq _ _ (ringChar.of_eq h) 1⟩
  rw [eq_comm, ← sub_eq_zero, sub_neg_eq_add, ← Nat.cast_one, ← Nat.cast_add] at h
  exact ((Nat.dvd_prime Nat.prime_two).mp (ringChar.dvd h)).resolve_left CharP.ringChar_ne_one

@[simp]
theorem orderOf_neg_one [Nontrivial R] : orderOf (-1 : R) = if ringChar R = 2 then 1 else 2 := by
  split_ifs with h
  · rw [neg_one_eq_one_iff.2 h, orderOf_one]
  apply orderOf_eq_prime
  · simp
  simpa [neg_one_eq_one_iff] using h

end ringChar

section CharP

variable [Ring R]

lemma CharP.orderOf_eq_two_iff [Nontrivial R] [NoZeroDivisors R] (p : ℕ)
    (hp : p ≠ 2) [CharP R p] {x : R} : orderOf x = 2 ↔ x = -1 := by
  simp only [orderOf_eq_prime_iff, sq_eq_one_iff, ne_eq, or_and_right, and_not_self, false_or,
    and_iff_left_iff_imp]
  rintro rfl
  exact fun h ↦ hp ((ringChar.eq R p) ▸ (neg_one_eq_one_iff.1 h))

end CharP
