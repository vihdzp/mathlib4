/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, María Inés de Frutos-Fernández
-/
module

public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Polynomials over subrings

Given a ring `K` with a subring `R`, we construct a map from polynomials in `K[X]` with coefficients
in `R` to `R[X]`. We provide several lemmas to deal with coefficients, degree, and evaluation of
`Polynomial.toSubring`.

## Main Definitions

* `Polynomial.toSubring` : given a polynomial `P` in `K[X]` whose coefficients all belong to a
  subring `R` of the ring `K`, `P.toSubring R` is the corresponding polynomial in `R[X]`.
-/

@[expose] public section

namespace Polynomial

variable {R : Type*} [Ring R] (p : R[X]) (T : Subring R)

/-! ### `toSubring`-/

/-- Given a polynomial `p` and a subring `T` that contains the coefficients of `p`,
return the corresponding polynomial whose coefficients are in `T`. -/
def toSubring (p : R[X]) (T : Subring R) (hp : ∀ n, p.coeff n ∈ T) : T[X] where
  toFinsupp :=
  { support := p.support
    toFun n := ⟨p.coeff n, hp n⟩
    mem_support_toFun n := by rw [ne_eq, ← Subring.coe_eq_zero_iff, mem_support_iff] }

variable (hp : ∀ n, p.coeff n ∈ T)

@[simp] theorem coeff_toSubring {n : ℕ} : coeff (p.toSubring T hp) n = coeff p n := rfl

@[deprecated (since := "2026-01-31")] alias coeff_toSubring' := coeff_toSubring

@[simp] theorem support_toSubring : support (p.toSubring T hp) = support p := rfl

@[simp] theorem degree_toSubring : (p.toSubring T hp).degree = p.degree := by simp [degree]
@[simp] theorem natDegree_toSubring : (p.toSubring T hp).natDegree = p.natDegree := by
  simp [natDegree]

@[simp] theorem toSubring_leadingCoeff : ↑(p.toSubring T hp).leadingCoeff = p.leadingCoeff := rfl

@[simp] theorem toSubring_zero : toSubring (0 : R[X]) T (by simp) = 0 := rfl
@[simp] theorem toSubring_one : toSubring (1 : R[X]) T (by aesop) = 1 := by aesop

@[simp]
theorem monic_toSubring : Monic (p.toSubring T hp) ↔ Monic p := by
  rw [Monic, Monic, ← toSubring_leadingCoeff p T, OneMemClass.coe_eq_one]

@[simp]
theorem map_toSubring : (p.toSubring T hp).map (Subring.subtype T) = p := by
  ext; simp

/-! ### `ofSubring`-/

/-- Given a polynomial whose coefficients are in some subring, return the corresponding polynomial
  whose coefficients are in the ambient ring. -/
noncomputable def ofSubring (p : T[X]) : R[X] :=
  p.map T.subtype

theorem coeff_ofSubring (p : T[X]) (n : ℕ) : coeff (ofSubring T p) n = (coeff p n : T) := by
  simp [ofSubring]

@[simp]
theorem coeffs_ofSubring {p : T[X]} : (↑(p.ofSubring T).coeffs : Set R) ⊆ T := by
  simp [ofSubring, coeffs, Set.subset_def]

end Polynomial
