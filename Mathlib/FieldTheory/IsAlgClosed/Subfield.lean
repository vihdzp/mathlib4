/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Algebraically closed subfields

We define a convenience predicate for algebraically closed subfields of an algebraically closed
field,
-/

variable {k : Type u} [Field k] [IsAlgClosed k]

namespace Subfield

/-- An algebraically closed subfield of an algebraically closed field. -/
def IsAlgClosed (s : Subfield k) : Prop :=
  _root_.IsAlgClosed s

theorem IsAlgClosed.to_subtype {s : Subfield k} (h : IsAlgClosed s) : _root_.IsAlgClosed s := h

theorem IsAlgClosed.exists_root (p : k[X]) (hp : p.degree ≠ 0) (hp' : ∀ n, p.coeff n ∈ s) :
    ∃ x ∈ s, IsRoot p x :=
  (IsAlgClosed.splits p).exists_eval_eq_zero hp

end Subfield
