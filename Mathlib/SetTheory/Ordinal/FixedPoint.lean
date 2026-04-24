/-
Copyright (c) 2018 Violeta Hernández Palacios, Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Mario Carneiro
-/
module

public import Mathlib.Logic.Small.List
public import Mathlib.SetTheory.Cardinal.Club
public import Mathlib.SetTheory.Ordinal.Enum
public import Mathlib.SetTheory.Ordinal.Exponential

/-!
# Fixed points of normal functions

We prove various statements about the fixed points of normal ordinal functions. We state them in
two forms: as statements about indexed families of normal functions, and as statements about a
single normal function.

Moreover, we prove some lemmas about the fixed points of specific normal functions.

## Main definitions and results

* `nfpFamily`, `nfp`: the next fixed point of a (family of) normal function(s).
* `not_bddAbove_fp_family`, `not_bddAbove_fp`: the (common) fixed points of a (family of) normal
  function(s) are unbounded in the ordinals.
* `deriv_add_eq_mul_omega0_add`: a characterization of the derivative of addition.
* `deriv_mul_eq_opow_omega0_mul`: a characterization of the derivative of multiplication.
-/

@[expose] public noncomputable section

universe u v

open Function Order

namespace Ordinal

open Cardinal in
private theorem isClub_sInter_fixedPoints
    {s : Set (Ordinal.{u} → Ordinal.{u})} [Small.{u} s] (hs : ∀ f ∈ s, IsNormal f) :
    IsClub (⋂₀ (fixedPoints '' s)) := by
  have h : cof Ordinal.{u} ≠ ℵ₀ := by simp
  refine .sInter h (mk_image_le.trans_lt ?_) ?_
  · rwa [← Cardinal.lift_id #s, cof_ordinal, ← small_iff_lift_mk_lt_univ]
  · rw [Set.forall_mem_image]
    exact fun f hf ↦ (hs f hf).isClub_fixedPoints h

/-! ### Fixed points of a set of normal functions -/

/-- Given a small set of normal functions, `derivSet` returns the function which enumerates their
common fixed points. -/
def derivSet (s : Set (Ordinal.{u} → Ordinal.{u})) [Small.{u} s] (hs : ∀ f ∈ s, IsNormal f) :
    Ordinal → Ordinal :=
  Subtype.val ∘ Order.enum (⋂₀ (Function.fixedPoints '' s))
    (by exact (isClub_sInter_fixedPoints hs).isCofinal)

/-- The next fixed point of a set of normal functions, i.e. the smallest common fixed point larger
than `x`. -/
def nfpSet (s : Set (Ordinal → Ordinal)) (x : Ordinal) : Ordinal :=
  ⨆ i : List s, List.foldr Subtype.val x i

section derivSet
variable {s : Set (Ordinal.{u} → Ordinal.{u})} [Small.{u} s] (hs : ∀ f ∈ s, IsNormal f)
  {x y : Ordinal.{u}}

@[simp]
theorem range_derivSet : .range (derivSet s hs) = ⋂ f ∈ s, fixedPoints f := by
  ext; simp [derivSet]

theorem mem_range_derivSet : x ∈ Set.range (derivSet s hs) ↔ ∀ f ∈ s, IsFixedPt f x := by
  simp

theorem isFixedPt_derivSet {f : Ordinal → Ordinal} (hf : f ∈ s) : f.IsFixedPt (derivSet s hs x) :=
  (mem_range_derivSet ..).1 (Set.mem_range_self x) f hf

theorem isNormal_derivSet : IsNormal (derivSet s hs) :=
  (isClub_sInter_fixedPoints hs).isNormal_enum

@[simp]
theorem derivSet_le_derivSet_iff : derivSet s hs x ≤ derivSet s hs y ↔ x ≤ y :=
  (isNormal_derivSet hs).strictMono.le_iff_le

@[simp]
theorem derivSet_lt_derivSet_iff : derivSet s hs x < derivSet s hs y ↔ x < y :=
  (isNormal_derivSet hs).strictMono.lt_iff_lt

@[simp]
theorem derivSet_inj : derivSet s hs x = derivSet s hs y ↔ x = y :=
  (isNormal_derivSet hs).strictMono.injective.eq_iff

theorem derivSet_le_of_forall_lt (hx : ∀ f ∈ s, IsFixedPt f x)
    (hf : ∀ z < y, derivSet s hs z < x) : derivSet s hs y ≤ x :=
  enum_le_of_forall_lt (by simpa) (by simpa)

variable (s x) in
theorem le_nfpSet : x ≤ nfpSet s x :=
  Ordinal.le_iSup _ []

theorem isFixedPt_nfpSet (hs : ∀ f ∈ s, IsNormal f) {f : Ordinal → Ordinal} (hf : f ∈ s) :
    f.IsFixedPt (nfpSet s x) := by
  apply (hs f hf).strictMono.le_apply.antisymm'
  rw [nfpSet, (hs f hf).map_iSup bddAbove_of_small]
  exact ciSup_le fun l ↦ Ordinal.le_iSup _ (⟨f, hf⟩ :: l)

omit [Small s] in
theorem nfpSet_le_of_isFixedPt (hs : ∀ f ∈ s, IsNormal f)
    (hx : x ≤ y) (hy : ∀ f ∈ s, f.IsFixedPt y) : nfpSet s x ≤ y := by
  refine Ordinal.iSup_le fun l ↦ ?_
  induction l with
  | nil => exact hx
  | cons a l IH => exact hy _ a.2 ▸ (hs _ a.2).monotone IH

theorem nfpSet_mono (hs : ∀ f ∈ s, IsNormal f) : Monotone (nfpSet s) :=
  fun _ y h ↦ nfpSet_le_of_isFixedPt hs (h.trans (le_nfpSet s y)) fun _ ↦ isFixedPt_nfpSet hs

theorem nfpSet_of_isFixedPt (hs : ∀ f ∈ s, IsNormal f) (hx : ∀ f ∈ s, f.IsFixedPt x) :
    nfpSet s x = x :=
  (nfpSet_le_of_isFixedPt hs le_rfl hx).antisymm (le_nfpSet s x)

theorem derivSet_zero : derivSet s hs 0 = nfpSet s 0 := by
  apply (derivSet_le_of_forall_lt ..).antisymm
  · exact nfpSet_le_of_isFixedPt hs bot_le fun _ ↦ isFixedPt_derivSet hs
  · exact fun _ ↦ isFixedPt_nfpSet hs
  · simp

theorem derivSet_add_one : derivSet s hs (x + 1) = nfpSet s (derivSet s hs x + 1) := by
  apply (derivSet_le_of_forall_lt ..).antisymm
  · apply nfpSet_le_of_isFixedPt hs _ fun _ ↦ isFixedPt_derivSet hs
    simp
  · exact fun _ ↦ isFixedPt_nfpSet hs
  · refine fun y hy ↦ (le_nfpSet ..).trans_lt' ?_
    simpa using hy

end derivSet

/-! ### Fixed points of a single normal function -/

/-- Given a normal function, `deriv` returns the function which enumerates its fixed points. -/
def deriv (f : Ordinal → Ordinal) (hf : IsNormal f) : Ordinal → Ordinal :=
  derivSet {f} (by simpa)

/-- The next fixed point of a normal function, i.e. the smallest fixed point larger than `x`. -/
def nfp (f : Ordinal → Ordinal) (x : Ordinal) : Ordinal :=
  nfpSet {f} x

section deriv
variable {f : Ordinal.{u} → Ordinal.{u}} (hf : IsNormal f) {x y : Ordinal.{u}}

@[simp]
theorem derivSet_singleton : derivSet {f} (by simpa) = deriv f hf :=
  rfl

@[simp]
theorem nfpSet_singleton (f : Ordinal → Ordinal) (x : Ordinal) : nfpSet {f} x = nfp f x :=
  rfl

theorem nfp_eq_iSup_iterate (f : Ordinal → Ordinal) (x : Ordinal) : nfp f x = ⨆ n, f^[n] x := by
  unfold nfp nfpSet iSup
  rw [← EquivLike.range_comp _ (Equiv.listUniqueEquiv _).symm]
  congr! with n
  induction n with
  | zero => rfl
  | succ n IH =>
    rw [Function.iterate_succ_apply']
    simp_all [List.replicate_succ]

@[simp]
theorem nfp_id : nfp id = id := by
  ext
  simp [nfp_eq_iSup_iterate]

@[simp]
theorem range_deriv : .range (deriv f hf) = fixedPoints f := by
  ext; simp [deriv]

theorem mem_range_deriv : x ∈ Set.range (deriv f hf) ↔ IsFixedPt f x := by
  simp

theorem isFixedPt_deriv : f.IsFixedPt (deriv f hf x) :=
  (mem_range_deriv ..).1 (Set.mem_range_self x)

theorem isNormal_deriv : IsNormal (deriv f hf) :=
  isNormal_derivSet (by simpa)

@[simp]
theorem deriv_le_deriv_iff : deriv f hf x ≤ deriv f hf y ↔ x ≤ y :=
  (isNormal_deriv hf).strictMono.le_iff_le

@[simp]
theorem deriv_lt_deriv_iff : deriv f hf x < deriv f hf y ↔ x < y :=
  (isNormal_deriv hf).strictMono.lt_iff_lt

@[simp]
theorem deriv_inj : deriv f hf x = deriv f hf y ↔ x = y :=
  (isNormal_deriv hf).strictMono.injective.eq_iff

theorem deriv_le_of_forall_lt (hx : IsFixedPt f x) (hf' : ∀ z < y, deriv f hf z < x) :
    deriv f hf y ≤ x :=
  enum_le_of_forall_lt (by simpa) (by simpa)

variable (x) in
theorem le_nfp : x ≤ nfp f x :=
  le_nfpSet _ x

@[simp]
theorem nfp_zero_left : nfp 0 = id := by
  ext x
  apply (le_nfp _).antisymm'
  rw [nfp_eq_iSup_iterate, Ordinal.iSup_le_iff]
  rintro (_ | _)
  · simp
  · rw [Function.iterate_succ_apply']; simp

theorem isFixedPt_nfp (hf : IsNormal f) {x : Ordinal} : f.IsFixedPt (nfp f x) :=
  isFixedPt_nfpSet (by simpa) (by simp)

theorem nfp_le_of_isFixedPt (hf : IsNormal f) (hx : x ≤ y) (hy : f.IsFixedPt y) : nfp f x ≤ y :=
  nfpSet_le_of_isFixedPt (by simpa) hx (by simpa)

theorem nfp_mono (hf : IsNormal f) : Monotone (nfp f) :=
  nfpSet_mono (by simpa)

theorem nfp_of_isFixedPt (hf : IsNormal f) (hx : f.IsFixedPt x) : nfp f x = x :=
  nfpSet_of_isFixedPt (by simpa) (by simpa)

theorem deriv_zero : deriv f hf 0 = nfp f 0 :=
  derivSet_zero (by simpa)

theorem deriv_add_one : deriv f hf (x + 1) = nfp f (deriv f hf x + 1) :=
  derivSet_add_one (by simpa)

end deriv

end Ordinal

namespace Ordinal

/-! ### Deprecated material -/

section

variable {ι : Type*} {f : ι → Ordinal.{u} → Ordinal.{u}}

/-- The next common fixed point, at least `a`, for a family of normal functions.

This is defined for any family of functions, as the supremum of all values reachable by applying
finitely many functions in the family to `a`.

`Ordinal.nfpFamily_fp` shows this is a fixed point, `Ordinal.le_nfpFamily` shows it's at
least `a`, and `Ordinal.nfpFamily_le_fp` shows this is the least ordinal with these properties. -/
@[deprecated nfpSet (since := "2026-04-24")]
def nfpFamily (f : ι → Ordinal.{u} → Ordinal.{u}) (a : Ordinal.{u}) : Ordinal :=
  ⨆ i, List.foldr f a i

set_option linter.deprecated false in
@[deprecated "`nfpFamily` is deprecated" (since := "2026-04-24")]
theorem foldr_le_nfpFamily [Small.{u} ι] (f : ι → Ordinal.{u} → Ordinal.{u}) (a l) :
    List.foldr f a l ≤ nfpFamily f a :=
  Ordinal.le_iSup _ _

set_option linter.deprecated false in
@[deprecated le_nfpSet (since := "2026-04-24")]
theorem le_nfpFamily [Small.{u} ι] (f : ι → Ordinal.{u} → Ordinal.{u}) (a) : a ≤ nfpFamily f a :=
  foldr_le_nfpFamily f a []

set_option linter.deprecated false in
@[deprecated "`nfpFamily` is deprecated" (since := "2026-04-24")]
theorem lt_nfpFamily_iff [Small.{u} ι] {a b} : a < nfpFamily f b ↔ ∃ l, a < List.foldr f b l :=
  Ordinal.lt_iSup_iff

set_option linter.deprecated false in
@[deprecated "`nfpFamily` is deprecated" (since := "2026-04-24")]
theorem nfpFamily_le_iff [Small.{u} ι] {a b} : nfpFamily f a ≤ b ↔ ∀ l, List.foldr f a l ≤ b :=
  Ordinal.iSup_le_iff

set_option linter.deprecated false in
@[deprecated "`nfpFamily` is deprecated" (since := "2026-04-24")]
theorem nfpFamily_le {a b} : (∀ l, List.foldr f a l ≤ b) → nfpFamily f a ≤ b :=
  Ordinal.iSup_le

set_option linter.deprecated false in
@[deprecated nfpSet_mono (since := "2026-04-24")]
theorem nfpFamily_monotone [Small.{u} ι] (hf : ∀ i, Monotone (f i)) : Monotone (nfpFamily f) :=
  fun _ _ h ↦ nfpFamily_le <| fun l ↦ (List.foldr_monotone hf l h).trans (foldr_le_nfpFamily _ _ l)

set_option linter.deprecated false in
@[deprecated "`nfpFamily` is deprecated" (since := "2026-04-24")]
theorem apply_lt_nfpFamily [Small.{u} ι] (H : ∀ i, IsNormal (f i)) {a b}
    (hb : b < nfpFamily f a) (i) : f i b < nfpFamily f a :=
  let ⟨l, hl⟩ := lt_nfpFamily_iff.1 hb
  lt_nfpFamily_iff.2 ⟨i::l, (H i).strictMono hl⟩

set_option linter.deprecated false in
@[deprecated "`nfpFamily` is deprecated" (since := "2026-04-24")]
theorem apply_lt_nfpFamily_iff [Nonempty ι] [Small.{u} ι] (H : ∀ i, IsNormal (f i)) {a b} :
    (∀ i, f i b < nfpFamily f a) ↔ b < nfpFamily f a := by
  refine ⟨fun h ↦ ?_, apply_lt_nfpFamily H⟩
  let ⟨l, hl⟩ := lt_nfpFamily_iff.1 (h (Classical.arbitrary ι))
  exact lt_nfpFamily_iff.2 <| ⟨l, (H _).strictMono.le_apply.trans_lt hl⟩

set_option linter.deprecated false in
@[deprecated "`nfpFamily` is deprecated" (since := "2026-04-24")]
theorem nfpFamily_le_apply [Nonempty ι] [Small.{u} ι] (H : ∀ i, IsNormal (f i)) {a b} :
    (∃ i, nfpFamily f a ≤ f i b) ↔ nfpFamily f a ≤ b := by
  contrapose!; exact apply_lt_nfpFamily_iff H

set_option linter.deprecated false in
@[deprecated nfpSet_le_of_isFixedPt (since := "2026-04-24")]
theorem nfpFamily_le_fp (H : ∀ i, Monotone (f i)) {a b} (ab : a ≤ b) (h : ∀ i, f i b ≤ b) :
    nfpFamily f a ≤ b := by
  apply Ordinal.iSup_le fun l ↦ ?_
  induction l generalizing a with
  | nil => exact ab
  | cons i l IH => exact (H i (IH ab)).trans (h i)

set_option linter.deprecated false in
@[deprecated isFixedPt_nfpSet (since := "2026-04-24")]
theorem nfpFamily_fp [Small.{u} ι] {i} (H : IsNormal (f i)) (a) :
    f i (nfpFamily f a) = nfpFamily f a := by
  rw [nfpFamily, H.map_iSup bddAbove_of_small]
  apply le_antisymm <;> refine Ordinal.iSup_le fun l => ?_
  · exact Ordinal.le_iSup _ (i::l)
  · exact H.strictMono.le_apply.trans (Ordinal.le_iSup _ _)

set_option linter.deprecated false in
@[deprecated "`nfpFamily` is deprecated" (since := "2026-04-24")]
theorem apply_le_nfpFamily [Small.{u} ι] [hι : Nonempty ι] (H : ∀ i, IsNormal (f i)) {a b} :
    (∀ i, f i b ≤ nfpFamily f a) ↔ b ≤ nfpFamily f a := by
  refine ⟨fun h => ?_, fun h i => ?_⟩
  · obtain ⟨i⟩ := hι
    exact (H i).strictMono.le_apply.trans (h i)
  · rw [← nfpFamily_fp (H i)]
    exact (H i).monotone h

set_option linter.deprecated false in
@[deprecated nfpSet_of_isFixedPt (since := "2026-04-24")]
theorem nfpFamily_eq_self [Small.{u} ι] {a} (h : ∀ i, f i a = a) : nfpFamily f a = a := by
  apply (Ordinal.iSup_le ?_).antisymm (le_nfpFamily f a)
  intro l
  rw [List.foldr_fixed' h l]

set_option linter.deprecated false in
-- Todo: This is actually a special case of the fact the intersection of club sets is a club set.
/-- A generalization of the fixed point lemma for normal functions: any family of normal functions
    has an unbounded set of common fixed points. -/
@[deprecated IsNormal.isClub_fixedPoints (since := "2026-04-24")]
theorem not_bddAbove_fp_family [Small.{u} ι] (H : ∀ i, IsNormal (f i)) :
    ¬ BddAbove (⋂ i, Function.fixedPoints (f i)) := by
  rw [not_bddAbove_iff]
  refine fun a ↦ ⟨nfpFamily f (succ a), ?_, (lt_succ a).trans_le (le_nfpFamily f _)⟩
  rintro _ ⟨i, rfl⟩
  exact nfpFamily_fp (H i) _

set_option linter.deprecated false in
/-- The derivative of a family of normal functions is the sequence of their common fixed points.

This is defined for all functions such that `Ordinal.derivFamily_zero`,
`Ordinal.derivFamily_succ`, and `Ordinal.derivFamily_limit` are satisfied. -/
@[deprecated derivSet (since := "2026-04-24")]
def derivFamily (f : ι → Ordinal.{u} → Ordinal.{u}) (o : Ordinal.{u}) : Ordinal.{u} :=
  limitRecOn o (nfpFamily f 0) (fun _ IH => nfpFamily f (succ IH))
    fun a _ g => ⨆ b : Set.Iio a, g _ b.2

set_option linter.deprecated false in
@[deprecated derivSet_zero (since := "2026-04-24")]
theorem derivFamily_zero (f : ι → Ordinal → Ordinal) :
    derivFamily f 0 = nfpFamily f 0 :=
  limitRecOn_zero ..

set_option linter.deprecated false in
@[deprecated derivSet_add_one (since := "2026-04-24")]
theorem derivFamily_add_one (f : ι → Ordinal → Ordinal) (o) :
    derivFamily f (o + 1) = nfpFamily f (derivFamily f o + 1) :=
  limitRecOn_succ ..

set_option linter.deprecated false in
@[deprecated derivSet_add_one (since := "2026-04-24")]
theorem derivFamily_succ (f : ι → Ordinal → Ordinal) (o) :
    derivFamily f (succ o) = nfpFamily f (succ (derivFamily f o)) :=
  derivFamily_add_one f o

set_option linter.deprecated false in
@[deprecated isNormal_derivSet (since := "2026-04-24")]
theorem derivFamily_limit (f : ι → Ordinal → Ordinal) {o} :
    IsSuccLimit o → derivFamily f o = ⨆ b : Set.Iio o, derivFamily f b :=
  limitRecOn_limit _ _ _ _

set_option linter.deprecated false in
@[deprecated isNormal_derivSet (since := "2026-04-24")]
theorem isNormal_derivFamily [Small.{u} ι] (f : ι → Ordinal.{u} → Ordinal.{u}) :
    IsNormal (derivFamily f) := by
  refine IsNormal.of_succ_lt (fun o ↦ ?_) @fun o h ↦ ?_
  · rw [derivFamily_succ, ← succ_le_iff]
    exact le_nfpFamily _ _
  · rw [derivFamily_limit _ h, Set.image_eq_range]
    have := h.nonempty_Iio.to_subtype
    exact isLUB_ciSup bddAbove_of_small

set_option linter.deprecated false in
@[deprecated isNormal_derivSet (since := "2026-04-24")]
theorem derivFamily_strictMono [Small.{u} ι] (f : ι → Ordinal.{u} → Ordinal.{u}) :
    StrictMono (derivFamily f) :=
  (isNormal_derivFamily f).strictMono

set_option linter.deprecated false in
@[deprecated isFixedPt_derivSet (since := "2026-04-24")]
theorem derivFamily_fp [Small.{u} ι] {i} (H : IsNormal (f i)) (o : Ordinal) :
    f i (derivFamily f o) = derivFamily f o := by
  induction o using limitRecOn with
  | zero =>
    rw [derivFamily_zero]
    exact nfpFamily_fp H 0
  | succ =>
    rw [derivFamily_succ]
    exact nfpFamily_fp H _
  | limit o l IH =>
    have := l.nonempty_Iio.to_subtype
    rw [derivFamily_limit _ l, H.map_iSup bddAbove_of_small]
    refine eq_of_forall_ge_iff fun c => ?_
    rw [Ordinal.iSup_le_iff, Ordinal.iSup_le_iff]
    refine forall_congr' fun a ↦ ?_
    rw [IH _ a.2]

set_option linter.deprecated false in
@[deprecated range_derivSet (since := "2026-04-24")]
theorem le_iff_derivFamily [Small.{u} ι] (H : ∀ i, IsNormal (f i)) {a} :
    (∀ i, f i a ≤ a) ↔ ∃ o, derivFamily f o = a :=
  ⟨fun ha => by
    suffices ∀ (o), a ≤ derivFamily f o → ∃ o, derivFamily f o = a from
      this a (isNormal_derivFamily _).strictMono.le_apply
    intro o
    induction o using limitRecOn with
    | zero =>
      intro h₁
      refine ⟨0, le_antisymm ?_ h₁⟩
      rw [derivFamily_zero]
      exact nfpFamily_le_fp (fun i => (H i).monotone) (zero_le _) ha
    | succ o IH =>
      intro h₁
      rcases le_or_gt a (derivFamily f o) with h | h
      · exact IH h
      refine ⟨succ o, le_antisymm ?_ h₁⟩
      rw [derivFamily_succ]
      exact nfpFamily_le_fp (fun i => (H i).monotone) (succ_le_of_lt h) ha
    | limit o l IH =>
      intro h₁
      rcases eq_or_lt_of_le h₁ with h | h
      · exact ⟨_, h.symm⟩
      rw [derivFamily_limit _ l, ← not_le, Ordinal.iSup_le_iff, not_forall] at h
      obtain ⟨o', h⟩ := h
      exact IH o' o'.2 (le_of_not_ge h),
    fun ⟨_, e⟩ i => e ▸ (derivFamily_fp (H i) _).le⟩

set_option linter.deprecated false in
@[deprecated range_derivSet (since := "2026-04-24")]
theorem fp_iff_derivFamily [Small.{u} ι] (H : ∀ i, IsNormal (f i)) {a} :
    (∀ i, f i a = a) ↔ ∃ o, derivFamily f o = a :=
  Iff.trans ⟨fun h i => le_of_eq (h i), fun h i => (H i).strictMono.le_apply.ge_iff_eq'.1 (h i)⟩
    (le_iff_derivFamily H)

set_option linter.deprecated false in
@[deprecated mem_range_derivSet (since := "2026-04-24")]
theorem mem_range_derivFamily [Small.{u} ι] (H : ∀ i, IsNormal (f i)) {a} :
    a ∈ Set.range (derivFamily f) ↔ ∀ i, f i a = a :=
  (fp_iff_derivFamily H).symm

set_option linter.deprecated false in
/-- For a family of normal functions, `Ordinal.derivFamily` enumerates the common fixed points. -/
@[deprecated "`derivFamily` is deprecated" (since := "2026-04-24")]
theorem derivFamily_eq_enumOrd [Small.{u} ι] (H : ∀ i, IsNormal (f i)) :
    derivFamily f = enumOrd (⋂ i, Function.fixedPoints (f i)) := by
  rw [eq_comm, eq_enumOrd _ (not_bddAbove_fp_family H)]
  use (isNormal_derivFamily f).strictMono
  rw [Set.range_eq_iff]
  refine ⟨?_, fun a ha => ?_⟩
  · rintro a S ⟨i, hi⟩
    rw [← hi]
    exact derivFamily_fp (H i) a
  rw [Set.mem_iInter] at ha
  rwa [← fp_iff_derivFamily H]

end

section

variable {f : Ordinal.{u} → Ordinal.{u}}

@[deprecated (since := "2026-04-24")] alias iSup_iterate_eq_nfp := nfp_eq_iSup_iterate

@[deprecated (since := "2026-04-24")] alias nfp_monotone := nfp_mono

@[deprecated (since := "2026-04-24")] alias nfp_le_fp := nfp_le_of_isFixedPt

@[deprecated (since := "2026-04-24")] alias nfp_fp := isFixedPt_nfp

@[deprecated (since := "2025-12-25")]
alias IsNormal.nfp_fp := nfp_fp

@[deprecated (since := "2026-04-24")] alias nfp_eq_self := nfp_of_isFixedPt

set_option linter.deprecated false in
/-- The fixed point lemma for normal functions: any normal function has an unbounded set of
fixed points. -/
@[deprecated IsNormal.isClub_fixedPoints (since := "2026-04-24")]
theorem not_bddAbove_fp (H : IsNormal f) : ¬ BddAbove (Function.fixedPoints f) := by
  convert not_bddAbove_fp_family fun _ : Unit => H
  exact (Set.iInter_const _).symm

@[deprecated (since := "2026-04-24")] alias deriv_eq_derivFamily := derivSet_singleton

@[deprecated (since := "2026-04-24")] alias deriv_succ := deriv_add_one

@[deprecated (since := "2026-04-24")] alias deriv_fp := isFixedPt_deriv

@[deprecated (since := "2025-10-25")]
alias IsNormal.deriv_fp := deriv_fp

@[deprecated (since := "2026-04-24")] alias le_iff_deriv := range_deriv

@[deprecated (since := "2025-10-25")]
alias IsNormal.le_iff_deriv := le_iff_deriv

@[deprecated (since := "2026-04-24")] alias deriv_zero_right := deriv_zero

end

/-! ### Fixed points of addition -/

@[simp]
theorem nfp_add_zero (a) : nfp (a + ·) 0 = a * ω := by
  simp [nfp_eq_iSup_iterate]

theorem nfp_add_eq_mul_omega0 {a b} (hba : b ≤ a * ω) : nfp (a + ·) b = a * ω := by
  apply (nfp_le_of_isFixedPt (isNormal_add_right a) hba _).antisymm
  · rw [← nfp_add_zero]
    exact nfp_mono (isNormal_add_right a) (zero_le _)
  · rw [IsFixedPt, ← mul_one_add, one_add_omega0]

theorem add_eq_right_iff_mul_omega0_le {a b : Ordinal} : a + b = b ↔ a * ω ≤ b := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← nfp_add_zero a, ← deriv_zero (isNormal_add_right a)]
    obtain ⟨c, hc⟩ := (mem_range_deriv (isNormal_add_right a)).2 h
    rw [← hc]
    exact (isNormal_deriv _).monotone (zero_le _)
  · have := Ordinal.add_sub_cancel_of_le h
    nth_rw 1 [← this]
    rwa [← add_assoc, ← mul_one_add, one_add_omega0]

theorem add_le_right_iff_mul_omega0_le {a b : Ordinal} : a + b ≤ b ↔ a * ω ≤ b := by
  rw [← add_eq_right_iff_mul_omega0_le]
  exact (isNormal_add_right a).strictMono.le_apply.ge_iff_eq'

theorem deriv_add_eq_mul_omega0_add (a b : Ordinal.{u}) :
    deriv (a + ·) (isNormal_add_right a) b = a * ω + b := by
  revert b
  rw [← funext_iff, IsNormal.ext_iff (isNormal_deriv _) (isNormal_add_right _)]
  refine ⟨?_, fun a h => ?_⟩
  · rw [bot_eq_zero, deriv_zero, add_zero]
    exact nfp_add_zero a
  · rw [succ_eq_add_one, deriv_add_one, h, ← add_assoc]
    exact nfp_of_isFixedPt (isNormal_add_right _)
      (add_eq_right_iff_mul_omega0_le.2 (le_self_add.trans (le_succ _)))

/-! ### Fixed points of multiplication -/

@[simp]
theorem nfp_mul_one {a : Ordinal} (ha : 0 < a) : nfp (a * ·) 1 = a ^ ω := by
  simp [nfp_eq_iSup_iterate, iSup_pow_natCast ha]

@[simp]
theorem nfp_mul_zero (a : Ordinal) : nfp (a * ·) 0 = 0 := by
  simp [nfp_eq_iSup_iterate]

theorem nfp_mul_eq_opow_omega0 {a b : Ordinal} (hb : 0 < b) (hba : b ≤ a ^ ω) :
    nfp (a * ·) b = a ^ ω := by
  rcases eq_zero_or_pos a with rfl | ha
  · rw [zero_opow omega0_ne_zero] at hba ⊢
    simp_rw [nonpos_iff_eq_zero.1 hba, zero_mul]
    exact congrFun nfp_zero_left 0
  apply le_antisymm
  · apply nfp_le_of_isFixedPt (isNormal_mul_right ha) hba
    rw [IsFixedPt, ← opow_one_add, one_add_omega0]
  rw [← nfp_mul_one ha]
  exact nfp_mono (isNormal_mul_right ha) (one_le_iff_pos.2 hb)

theorem eq_zero_or_opow_omega0_le_of_mul_eq_right {a b : Ordinal} (hab : a * b = b) :
    b = 0 ∨ a ^ ω ≤ b := by
  rcases eq_zero_or_pos a with rfl | ha
  · rw [zero_opow omega0_ne_zero]
    exact Or.inr (zero_le b)
  rw [or_iff_not_imp_left]
  intro hb
  rw [← nfp_mul_one ha]
  rw [← Ne, ← one_le_iff_ne_zero] at hb
  exact nfp_le_of_isFixedPt (isNormal_mul_right ha) hb hab

theorem mul_eq_right_iff_opow_omega0_dvd {a b : Ordinal} : a * b = b ↔ a ^ ω ∣ b := by
  rcases eq_zero_or_pos a with ha | ha
  · rw [ha, zero_mul, zero_opow omega0_ne_zero, zero_dvd_iff]
    exact eq_comm
  refine ⟨fun hab => ?_, fun h => ?_⟩
  · rw [dvd_iff_mod_eq_zero]
    rw [← div_add_mod b (a ^ ω), mul_add, ← mul_assoc, ← opow_one_add, one_add_omega0,
      add_left_cancel_iff] at hab
    rcases eq_zero_or_opow_omega0_le_of_mul_eq_right hab with hab | hab
    · exact hab
    refine (not_lt_of_ge hab (mod_lt b (opow_ne_zero ω ?_))).elim
    rwa [← pos_iff_ne_zero]
  obtain ⟨c, hc⟩ := h
  rw [hc, ← mul_assoc, ← opow_one_add, one_add_omega0]

theorem mul_le_right_iff_opow_omega0_dvd {a b : Ordinal} (ha : 0 < a) :
    a * b ≤ b ↔ (a ^ ω) ∣ b := by
  rw [← mul_eq_right_iff_opow_omega0_dvd]
  exact (isNormal_mul_right ha).strictMono.le_apply.ge_iff_eq'

theorem nfp_mul_opow_omega0_add {a c : Ordinal} (b) (ha : 0 < a) (hc : 0 < c)
    (hca : c ≤ a ^ ω) : nfp (a * ·) (a ^ ω * b + c) = a ^ ω * succ b := by
  apply le_antisymm
  · apply nfp_le_of_isFixedPt (isNormal_mul_right ha)
    · rw [mul_succ]
      gcongr
    · dsimp only; rw [IsFixedPt, ← mul_assoc, ← opow_one_add, one_add_omega0]
  · obtain ⟨d, hd⟩ :=
      mul_eq_right_iff_opow_omega0_dvd.1 (isFixedPt_nfp (isNormal_mul_right ha))
    rw [hd]
    apply mul_le_mul_right
    have := le_nfp (f := (a * ·)) (a ^ ω * b + c)
    rw [hd] at this
    have := (add_lt_add_right hc (a ^ ω * b)).trans_le this
    rw [add_zero, mul_lt_mul_iff_right₀ (opow_pos ω ha)] at this
    rwa [succ_le_iff]

theorem deriv_mul_eq_opow_omega0_mul {a : Ordinal.{u}} (ha : 0 < a) (b) :
    deriv (a * ·) (isNormal_mul_right ha) b = a ^ ω * b := by
  revert b
  rw [← funext_iff,
    IsNormal.ext_iff (isNormal_deriv _) (isNormal_mul_right (opow_pos ω ha))]
  refine ⟨?_, fun c h => ?_⟩
  · rw [bot_eq_zero, deriv_zero, nfp_mul_zero, mul_zero]
  · rw [succ_eq_add_one, deriv_add_one, h]
    exact nfp_mul_opow_omega0_add c ha zero_lt_one (one_le_iff_pos.2 (opow_pos _ ha))

end Ordinal
