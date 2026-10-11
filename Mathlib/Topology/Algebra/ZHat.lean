/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
public import Mathlib.Topology.Instances.Shrink
public import Mathlib.Topology.Instances.ZMod
public import Mathlib.Topology.Compactness.Compact

import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Profinite completion of ℤ
-/

public section

open ProfiniteAddGrp.ProfiniteCompletion

universe u

/-- The continuous multiplicative equivalence between `ULift α` and `α`. -/
@[to_additive /-- The continuous additive equivalence between `ULift α` and `α`. -/]
def ContinuousMulEquiv.ulift {M : Type*} [Mul M] [TopologicalSpace M] : ULift M ≃ₜ* M where
  __ := MulEquiv.ulift
  __ := Homeomorph.ulift

/-- Shrink `α` to a smaller universe preserves multiplication. -/
@[expose, to_additive (attr := simps!) /-- Shrink `α` to a smaller universe preserves addition. -/]
noncomputable def Shrink.continuousMulEquiv {M : Type*} [Mul M] [TopologicalSpace M] [Small.{u} M] :
    Shrink.{u} M ≃ₜ* M where
  __ := Shrink.mulEquiv
  __ := (Shrink.homeomorph _).symm

@[expose, to_additive (attr := simps!)]
def ContinuousMonoidHom.subtype {M : Type*} [Group M] [TopologicalSpace M] [IsTopologicalGroup M]
    (G : Subgroup M) : G →ₜ* M where
  __ := G.subtype

theorem small_closure {X : Type*} [TopologicalSpace X] [T2Space X] (s : Set X) [Small.{u} s] :
    Small.{u} (closure s) := by
  sorry

@[to_additive]
instance {X : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [Small.{u} X] :
    IsTopologicalGroup (Shrink.{u} X) :=
  sorry

instance {X : Type*} [TopologicalSpace X] [CompactSpace X] [Small.{u} X] :
    CompactSpace (Shrink.{u} X) :=
  sorry

instance {X : Type*} [TopologicalSpace X] [TotallyDisconnectedSpace X] [Small.{u} X] :
    TotallyDisconnectedSpace (Shrink.{u} X) :=
  sorry

/-! ### The profinite completion of integers -/

/-- The profinite completion of the integers $\widehat{\mathbb Z}$. -/
abbrev ZHat : Type :=
  completion (.mk ℤ)

namespace ZHat

instance : IntCast ZHat where
  intCast := etaFn (.mk ℤ)

instance : AddGroupWithOne ZHat where
  natCast n := (n : ℤ)
  one := (1 : ℤ)

instance : CharZero ZHat where
  cast_injective x y h := by
    rw [← Nat.cast_inj (R := ℤ)]
    apply (etaFn_injective_iff_residuallyFinite _).2 _ h
    infer_instance

theorem denseRange_intCast : DenseRange (Int.cast (R := ZHat)) :=
  denseRange _

-- We build a version with more general universes below.
private noncomputable def lift' {G : Type} [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (f : ℤ →+ G) :
    ZHat →ₜ+ G :=
  (ProfiniteAddGrp.ProfiniteCompletion.lift (P := .of G) (AddGrpCat.ofHom f)).hom

private theorem lift'_intCast {G : Type} [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (f : ℤ →+ G) (n : ℤ) :
    lift' f n = f n :=
  congrArg (fun x ↦ x n) <| lift_eta (P := .of G) (AddGrpCat.ofHom f)

noncomputable def lift {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (f : ℤ →+ G) : ZHat →ₜ+ G :=
  have : Small.{0} f.range := small_range f
  have : Small.{0} f.range.topologicalClosure := small_closure _
  have : CompactSpace f.range.topologicalClosure :=
    isCompact_iff_compactSpace.1 (AddSubgroup.isClosed_topologicalClosure _).isCompact
  (ContinuousAddMonoidHom.subtype f.range.topologicalClosure).comp <|
    (ContinuousAddMonoidHom.toContinuousAddMonoidHom Shrink.continuousAddEquiv).comp <| lift' <|
  Shrink.addEquiv.symm.toAddMonoidHom.comp <|
    (AddSubgroup.inclusion <| AddSubgroup.le_topologicalClosure _).comp f.rangeRestrict

@[simp]
theorem lift_intCast {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (f : ℤ →+ G) (n : ℤ) : lift f n = f n := by
  simp [lift, lift'_intCast, AddSubgroup.inclusion, Shrink.addEquiv, Shrink.continuousAddEquiv]

@[simp]
theorem lift_natCast {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (f : ℤ →+ G) (n : ℕ) : lift f n = f n :=
  lift_intCast f n

@[simp]
theorem lift_one {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (f : ℤ →+ G) : lift f 1 = f 1 :=
  lift_intCast f 1

theorem lift_unique {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (f g : ZHat →ₜ+ G) (h : f 1 = g 1) : f = g := by
  rw [← DFunLike.coe_fn_eq]
  apply denseRange_intCast.equalizer f.continuous g.continuous
  ext n
  apply_fun (n • ·) at h
  simpa [← map_zsmul] using h

theorem lift_unique' {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (f g : ZHat →ₜ+ G) (h : f 1 = g 1) (x) :
    f x = g x := by
  rw [lift_unique f g h]

/-- The canonical mod $n$ map. -/
noncomputable def toZMod (n : ℕ) [NeZero n] : ZHat →ₜ+ ZMod n :=
  lift (Int.castAddHom (ZMod n))

@[simp] theorem toZMod_intCast (n : ℕ) (m : ℤ) [NeZero n] : toZMod n m = m := by simp [toZMod]
@[simp] theorem toZMod_natCast (n m : ℕ) [NeZero n] : toZMod n m = m := by simp [toZMod]
@[simp] theorem toZMod_one (n : ℕ) [NeZero n] : toZMod n 1 = 1 := by simp [toZMod]

theorem cast_toZMod (x : ZHat) {m n : ℕ} (h : m ∣ n) [NeZero n] :
    haveI : NeZero m := ⟨by rintro rfl; exact NeZero.ne _ <| zero_dvd_iff.1 h⟩
    (x.toZMod n).cast = x.toZMod m := by
  generalize_proofs
  let f : ZMod n →ₜ+ ZMod m := { __ := ZMod.castHom h _ }
  apply lift_unique' (f.comp (toZMod n)) (toZMod m)
  change ZMod.castHom h (ZMod m) (toZMod n 1) = _
  rw [toZMod_one, toZMod_one, map_one]

/-! ### Compatible sequences -/

/-- The subgroup of sequences `f (n : ℕ+) : ZMod n` satisfying the following compatibility
condition: if `m ∣ n`, then `f m` equals `f n` mod `m`.

We prove that this is isomorphic to `ZHat`. -/
def compatibleSeq : AddSubgroup (Π n : ℕ+, ZMod n) where
  carrier := {f | ∀ (m n : ℕ+) (h : (m : ℕ) ∣ n), (f n).cast = f m }
  zero_mem' := by simp
  neg_mem' := fun {x} hx => by
    simp only [Set.mem_ofPred_eq, Pi.neg_apply] at *
    intro m n h
    rw [ZMod.cast_neg h, hx _ _ h, neg_inj]
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, Pi.add_apply] at *
    intro m n h
    rw [ZMod.cast_add h, ha _ _ h, hb _ _ h]

instance : CompactSpace compatibleSeq := by
  constructor
  rw [Subtype.isCompact_iff, Set.image_univ, Subtype.range_coe_subtype, SetLike.setOfPred_mem_eq]
  apply IsClosed.isCompact
  sorry

instance : TotallyDisconnectedSpace compatibleSeq := inferInstance

private noncomputable def piIso :
    (Π n : ℕ+, ZMod n) ≃+ Π H : FiniteIndexNormalAddSubgroup ℤ, ℤ ⧸ H.toAddSubgroup :=
  (AddEquiv.piCongrRight (fun n : ℕ+ ↦ Int.quotientZMultiplesNatEquivZMod n)).symm.trans <|
    AddEquiv.piCongrLeft (fun H ↦ ℤ ⧸ H.toAddSubgroup) Int.finiteIndexNormalSubgroupEquiv.symm

private noncomputable def compatibleSeqIso' : ZHat ≃+ compatibleSeq :=
  let S : AddSubgroup (Π H : FiniteIndexNormalAddSubgroup ℤ, ℤ ⧸ H.toAddSubgroup) :=
    ProfiniteAddGrp.limitConePtAux (diagram (.mk ℤ))
  (AddEquiv.addSubgroupMap piIso.symm S).trans <| AddEquiv.addSubgroupCongr <| by
    ext
    simp [piIso]
    sorry

end ZHat
