/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
public import Mathlib.Topology.Instances.Shrink

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

/-! ### Lemmas about integers -/

instance : AddGroup.ResiduallyFinite ℤ := by
  rw [AddGroup.residuallyFinite_iff_exists_finiteIndex]
  intro g hg
  refine ⟨AddSubgroup.zmultiples (|g| + 1), ?_, ?_⟩
  · rw [AddSubgroup.finiteIndex_iff, Int.index_zmultiples]
    positivity
  · rw [Int.mem_zmultiples_iff]
    intro hg'
    simpa using Int.le_abs_of_dvd hg hg'

/-- The finite index (normal) subgroups of ℤ are exactly `AddSubgroup.zmultiples n` for `n : ℕ+`. -/
noncomputable def Int.finiteIndexNormalSubgroupEquiv : FiniteIndexNormalAddSubgroup ℤ ≃ ℕ+ where
  toFun G := ⟨(Classical.choose (IsAddCyclic.zmultiples_surjective G.toAddSubgroup)).natAbs, by
    generalize_proofs H
    have ⟨n, hn⟩ := H
    rw [Nat.pos_iff_ne_zero, natAbs_ne_zero]
    intro h0
    have := (h0 ▸ Classical.choose_spec H).symm
    simp at this
  ⟩
  invFun n := ⟨AddSubgroup.zmultiples n, inferInstance, ⟨by simp⟩⟩
  left_inv G := by
    ext x
    dsimp
    generalize_proofs H
    rw [zmultiples_natAbs, Classical.choose_spec H]
  right_inv n := by
    apply PNat.coe_injective
    dsimp
    generalize_proofs H H'
    have := Classical.choose_spec H
    rw [AddSubgroup.zmultiples_eq_zmultiples_iff_of_isAddTorsionFree] at this
    rwa [natAbs_eq_iff, ← neg_eq_iff_eq_neg]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
theorem Int.finiteIndexNormalSubgroupEquiv_apply (G : FiniteIndexNormalAddSubgroup ℤ) :
    finiteIndexNormalSubgroupEquiv G = ⟨G.index, G.isFiniteIndex'.index_ne_zero.pos⟩ := by
  rw [finiteIndexNormalSubgroupEquiv]
  apply PNat.coe_injective
  dsimp
  generalize_proofs H
  conv_rhs => rw [← Classical.choose_spec H, index_zmultiples]

@[simp]
theorem Int.finiteIndexNormalSubgroupEquiv_symm_apply (n : ℕ+) :
    finiteIndexNormalSubgroupEquiv.symm n =
      ⟨AddSubgroup.zmultiples n, inferInstance, ⟨by simp⟩⟩ :=
  (rfl)

/-! ### The profinite completion of integers -/

/-- The profinite completion of the integers $\widehat{\mathbb Z}$. -/
abbrev ZHat : Type :=
  completion (.mk ℤ)

namespace ZHat

-- We build a version with more general universes below.
private noncomputable def lift' {G : Type} [AddGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (f : ℤ →+ G) :
    ZHat →ₜ+ G :=
  (ProfiniteAddGrp.ProfiniteCompletion.lift (P := .of G) (AddGrpCat.ofHom f)).hom

noncomputable def lift {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (f : ℤ →+ G) : ZHat →ₜ+ G :=
  have : Small.{0} f.range := small_range f
  have : Small.{0} f.range.topologicalClosure := small_closure _
  have : CompactSpace f.range.topologicalClosure :=
    isCompact_iff_compactSpace.1 (AddSubgroup.isClosed_topologicalClosure _).isCompact
  ContinuousAddMonoidHom.comp
    ⟨f.range.topologicalClosure.subtype, continuous_iff_le_induced.mpr fun _ ↦ id⟩ <|
  (ContinuousAddMonoidHom.toContinuousAddMonoidHom Shrink.continuousAddEquiv).comp <| lift' <|
    Shrink.addEquiv.symm.toAddMonoidHom.comp <|
      (AddSubgroup.inclusion <| AddSubgroup.le_topologicalClosure _).comp f.rangeRestrict

instance : IntCast ZHat where
  intCast := etaFn (.mk ℤ)

instance : AddMonoidWithOne ZHat where
  natCast n := (n : ℤ)
  one := (1 : ℤ)

instance : CharZero ZHat where
  cast_injective x y h := by
    rw [← Nat.cast_inj (R := ℤ)]
    apply (etaFn_injective_iff_residuallyFinite _).2 _ h
    infer_instance

/-- The subring of sequences `f (n : ℕ+) : ZMod n` satisfying the following compatibility condition:
if `m ∣ n`, then `f m` equals `f n` mod `m`.

As an additive group, this is isomorphic to `ZHat`, and we use this isomorphism to give it its ring
structure. -/
def compatibleSeq : Subring (Π n : ℕ+, ZMod n) where
  carrier := {f | ∀ (m n : ℕ+) (h : (m : ℕ) ∣ n), ZMod.castHom h (ZMod m) (f n) = f m }
  zero_mem' := by simp
  neg_mem' := fun {x} hx => by
    simp only [ZMod.castHom_apply, Set.mem_ofPred_eq, Pi.neg_apply] at *
    intro m n h
    rw [ZMod.cast_neg h, hx _ _ h, neg_inj]
  add_mem' := fun {a b} ha hb => by
    simp only [ZMod.castHom_apply, Set.mem_ofPred_eq, Pi.add_apply] at *
    intro m n h
    rw [ZMod.cast_add h, ha _ _ h, hb _ _ h]
  one_mem' := by
    simp only [ZMod.castHom_apply, Set.mem_ofPred_eq, Pi.one_apply]
    intro m n h
    rw [ZMod.cast_one h]
  mul_mem' := fun {a b} ha hb => by
    simp only [ZMod.castHom_apply, Set.mem_ofPred_eq, Pi.mul_apply] at *
    intro m n h
    rw [ZMod.cast_mul h, ha _ _ h, hb _ _ h]

private def piIso :
    (Π n : ℕ+, ZMod n) ≃+ Π H : FiniteIndexNormalAddSubgroup ℤ, ℤ ⧸ H.toAddSubgroup :=
  (AddEquiv.piCongrRight (fun n : ℕ+ ↦ Int.quotientZMultiplesNatEquivZMod n)).symm.trans sorry

private def compatibleSeqIso' : ZHat ≃+ compatibleSeq :=
  (AddEquiv.addSubgroupCongr sorry).comp <| AddEquiv.addSubgroupMap

end ZHat
