/-
Copyright (c) 2026 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion

/-!
# cool docstring
-/

universe u

@[expose] public section

-- TODO: generalize universes
variable {G H : Type u} [Group G] [Group H] [TopologicalSpace H] [CompactSpace H] [T2Space H]
  [TotallyDisconnectedSpace H] [IsTopologicalGroup H]

variable (G) in
/-- The profinite completion of a group is the direct limit of all its finite subquotients. -/
def ProfiniteCompletion : Type _ := ProfiniteGrp.ProfiniteCompletion.completion (.mk G)
  deriving Group, TopologicalSpace, CompactSpace, T2Space, TotallyDisconnectedSpace,
  IsTopologicalGroup

namespace ProfiniteCompletion

def mk : G →* ProfiniteCompletion G :=
  (ProfiniteGrp.ProfiniteCompletion.eta (.mk G)).hom

theorem denseRange_mk : DenseRange (mk (G := G)) :=
  ProfiniteGrp.ProfiniteCompletion.denseRange _

noncomputable def lift (f : G →* H) : ProfiniteCompletion G →ₜ* H :=
  (ProfiniteGrp.ProfiniteCompletion.lift (P := .mk (.of H)) (GrpCat.ofHom f)).hom

end ProfiniteCompletion
