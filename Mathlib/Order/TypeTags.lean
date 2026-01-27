/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Simon Hudon, Yury Kudryashov
-/
module

public import Mathlib.Order.Notation

/-!
# Order-related type synonyms

In this file we define the inductive types `WithBot` and `WithTop` to add a bottom or top element to
a type respectively, as well as the abbrev `WithBotTop` which adds both.
-/

@[expose] public section

variable {α : Type*}

/-- Attach `⊥` to a type. -/
@[to_dual /-- Attach `⊤` to a type. -/]
def WithBot (α : Type*) := Option α

instance WithBot.instRepr [Repr α] : Repr (WithBot α) :=
  ⟨fun o _ =>
    match o with
    | none => "⊥"
    | some a => "↑" ++ repr a⟩

@[to_dual existing]
instance WithTop.instRepr [Repr α] : Repr (WithTop α) :=
  ⟨fun o _ =>
    match o with
    | none => "⊤"
    | some a => "↑" ++ repr a⟩

namespace WithBot

/-- The canonical map from `α` into `WithBot α` -/
@[to_dual (attr := coe, match_pattern) /-- The canonical map from `α` into `WithTop α` -/]
def some : α → WithBot α :=
  Option.some

@[to_dual]
instance coe : Coe α (WithBot α) :=
  ⟨some⟩

@[to_dual]
instance bot : Bot (WithBot α) :=
  ⟨none⟩

@[to_dual]
instance inhabited : Inhabited (WithBot α) :=
  ⟨⊥⟩

/-- Recursor for `WithBot` using the preferred forms `⊥` and `↑a`. -/
@[to_dual (attr := elab_as_elim, induction_eliminator, cases_eliminator)
/-- Recursor for `WithTop` using the preferred forms `⊤` and `↑a`. -/]
def recBotCoe {motive : WithBot α → Sort*} (bot : motive ⊥) (coe : ∀ a : α, motive a) :
    ∀ x, motive x
  | ⊥ => bot
  | (a : α) => coe a

@[to_dual (attr := simp)]
theorem recBotCoe_bot {motive : WithBot α → Sort*} (bot : motive ⊥) (coe : ∀ a : α, motive a) :
    @recBotCoe _ motive bot coe ⊥ = bot :=
  rfl

@[to_dual (attr := simp)]
theorem recBotCoe_coe {motive : WithBot α → Sort*} (bot : motive ⊥) (coe : ∀ a : α, motive a)
    (x : α) : @recBotCoe _ motive bot coe ↑x = coe x :=
  rfl

end WithBot

/-- Attach both `⊥` and `⊤` to a type. This is intended as a common, canonical spelling for
`WithBot (WithTop α)` and `WithTop (WithBot α)` -/
abbrev WithBotTop (α : Type*) := WithBot (WithTop α)

namespace WithBotTop

instance instRepr [Repr α] : Repr (WithBotTop α) :=
  ⟨fun o _ =>
    match o with
    | none => "⊥"
    | some a => repr a⟩

/-- The canonical map from `α` into `WithBotTop α` -/
@[coe, match_pattern]
abbrev some : α → WithBotTop α :=
  WithBot.some ∘ WithTop.some

instance coe : Coe α (WithBotTop α) :=
  ⟨some⟩

instance bot : Bot (WithBotTop α) :=
  ⟨none⟩

@[to_dual existing]
instance top : Top (WithBotTop α) :=
  ⟨WithBot.some none⟩

instance inhabited : Inhabited (WithBotTop α) :=
  ⟨⊥⟩

/-- Recursor for `WithBotTop` using the preferred forms `⊥`, `⊤`, and `↑a`. -/
@[to_dual self (reorder := bot top), elab_as_elim, induction_eliminator, cases_eliminator]
def recBotTopCoe {motive : WithBotTop α → Sort*}
    (bot : motive ⊥) (top : motive ⊤) (coe : ∀ a : α, motive a) : ∀ x, motive x
  | ⊥ => bot
  | ⊤ => top
  | (a : α) => coe a

@[to_dual (attr := simp)]
theorem recBotCoe_bot {motive : WithBotTop α → Sort*} (bot : motive ⊥) (top : motive ⊤)
    (coe : ∀ a : α, motive a) : @recBotTopCoe _ motive bot top coe ⊥ = bot :=
  rfl

@[to_dual self, simp]
theorem recBotCoe_coe {motive : WithBotTop α → Sort*} (bot : motive ⊥) (top : motive ⊤)
    (coe : ∀ a : α, motive a) (x : α) : @recBotTopCoe _ motive bot top coe x = coe x :=
  rfl

end WithBotTop

/-- The type of extended integers `[-∞, ∞]`, constructed as `WithBotTop ℤ`. -/
abbrev EInt := WithBotTop Int
