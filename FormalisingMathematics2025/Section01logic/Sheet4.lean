/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases`
* `constructor`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : P ∧ Q → P := by
  intro h
  cases h with
  | intro left right => exact left
  done

example : P ∧ Q → Q := by
  intro pq
  cases' pq with p q
  exact q

example : (P → Q → R) → P ∧ Q → R := by
  intro pqr pq
  cases' pq with p q
  exact pqr p q

example : P → Q → P ∧ Q := by
  intro p q
  constructor
  · exact p
  exact q

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := by
  intro pq
  cases' pq with p q
  constructor
  · exact q
  exact p

example : P → P ∧ True := by
  intro p
  constructor
  · exact p
  trivial

example : False → P ∧ False := by
  intro h
  exfalso
  exact h

/-- `∧` is transitive -/
example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro pq qr
  constructor
  · exact pq.1
  exact qr.2

example : (P ∧ Q → R) → P → Q → R := by
  intro pqr p q
  apply pqr
  constructor <;> assumption
