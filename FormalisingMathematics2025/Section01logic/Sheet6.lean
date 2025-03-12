/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 6 : "or" (`∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro p
  left
  exact p

example : Q → P ∨ Q := by
  intro q
  right
  exact q

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro porq pr qr
  rcases porq with (p | q)
  · exact pr p
  exact qr q

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro pq
  rcases pq with (p | q)
  · right
    exact p
  left
  exact q

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  · rintro ((p | q) | r)
    · left
      exact p
    · right
      left
      exact q
    right
    right
    exact r
  rintro (p | q | r)
  · left
    left
    exact p
  · left
    right
    exact q
  right
  exact r

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  rintro pr qs (p | q)
  · left
    exact pr p
  right
  exact qs q

example : (P → Q) → P ∨ R → Q ∨ R := by
  rintro pq (p | r)
  · left
    exact pq p
  right
  exact r

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro pr qs
  rw [pr, qs]

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  · intro npq
    constructor
    · intro p
      apply npq
      left
      exact p
    intro q
    apply npq
    right
    exact q
  rintro npnq  (p | q)
  · exact npnq.1 p
  · exact npnq.2 q

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  · intro npq
    by_cases hp: P
    · right
      intro q
      apply npq
      exact ⟨hp, q⟩
    · left
      exact hp
  rintro (np | nq) ⟨p, q⟩
  · contradiction
  contradiction
