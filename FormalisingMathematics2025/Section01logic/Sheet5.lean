/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  constructor <;> intro p <;> exact p

example : (P ↔ Q) → (Q ↔ P) := by
  intro h
  rw [h]

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor <;> intro h <;> rw [h]

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro h1 h2
  rwa [← h2]

example : P ∧ Q ↔ Q ∧ P := by
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h2, h1⟩

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  · rintro ⟨⟨p, q⟩, r⟩
    exact ⟨p, q, r⟩
  rintro ⟨p, q, r⟩
  exact ⟨⟨p, q⟩, r⟩

example : P ↔ P ∧ True := by
  constructor
  · intro p
    exact ⟨p, by trivial⟩
  rintro ⟨p⟩
  exact p

example : False ↔ P ∧ False := by
  constructor
  · intro f
    exfalso
    exact f
  rintro ⟨-, f⟩
  exact f

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  rintro ⟨pq, qp⟩ ⟨rs, sr⟩
  constructor
  · rintro ⟨p, r⟩
    exact ⟨pq p, rs r⟩
  rintro ⟨q, s⟩
  exact ⟨qp q, sr s⟩

example : ¬(P ↔ ¬P) := by
  change (P ↔ ¬ P) → False
  rintro ⟨pnp, npp⟩
  by_cases p : P
  · exact (pnp p) p
  exact p (npp p)
