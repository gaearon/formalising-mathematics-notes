/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 3 : not in (`∉`) and complement `Aᶜ`

The definition in Lean of `x ∉ A` is `¬ (x ∈ A)`. In other words,
`x ∉ A`, `¬ (x ∈ A)` and `(x ∈ A) → False` are all equal *by definition*
in Lean.

The complement of a subset `A` of `X` is the subset `Aᶜ`; it's the terms of
type `X` which aren't in `A`. The *definition* of `x ∈ Aᶜ` is `x ∉ A`.

For example, if you have a hypothesis `h : x ∈ Aᶜ` and your goal
is `False`, then `apply h` will work and will change the goal to `x ∈ A`.
Think a bit about why, it's a good logic exercise.

-/


open Set

variable (X : Type) -- Everything will be a subset of `X`
  (A B C D E : Set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

-- x,y,z are elements of `X` or, more precisely, terms of type `X`
example : x ∉ A → x ∈ A → False := by
  intro xna xa
  exact xna xa

example : x ∈ A → x ∉ A → False := by
  intro xa xna
  exact xna xa

example : A ⊆ B → x ∉ B → x ∉ A := by
  intro ab xnb xa
  apply xnb
  exact ab xa

-- Lean couldn't work out what I meant when I wrote `x ∈ ∅` so I had
-- to give it a hint by telling it the type of `∅`.
example : x ∉ (∅ : Set X) := by
  intro xo
  exact xo

example : x ∈ Aᶜ → x ∉ A := by
  intro xac
  exact xac

example : (∀ x, x ∈ A) ↔ ¬∃ x, x ∈ Aᶜ := by
  constructor
  · intro hx ⟨x, hx2⟩
    exact hx2 (hx x)
  · intro hx x
    by_contra hna
    apply hx
    use x, hna

example : (∃ x, x ∈ A) ↔ ¬∀ x, x ∈ Aᶜ := by
  constructor
  · rintro ⟨x, hx⟩ xna
    exact xna x hx
  · rintro nxna
    push_neg at nxna
    have ⟨x, hx⟩ := nxna
    use x
    by_contra
    contradiction
