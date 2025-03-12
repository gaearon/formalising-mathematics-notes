/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → False`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part 1 of the course notes:
https://b-mehta.github.io/formalising-mathematics-notes/

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by
  intro h
  apply h
  trivial

example : False → ¬True := by
  intro h
  intro h'
  exact h

example : ¬False → True := by
  intro h
  trivial

example : True → ¬False := by
  intro h
  change False → False
  intro h'
  exact h'

example : False → ¬P := by
  intro h
  exfalso
  exact h

example : P → ¬P → False := by
  intro h h'
  exact h' h

example : P → ¬¬P := by
  intro h
  change ¬P → False
  intro h'
  exact h' h

example : (P → Q) → ¬Q → ¬P := by
  intro h h'
  change P → False
  change Q → False at h'
  intro p
  apply h'
  exact h p

example : ¬¬False → False := by
  intro h
  by_contra h'
  exact h h'

example : ¬¬P → P := by
  intro h
  by_contra h'
  exact h h'

example : (¬Q → ¬P) → P → Q := by
  intro h p
  change ¬Q → (P → False) at h
  by_cases h' : Q
  · exact h'
  exfalso
  exact h h' p
