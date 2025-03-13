/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/

import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 6 : pushforward and pullback

## Pushforward of a set along a map

If `f : X → Y` then given a subset `S : Set X` of `X` we can push it
forward along `f` to make a subset `f(S) : Set Y` of `Y`. The definition
of `f(S)` is `{y : Y | ∃ x : X, x ∈ S ∧ f x = y}`.

However `f(S)` doesn't make sense in Lean, because `f` eats
terms of type `X` and not `S`, which has type `Set X`.
In Lean we use the notation `f '' S` for this. This is notation
for `Set.image` and if you need any API for this, it's likely
to use the word `image`.

## Pullback of a set along a map

If `f : X → Y` then given a subset `T : Set Y` of `Y` we can
pull it back along `f` to make a subset `f⁻¹(T) : Set X` of `X`. The
definition of `f⁻¹(T)` is `{x : X | f x ∈ T}`.

However `f⁻¹(T)` doesn't make sense in Lean either, because
`⁻¹` is notation for `Inv.inv`, whose type in Lean
is `α → α`. In other words, if `x` has a certain type, then
`x⁻¹` *must* have the same type: the notation was basically designed
for group theory. In Lean we use the notation `f ⁻¹' T` for this pullback.

-/

variable (X Y : Type) (f : X → Y) (S : Set X) (T : Set Y)

example : S ⊆ f ⁻¹' (f '' S) := by
  intro x xs
  use x

example : f '' (f ⁻¹' T) ⊆ T := by
  intro x hx
  rw [Set.mem_image] at hx
  have ⟨y, hy, hfyx⟩ := hx
  rw [Set.mem_preimage, hfyx] at hy
  exact hy

-- `library_search` will do this but see if you can do it yourself.
example : f '' S ⊆ T ↔ S ⊆ f ⁻¹' T := by
  constructor
  · intro fst x xs
    apply fst
    use x
  · intro sfpt y yfs
    have ⟨x, hs, fxy⟩ := yfs
    have := sfpt hs
    rw [Set.mem_preimage, fxy] at this
    exact this

-- Pushforward and pullback along the identity map don't change anything
-- pullback is not so hard
example : id ⁻¹' S = S := by
  ext x
  constructor <;> intro h <;> exact h

-- pushforward is a little trickier. You might have to `ext x, split`.
example : id '' S = S := by
  ext x
  constructor
  · rintro ⟨x', x's, rfl⟩
    exact x's
  · intro xs
    use x, xs
    rfl

-- Now let's try composition.
variable (Z : Type) (g : Y → Z) (U : Set Z)

-- preimage of preimage is preimage of comp
example : g ∘ f ⁻¹' U = f ⁻¹' (g ⁻¹' U) := by
  ext x
  constructor <;> intro hx <;> exact hx

-- preimage of preimage is preimage of comp
example : g ∘ f '' S = g '' (f '' S) := by
  ext z
  constructor
  · intro ⟨x, xs, hx⟩
    use f x
    constructor
    · use x
    · exact hx
  · rintro ⟨y, ⟨x, xs, rfl⟩, rfl⟩
    use x, xs
    rfl
