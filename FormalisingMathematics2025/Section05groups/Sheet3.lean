/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-

# Subgroups and group homomorphisms

Like subsets of a type, a subgroup of a group isn't a type
and so it isn't a group! You can *make* a subgroup into a group,
but a group is a type and a subgroup is a term.

-/

section Subgroups

-- let `G` be a group
variable (G : Type) [Group G]

-- The type of subgroups of `G` is `Subgroup G`

-- Let `H` be a subgroup of `G`
variable (H : Subgroup G)

-- Just like subsets, elements of the subgroup `H` are terms `g` of type `G`
-- satisfying `g ∈ H`.

example (a b : G) (ha : a ∈ H) (hb : b ∈ H) : a * b ∈ H := by
  exact H.mul_mem ha hb -- I found this with `exact?` and then used dot notation.

-- You could instead do `apply H.mul_mem` and go on from there.

-- Try this one:

example (a b c : G) (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H) :
    a * b⁻¹ * 1 * (a * c) ∈ H := by
  apply H.mul_mem
  · apply H.mul_mem
    · exact H.mul_mem ha (H.inv_mem hb)
    · exact H.one_mem
  · apply H.mul_mem ha hc

/-

## Lattice notation for sub-things

Given two subgroups of a group, we can look at their intersection
(which is a subgroup) and their union (which in general isn't).
This means that set-theoretic notations such as `∪` and `∩` are not
always the right concepts in group theory. Instead, Lean uses
"lattice notation". The intersection of two subgroups `H` and `K` of `G`
is `H ⊓ K`, and the subgroup they generate is `H ⊔ K`. To say
that `H` is a subset of `K` we use `H ≤ K`. The smallest subgroup
of `G`, i.e., {e}, is `⊥`, and the biggest subgroup (i.e. G, but
G is a group not a subgroup so it's not G) is `⊤`.

-/

-- intersection of two subgroups, as a subgroup
example (H K : Subgroup G) : Subgroup G := H ⊓ K
-- note that H ∩ K *doesn't work* because `H` and `K` don't
-- have type `Set G`, they have type `Subgroup G`. Lean
-- is very pedantic!

example (H K : Subgroup G) (a : G) : a ∈ H ⊓ K ↔ a ∈ H ∧ a ∈ K := by
  -- true by definition!
  rfl

-- Note that `a ∈ H ⊔ K ↔ a ∈ H ∨ a ∈ K` is not true; only `←` is true.
-- Take apart the `Or` and use `exact?` to find the relevant lemmas.
example (H K : Subgroup G) (a : G) : a ∈ H ∨ a ∈ K → a ∈ H ⊔ K := by
  rintro (ah | ak)
  · exact Subgroup.mem_sup_left ah
  · exact Subgroup.mem_sup_right ak

end Subgroups

/-

## Group homomorphisms

The notation is `→*`, i.e. "function which preserves `*`."

-/

section Homomorphisms

-- Let `G` and `H` be groups
variable (G H : Type) [Group G] [Group H]

-- Let `φ` be a group homomorphism
variable (φ : G →* H)

-- `φ` preserves multiplication

example (a b : G) : φ (a * b) = φ a * φ b := by
  exact φ.map_mul a b -- see what happens if you remove both `by / exact` from this

example (a b : G) : φ (a * b⁻¹ * 1) = φ a * (φ b)⁻¹ * 1 := by
  -- if `φ.map_mul` means that `φ` preserves multiplication
  -- (and you can rewrite with this) then what do you think
  -- the lemmas that `φ` preserves inverse and one are called?
  rw [φ.map_mul, φ.map_mul, φ.map_inv, φ.map_one]

-- Group homomorphisms are extensional: if two group homomorphisms
-- are equal on all inputs then they're the same.

example (φ ψ : G →* H) (h : ∀ g : G, φ g = ψ g) : φ = ψ := by
  -- Use the `ext` tactic.
  ext g
  exact h g

end Homomorphisms
