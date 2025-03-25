/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

namespace Section7sheet3

/-

# Quotient groups

mathlib has quotient groups. Here's how they work.

-/
-- let G be a group and let N be a normal subgroup
variable (G : Type) [Group G] (N : Subgroup G) [Subgroup.Normal N]

-- The underlying type (or set) of the quotient group. Note that `⧸` is `\quot`, not the slash
-- character `/` on your keyboard (which means division in Lean, not quotient).
example : Type :=
  G ⧸ N

-- Let's check that the typeclass inference system can find the group structure on the quotient
example : Group (G ⧸ N) := by
  infer_instance
  done


-- The group homomorphism from `G` to `G ⧸ N`
example : G →* G ⧸ N :=
  QuotientGroup.mk' N

/- Remarks:

(1) Why `QuotientGroup.mk'` and not the unprimed `QuotientGroup.mk`? Because the version without
the `'` is just the bare function, the version with the `'` is the group homomorphism.

(2) Why does `QuotientGroup.mk' N` want to have `N` as an input but not `G`? It's because
the type of `N` is `Subgroup G` so Lean can figure out `G` from `N`: if you like, `N` "knows
which group it's a subgroup of".

(3) I am going to do `open QuotientGroup` very shortly, so then you'll just
be able to write `mk'` instead of `QuotientGroup.mk'`.

Here is the basic API you need for quotient groups.
-/

-- the map G → G ⧸ N is surjective
example : Function.Surjective (QuotientGroup.mk' N) :=
  QuotientGroup.mk'_surjective N

-- let's do that again with QuotientGroup opened

open QuotientGroup


-- the map G → G ⧸ N is surjective
example : Function.Surjective (mk' N) :=
  mk'_surjective N

-- Two elements of G have the same image in `G ⧸ N` iff they differ by an element of `N`
example (x y : G) : mk' N x = mk' N y ↔ ∃ n ∈ N, x * n = y :=
  mk'_eq_mk' N -- this is QuotientGroup.mk'_eq_mk'

/-
There is of course much more API, but if you want to get some practice you can
just develop some of it yourself from these two functions.
-/
example : (mk' N).ker = N := by
  ext g
  rw [MonoidHom.mem_ker, ← MonoidHom.map_one (mk' N), eq_comm, mk'_eq_mk']
  simp

/-
# Universal properties

The "universal property" of quotients says that if you have a group homomorphism `φ : G →* H`
whose kernel contains `N` then it "extends" to a group homomorphism `ψ : G ⧸ N →* H`
such that the composite map `ψ ∘ (QuotientGroup.mk' N)` equals `φ`. Given `φ`, the `ψ` with
this property is called `QuotientGroup.lift N φ h`, where `h` is a proof of `∀ x, x ∈ N → φ x = 1`.
-/
variable (H : Type) [Group H] (φ : G →* H) (h : ∀ x, x ∈ N → φ x = 1)

example : G ⧸ N →* H :=
  lift N φ h -- the full name of this function is QuotientGroup.lift

/-
The proof that if `x : G` then `(quotient_group.lift N φ h) ((quotient_group.mk' N) x) = φ x`
is, amazingly, `rfl`.
-/
example (x : G) : (lift N φ h) ((mk' N) x) = φ x := by rfl

/-
Technical remark: this would not be the case if quotient groups were *defined* to
be cosets. In Lean quotient groups are an *opaque definition*. What do I mean by this?
You probably learnt in algebra that if G is a group and H is a normal subgroup then the
quotient G⧸H has elements which are *equal* to cosets of H. In Lean this is not true.
A term of the quotient type G⧸H cannot be taken apart with `cases` because it is not *equal* to
a coset. But the universal property `QuotientGroup.lift` is all we need; we don't
need to worry about the underlying definition of the quotient.
Example. Let's use `QuotientGroup.lift` to define the following map. Say `φ : G →* H` is a
group hom and we have normal subgroups `N : Subgroup G` and `P : Subgroup H` such that `φ N ≤ P`.
Then the induced map `G →* H ⧸ P` has `N` in the kernel, so it "lifts" to a group hom
`ρ : G ⧸ N →* H ⧸ P` with the property that for all `x : G`,
`ρ (QuotientGroup.mk' N x) = QuotientGroup.mk' P (φ x)`. Let's define `ρ` and prove
this equality.
-/
variable {G H φ N}
variable {P : Subgroup H} [P.Normal]

def ρ (h : N.map φ ≤ P) : G ⧸ N →* H ⧸ P :=
  lift N ((mk' P).comp φ) (by
    -- we are using `lift` so we need to supply the proof that `(mk' P).comp φ` kills `N`
    intro g hgn
    rw [MonoidHom.mem_ker,  MonoidHom.coe_comp, coe_mk', Function.comp_apply, eq_one_iff]
    apply h
    use g, hgn
  )

-- Now let's prove that `ρ ∘ mk' N = mk' P ∘ φ`
/-
    G ----φ----> H
    |            |
    |            |
   mk'           mk'
    |            |
    \/           \/
  G ⧸ N --ρ--> H ⧸ P
-/

example (h : N.map φ ≤ P) (x : G) : ρ h (mk' N x) = mk' P (φ x) := by
  rfl

end Section7sheet3
