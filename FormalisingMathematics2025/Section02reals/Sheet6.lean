/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics
import FormalisingMathematics2025.Solutions.Section02reals.Sheet5 -- import a bunch of previous stuff

namespace Section2sheet6

open Section2sheet3solutions Section2sheet5solutions

/-

# Harder questions

Here are some harder questions. Don't feel like you have
to do them. We've seen enough techniques to be able to do
all of these, but the truth is that we've seen a ton of stuff
in this course already, so probably you're not on top of all of
it yet, and furthermore we have not seen
some techniques which will enable you to cut corners. If you
want to become a real Lean expert then see how many of these
you can do. I will go through them all in class,
so if you like you can try some of them and then watch me
solving them.

Good luck!
-/
/-- If `a(n)` tends to `t` then `37 * a(n)` tends to `37 * t`-/
theorem tendsTo_thirtyseven_mul (a : ℕ → ℝ) (t : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ 37 * a n) (37 * t) := by
  intro ε εpos
  dsimp
  specialize h (ε / 37) (by linarith)
  obtain ⟨N, hN⟩ := h
  use N
  intro n hn
  specialize hN n hn
  rw [← mul_sub, abs_mul, abs_of_pos (by norm_num)]
  linarith

/-- If `a(n)` tends to `t` and `c` is a positive constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_pos_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : 0 < c) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  intro ε εpos
  dsimp
  specialize h (ε / c) (div_pos εpos hc)
  obtain ⟨N, hN⟩ := h
  use N
  intro n hn
  specialize hN n hn
  rw [← mul_sub, abs_mul, abs_of_pos hc]
  exact (lt_div_iff₀' hc).mp hN

/-- If `a(n)` tends to `t` and `c` is a negative constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_neg_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : c < 0) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  intro ε εpos
  dsimp
  specialize h (-(ε / c)) (neg_pos.mpr (div_neg_of_pos_of_neg εpos hc))
  obtain ⟨N, hN⟩ := h
  use N
  intro n hn
  specialize hN n hn
  rw [← mul_sub, abs_mul, abs_of_neg hc]
  apply (lt_div_iff₀' (neg_pos.mpr (hc))).mp
  linarith

/-- If `a(n)` tends to `t` and `c` is a constant then `c * a(n)` tends
to `c * t`. -/
theorem tendsTo_const_mul {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  rcases lt_trichotomy c 0 with (clez | ceqz | zlec)
  · exact tendsTo_neg_const_mul h clez
  · simpa only [ceqz, zero_mul] using tendsTo_const 0
  · exact tendsTo_pos_const_mul h zlec

/-- If `a(n)` tends to `t` and `c` is a constant then `a(n) * c` tends
to `t * c`. -/
theorem tendsTo_mul_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ a n * c) (t * c) := by
  simpa only [mul_comm] using tendsTo_const_mul c h

-- another proof of this result
theorem tendsTo_neg' {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n ↦ -a n) (-t) := by
  simpa only [neg_one_mul] using tendsTo_const_mul (-1) ha

/-- If `a(n)-b(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)` tends to `t + u`. -/
theorem tendsTo_of_tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (h1 : TendsTo (fun n ↦ a n - b n) t)
    (h2 : TendsTo b u) : TendsTo a (t + u) := by
  simpa only [sub_add_cancel] using tendsTo_add h1 h2

/-- If `a(n)` tends to `t` then `a(n)-t` tends to `0`. -/
theorem tendsTo_sub_lim_iff {a : ℕ → ℝ} {t : ℝ} : TendsTo a t ↔ TendsTo (fun n ↦ a n - t) 0 := by
  constructor
  · intro ha
    simpa only [sub_self] using tendsTo_sub ha (tendsTo_const t)
  · intro ha
    simpa only [sub_add_cancel, zero_add] using tendsTo_add ha (tendsTo_const t)

/-- If `a(n)` and `b(n)` both tend to zero, then their product tends
to zero. -/
theorem tendsTo_zero_mul_tendsTo_zero {a b : ℕ → ℝ} (ha : TendsTo a 0) (hb : TendsTo b 0) :
    TendsTo (fun n ↦ a n * b n) 0 := by
  intro ε εpos
  specialize ha ε εpos
  specialize hb 1 (show 1 > 0 by norm_num)
  obtain ⟨Na, hNa⟩ := ha
  obtain ⟨Nb, hNb⟩ := hb
  use (max Na Nb)
  intro n hn
  specialize hNa n (le_of_max_le_left hn)
  specialize hNb n (le_of_max_le_right hn)
  simpa [abs_mul] using mul_lt_mul'' hNa hNb

/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)*b(n)` tends to `t*u`. -/
theorem tendsTo_mul (a b : ℕ → ℝ) (t u : ℝ) (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n * b n) (t * u) := by
  rw [tendsTo_sub_lim_iff] at *
  have h : ∀ n, a n * b n - t * u = (a n - t) * (b n - u) + t * (b n - u) + u * (a n - t) := by
    intro n
    ring
  simp only [h]
  rw [show (0: ℝ) = 0 + t * 0 + u * 0 by ring]
  refine' tendsTo_add (tendsTo_add ?_ ?_) ?_
  · exact tendsTo_zero_mul_tendsTo_zero ha hb
  · exact tendsTo_const_mul t hb
  · exact tendsTo_const_mul u ha

theorem dist_trans {a b c ε : ℝ} (hab : |a - b| < ε) (hbc : |a - c| < ε) :
  (|b - c| < 2 * ε) := by
  rw [abs_sub_lt_iff] at *
  constructor
  · linarith
  · linarith

-- something we never used!
/-- A sequence has at most one limit. -/
theorem tendsTo_unique (a : ℕ → ℝ) (s t : ℝ) (hs : TendsTo a s) (ht : TendsTo a t) : s = t := by
  by_cases h : s = t
  · exact h
  set ε := |s - t| / 2
  have εpos : |s - t| / 2 > 0 := by
    rw [(show (0 : ℝ) = 0 / 2 by norm_num)]
    gcongr
    apply abs_pos.mpr
    apply sub_ne_zero_of_ne h
  specialize hs ε εpos
  specialize ht ε εpos
  have ⟨Ns, hNs⟩ := hs
  have ⟨Nt, hNt⟩ := ht
  set n := max Ns Nt
  specialize hNs n (le_max_left _ _)
  specialize hNt n (le_max_right _ _)
  have h := dist_trans hNs hNt
  dsimp [ε] at h
  linarith

end Section2sheet6
