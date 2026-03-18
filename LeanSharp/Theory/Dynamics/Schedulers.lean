/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic

/-!
# Learning Rate Schedulers

This module formalizes various learning rate schedules used in optimization,
starting with the popular Cosine Decay schedule.

## Main definitions

* `Schedule`: A type alias for `ℕ → ℝ`, mapping a step index to a learning rate.
* `cosine_decay_schedule`: Implements the cosine annealing decay.

## Theorems

* `cosine_argument_in_range`.
* `cosine_argument_mono`.
* `cosine_decay_zero`.
* `cosine_decay_schedule_of_ge`.
* `cosine_decay_at_T`.
* `cosine_decay_antitone`.
-/

namespace LeanSharp

open Real

/-- A Schedule maps a time step `t` to a learning rate `η`. -/
def Schedule := ℕ → ℝ

/--
**Cosine Decay Schedule**:
$\eta_t = \eta_{min} + \frac{1}{2}(\eta_{max} - \eta_{min})(1 + \cos(\frac{t\pi}{T}))$
for $t < T$, and $\eta_t = \eta_{min}$ for $t \ge T$.
-/
noncomputable def cosine_decay_schedule (η_max η_min : ℝ) (T : ℕ) : Schedule := fun t =>
  if t < T then
    η_min + (1 / 2) * (η_max - η_min) * (1 + cos (t * π / T))
  else
    η_min

/-- Helper: The argument to `cos` stays within `[0, π]`. -/
theorem cosine_argument_in_range {t T : ℕ} (ht : t ≤ T) (hT : T ≠ 0) :
    t * π / T ∈ Set.Icc 0 π := by
  have hT_pos : 0 < (T : ℝ) := by norm_cast; exact Nat.pos_of_ne_zero hT
  constructor
  · positivity
  · have h_le : (t : ℝ) ≤ T := by norm_cast
    have : (t : ℝ) / T ≤ 1 := (div_le_one hT_pos).mpr h_le
    calc (t : ℝ) * π / T = ((t : ℝ) / T) * π := by ring
      _ ≤ 1 * π := mul_le_mul_of_nonneg_right this (le_of_lt pi_pos)
      _ = π := by ring

/-- Helper: The argument to `cos` is monotonic in `t`. -/
theorem cosine_argument_mono {t₁ t₂ T : ℕ} (ht : t₁ ≤ t₂) (hT : T ≠ 0) :
    t₁ * π / T ≤ t₂ * π / T := by
  have hT_pos : 0 < (T : ℝ) := by norm_cast; exact Nat.pos_of_ne_zero hT
  have h_le : (t₁ : ℝ) ≤ t₂ := by norm_cast
  calc (t₁ : ℝ) * π / T = (t₁ : ℝ) * (π / T) := by ring
    _ ≤ (t₂ : ℝ) * (π / T) := mul_le_mul_of_nonneg_right h_le (by positivity)
    _ = t₂ * π / T := by ring

/-- The Cosine Decay schedule starts at `η_max` when `t = 0`. -/
theorem cosine_decay_zero (η_max η_min : ℝ) (T : ℕ) (hT : 0 < T) :
    cosine_decay_schedule η_max η_min T 0 = η_max := by
  unfold cosine_decay_schedule
  rw [if_pos hT]
  norm_cast
  rw [
    one_div,
    zero_mul,
    zero_div,
    cos_zero
  ]
  ring

/-- For any step at or beyond the cutoff horizon, cosine decay returns `η_min`.
This theorem exists as a canonical simplification rule for endpoint and
post-horizon schedule evaluations. -/
@[simp] theorem cosine_decay_schedule_of_ge (η_max η_min : ℝ) (T t : ℕ) (ht : T ≤ t) :
    cosine_decay_schedule η_max η_min T t = η_min := by
  unfold cosine_decay_schedule
  rw [if_neg (Nat.not_lt.mpr ht)]

/-- The Cosine Decay schedule reaches `η_min` at `t = T`. -/
theorem cosine_decay_at_T (η_max η_min : ℝ) (T : ℕ) :
    cosine_decay_schedule η_max η_min T T = η_min := by
  exact cosine_decay_schedule_of_ge η_max η_min T T le_rfl

/-- **Monotonicity of Cosine Decay**: The schedule is non-increasing for `η_min ≤ η_max`. -/
theorem cosine_decay_antitone (η_max η_min : ℝ) (T : ℕ) (h_le : η_min ≤ η_max) :
    Antitone (cosine_decay_schedule η_max η_min T) := by
  intro t₁ t₂ ht
  unfold cosine_decay_schedule
  split_ifs with h₂ h₁
  · -- t₂ < T, t₁ < T
    have h_arg : cos (↑t₂ * π / ↑T) ≤ cos (↑t₁ * π / ↑T) := by
      apply antitoneOn_cos
      · apply cosine_argument_in_range h₁.le (by linarith)
      · apply cosine_argument_in_range h₂.le (by linarith)
      · apply cosine_argument_mono ht (by linarith)
    have h_diff : 0 ≤ η_max - η_min := by linarith
    nlinarith
  · -- t₂ < T, t₁ ≥ T (contradiction because t₁ ≤ t₂)
    linarith
  · -- t₂ ≥ T, t₁ < T
    have h_cos : -1 ≤ cos (t₁ * π / T) := neg_one_le_cos _
    have h_diff : 0 ≤ η_max - η_min := by linarith
    nlinarith
  · -- t₂ ≥ T, t₁ ≥ T
    exact le_refl _

end LeanSharp
