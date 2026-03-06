/-
Copyright (c) 2024 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Sam
import LeanSharp.Core.Landscape
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Linarith

/-!
# Taylor Descent Lemma for SAM

This module proves a second-order Taylor bound for L-smooth loss functions,
which is critical for the convergence analysis of SAM variants.

## Main theorems

* `smooth_descent`: The standard quadratic upper bound for L-smooth functions.
* `sam_taylor_bound`: Specifically adapts the descent lemma to the SAM objective.
-/

namespace LeanSharp

open Set InnerProductSpace Real NNReal

/-- Auxiliary: the derivative of `t ↦ L(p + t•ε)` is `inner ℝ (∇L) ε`. -/
private lemma path_hasDerivAt {d : ℕ} [Fact (0 < d)] (L : W d → ℝ) (p ε : W d) (t : ℝ)
    (h_diff : Differentiable ℝ L) :
    HasDerivAt (fun (t : ℝ) => L (p + t • ε)) (inner ℝ (gradient L (p + t • ε)) ε) t := by
  have hf : HasDerivAt (fun (s : ℝ) => p + s • ε) ε t := by
    simpa using (hasDerivAt_id t).smul_const ε |>.const_add p
  have hcomp := (h_diff (p + t • ε)).hasFDerivAt.comp_hasDerivAt t hf
  simpa [gradient, InnerProductSpace.toDual_symm_apply] using hcomp

/-- **The L-Smooth Descent Lemma**: `L(w + ε) ≤ L(w) + ⟪∇L(w), ε⟫ + M/2 · ‖ε‖²`. -/
theorem smooth_descent {d : ℕ} [Fact (0 < d)] (L : W d → ℝ) (w ε : W d) (M : ℝ≥0)
    (h_diff : Differentiable ℝ L)
    (h_smooth : LipschitzWith M (gradient L)) :
    L (w + ε) ≤ L w + inner ℝ (gradient L w) ε + (M : ℝ) / 2 * ‖ε‖ ^ 2 := by
  let c := inner ℝ (gradient L w) ε
  let m := (M : ℝ) / 2 * ‖ε‖ ^ 2
  let φ : ℝ → ℝ := fun t => L (w + t • ε) - t * c - t ^ 2 * m
  have hφ' : ∀ t : ℝ, HasDerivAt φ
      (inner ℝ (gradient L (w + t • ε) - gradient L w) ε - 2 * t * m) t := by
    intro t
    have h1 := path_hasDerivAt L w ε t h_diff
    have h2 : HasDerivAt (fun (s : ℝ) => s * c) c t := by
      simpa using (hasDerivAt_id t).mul_const c
    have h3 : HasDerivAt (fun (s : ℝ) => s ^ 2 * m) (2 * t * m) t := by
      simpa using (hasDerivAt_id t).pow 2 |>.mul_const m
    convert h1.sub h2 |>.sub h3 using 1
    simp [inner_sub_left]; ring
  have hφ'_nonpos : ∀ (t : ℝ), 0 ≤ t → t ≤ 1 →
      inner ℝ (gradient L (w + t • ε) - gradient L w) ε - 2 * t * m ≤ 0 := by
    intro t h0t ht1
    have hcs : inner ℝ (gradient L (w + t • ε) - gradient L w) ε ≤
        ‖gradient L (w + t • ε) - gradient L w‖ * ‖ε‖ :=
      real_inner_le_norm _ _
    have hlip : ‖gradient L (w + t • ε) - gradient L w‖ ≤ (M : ℝ) * t * ‖ε‖ := by
      have := h_smooth.dist_le_mul (w + t • ε) w
      simpa [dist_eq_norm, norm_smul, abs_of_nonneg h0t, mul_assoc] using this
    have h_bound : inner ℝ (gradient L (w + t • ε) - gradient L w) ε ≤
        (M : ℝ) * t * ‖ε‖ ^ 2 := by
      calc inner ℝ (gradient L (w + t • ε) - gradient L w) ε
          ≤ ‖gradient L (w + t • ε) - gradient L w‖ * ‖ε‖ := hcs
        _ ≤ ((M : ℝ) * t * ‖ε‖) * ‖ε‖ := mul_le_mul_of_nonneg_right hlip (norm_nonneg ε)
        _ = (M : ℝ) * t * ‖ε‖ ^ 2 := by ring
    have h_2tm : 2 * t * m = (M : ℝ) * t * ‖ε‖ ^ 2 := by simp [m]; ring
    linarith [h_bound, h_2tm]
  have hφ_cont : ContinuousOn φ (Icc 0 1) := by
    have hLp : Continuous (fun (t : ℝ) => L (w + t • ε)) := by
      apply h_diff.continuous.comp
      exact continuous_const.add (continuous_id.smul continuous_const)
    have h2 : Continuous (fun (t : ℝ) => t * c) := continuous_id.mul continuous_const
    have h3 : Continuous (fun (t : ℝ) => t ^ 2 * m) := (continuous_id.pow 2).mul continuous_const
    refine hLp.continuousOn.sub h2.continuousOn |>.sub h3.continuousOn
  have hφ_le : φ 1 ≤ φ 0 := by
    let B := fun (_ : ℝ) => φ 0
    let B' := fun (_ : ℝ) => (0 : ℝ)
    have ha : φ 0 ≤ B 0 := le_refl _
    have hB : ContinuousOn B (Icc 0 1) := continuousOn_const
    have hB' : ∀ (x : ℝ), x ∈ Ico 0 1 → HasDerivWithinAt B (B' x) (Ici x) x :=
      fun x _ => hasDerivAt_const x (φ 0) |>.hasDerivWithinAt
    have h_deriv_le : ∀ (x : ℝ), x ∈ Ico 0 1 →
        (inner ℝ (gradient L (w + x • ε) - gradient L w) ε - 2 * x * m) ≤ B' x :=
      fun x hx => hφ'_nonpos x hx.1 (le_of_lt hx.2)
    exact image_le_of_deriv_right_le_deriv_boundary hφ_cont
      (fun t ht => (hφ' t).hasDerivWithinAt) ha hB hB' h_deriv_le (right_mem_Icc.mpr zero_le_one)
  have hφ0 : φ 0 = L w := by simp [φ]
  simp [φ, hφ0, m, c] at hφ_le
  linarith

/-- **SAM Taylor Bound**: `sam_objective L w ρ ≤ L w + ‖∇L(w)‖ * ρ + M/2 * ρ²`. -/
theorem sam_taylor_bound {d : ℕ} [Fact (0 < d)] (L : W d → ℝ) (w : W d) (ρ : ℝ)
    (M : ℝ≥0)
    (h_smooth : LipschitzWith M (gradient L))
    (h_diff : Differentiable ℝ L)
    (hρ : 0 ≤ ρ) :
    sam_objective L w ρ ≤ L w + ‖gradient L w‖ * ρ + (M : ℝ) / 2 * ρ ^ 2 := by
  unfold sam_objective perturbation_neighborhood
  apply csSup_le
  · exact ⟨L w, w, ⟨0, by simpa [Metric.mem_closedBall] using hρ, by simp⟩, rfl⟩
  · rintro v ⟨_, ⟨ε, hε_norm, rfl⟩, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hε_norm
    have hdescent := smooth_descent L w ε M h_diff h_smooth
    have hcs : inner ℝ (gradient L w) ε ≤ ‖gradient L w‖ * ρ := by
      calc inner ℝ (gradient L w) ε
          ≤ ‖gradient L w‖ * ‖ε‖ := real_inner_le_norm _ _
        _ ≤ ‖gradient L w‖ * ρ := by apply mul_le_mul_of_nonneg_left hε_norm (norm_nonneg _)
    have hsq : (M : ℝ) / 2 * ‖ε‖ ^ 2 ≤ (M : ℝ) / 2 * ρ ^ 2 := by
      have : ‖ε‖ ^ 2 ≤ ρ ^ 2 := by
        apply sq_le_sq.mpr
        rw [abs_of_nonneg (norm_nonneg ε), abs_of_nonneg hρ]
        exact hε_norm
      apply mul_le_mul_of_nonneg_left this
      positivity
    linarith [hdescent, hcs, hsq]

/-- **One-Step Descent Recurrence**: For an L-smooth function, a gradient descent step
with learning rate $\eta \le 1/L$ ensures a decrease proportional to the gradient norm squared:
$L(w - \eta \nabla L(w)) \le L(w) - \frac{\eta}{2} \|\nabla L(w)\|^2$. -/
theorem smooth_one_step_descent {d : ℕ} [Fact (0 < d)] (L : W d → ℝ) (w : W d) (M : ℝ≥0) (η : ℝ)
    (h_diff : Differentiable ℝ L)
    (h_smooth : LipschitzWith M (gradient L))
    (h_eta : 0 < η)
    (h_eta_bound : η ≤ 1 / (M : ℝ)) :
    L (w - η • gradient L w) ≤ L w - (η / 2) * ‖gradient L w‖ ^ 2 := by
  set g := gradient L w
  have h_descent := smooth_descent L w (-(η • g)) M h_diff h_smooth
  have h_step : w - η • g = w + -(η • g) := sub_eq_add_neg w (η • g)
  have h_bound : (M : ℝ) * η ≤ 1 := by
    if hM : (M : ℝ) = 0 then
      rw [hM] at h_eta_bound; simp [div_zero] at h_eta_bound; linarith
    else
      have hM_pos : 0 < (M : ℝ) := (NNReal.coe_nonneg M).lt_of_ne (Ne.symm hM)
      calc (M : ℝ) * η
        _ ≤ (M : ℝ) * (1 / (M : ℝ)) := mul_le_mul_of_nonneg_left h_eta_bound hM_pos.le
        _ = 1 := mul_one_div_cancel hM_pos.ne.symm
  have h_inner_desc : inner ℝ g (-(η • g)) = -η * ‖g‖ ^ 2 := by
    simp [inner_neg_right, inner_smul_right]
  have h_norm_desc : ‖-(η • g)‖ ^ 2 = η ^ 2 * ‖g‖ ^ 2 := by
    simp [norm_neg, norm_smul, mul_pow]
  calc L (w - η • g)
    _ = L (w + -(η • g)) := by rw [h_step]
    _ ≤ L w + inner ℝ g (-(η • g)) + (M : ℝ) / 2 * ‖-(η • g)‖ ^ 2 := h_descent
    _ ≤ L w - (η / 2) * ‖g‖ ^ 2 := by
      nlinarith [h_bound, h_inner_desc, h_norm_desc]

end LeanSharp
