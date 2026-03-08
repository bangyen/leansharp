/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
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

variable {d : ℕ}

/-- Auxiliary: the derivative of `t ↦ L(p + t•ε)` is `inner ℝ (∇L) ε`. -/
private lemma path_hasDerivAt (L : W d → ℝ) (p ε : W d) (t : ℝ)
    (h_diff : Differentiable ℝ L) :
    HasDerivAt (fun (t : ℝ) => L (p + t • ε)) (inner ℝ (gradient L (p + t • ε)) ε) t := by
  have hf : HasDerivAt (fun (s : ℝ) => p + s • ε) ε t := by
    simpa using (hasDerivAt_id t).smul_const ε |>.const_add p
  have hcomp := (h_diff (p + t • ε)).hasFDerivAt.comp_hasDerivAt t hf
  simpa [gradient, InnerProductSpace.toDual_symm_apply] using hcomp

/-- Auxiliary: the function `t ↦ L(w + tε) - t⟨∇L(w), ε⟩ - t²/2 * M‖ε‖²` is continuous. -/
private lemma smooth_descent_aux_continuous (L : W d → ℝ) (w ε : W d)
    (c m : ℝ) (h_diff : Differentiable ℝ L) :
    Continuous (fun t => L (w + t • ε) - t * c - t ^ 2 * m) :=
  (h_diff.continuous.comp (continuous_const.add (continuous_id.smul continuous_const))).sub
    (continuous_id.mul continuous_const) |>.sub ((continuous_id.pow 2).mul continuous_const)

/-- Auxiliary: the derivative of the smooth descent auxiliary function. -/
private lemma smooth_descent_aux_hasDerivAt (L : W d → ℝ) (w ε : W d)
    (c m t : ℝ) (h_diff : Differentiable ℝ L) :
    HasDerivAt (fun t => L (w + t • ε) - t * c - t ^ 2 * m)
      (inner ℝ (gradient L (w + t • ε)) ε - c - 2 * t * m) t := by
  have h1 := path_hasDerivAt L w ε t h_diff
  have h2 := (hasDerivAt_id t).mul_const c
  have h3 := (hasDerivAt_id t).pow 2 |>.mul_const m
  simpa using h1.sub h2 |>.sub h3

/-- **MVT Comparison Step**: Auxiliary lemma for the smooth descent bound. Concludes
$\phi(1) \le \phi(0)$ given that the derivative of $\phi$ is non-positive. -/
private lemma smooth_descent_mvt_step {φ : ℝ → ℝ} {f' : ℝ → ℝ} (hφ_cont : ContinuousOn φ (Icc 0 1))
    (hφ' : ∀ t ∈ Ico 0 1, HasDerivWithinAt φ (f' t) (Ici t) t)
    (hf'_nonpos : ∀ t ∈ Ico 0 1, f' t ≤ 0) :
    φ 1 ≤ φ 0 := by
  let B := fun (_ : ℝ) => φ 0
  let B' := fun (_ : ℝ) => (0 : ℝ)
  have ha : φ 0 ≤ B 0 := le_refl _
  have hB : ContinuousOn B (Icc 0 1) := continuousOn_const
  have hB' : ∀ (x : ℝ), x ∈ Ico 0 1 → HasDerivWithinAt B (B' x) (Ici x) x :=
    fun x _ => hasDerivAt_const x (φ 0) |>.hasDerivWithinAt
  exact image_le_of_deriv_right_le_deriv_boundary hφ_cont hφ' ha hB hB' hf'_nonpos
      (right_mem_Icc.mpr zero_le_one)

/-- **The L-Smooth Descent Lemma**: `L(w + ε) ≤ L(w) + ⟪∇L(w), ε⟫ + M/2 · ‖ε‖²`. -/
theorem smooth_descent (L : W d → ℝ) (w ε : W d) (M : ℝ≥0)
    (h_diff : Differentiable ℝ L)
    (h_smooth : LipschitzWith M (gradient L)) :
    L (w + ε) ≤ L w + inner ℝ (gradient L w) ε + (M : ℝ) / 2 * ‖ε‖ ^ 2 := by
  -- Step 1: Define the auxiliary path function φ(t) = L(w + tε) - t⟨∇L(w), ε⟩ - t²/2 * M‖ε‖²
  let c := inner ℝ (gradient L w) ε
  let m := (M : ℝ) / 2 * ‖ε‖ ^ 2
  let φ : ℝ → ℝ := fun t => L (w + t • ε) - t * c - t ^ 2 * m
  -- Step 2: Show that the derivative of φ is non-positive on [0, 1]
  have hφ' : ∀ t : ℝ, HasDerivAt φ
      (inner ℝ (gradient L (w + t • ε) - gradient L w) ε - 2 * t * m) t := by
    intro t
    have h_deriv := smooth_descent_aux_hasDerivAt L w ε c m t h_diff
    convert h_deriv using 1
    simp [inner_sub_left, c]
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
  -- Step 3: Use the Boundary Derivative Lemma to conclude φ(1) ≤ φ(0)
  have hφ_cont : ContinuousOn φ (Icc 0 1) :=
    (smooth_descent_aux_continuous L w ε c m h_diff).continuousOn
  have hφ_le : φ 1 ≤ φ 0 :=
    smooth_descent_mvt_step hφ_cont (fun t ht => (hφ' t).hasDerivWithinAt)
      (fun x hx => hφ'_nonpos x hx.1 (le_of_lt hx.2))
  -- Step 4: Recover the descent bound from φ(1) ≤ φ(0)
  have hφ0 : φ 0 = L w := by simp [φ]
  simp [φ, hφ0, m, c] at hφ_le
  linarith

/-- **SAM Taylor Terms Bound**: Auxiliary lemma to bound the SAM objective terms. -/
lemma sam_taylor_terms_bound (M : ℝ≥0) (ρ : ℝ) (hρ : 0 ≤ ρ) (g ε : W d) (h_norm : ‖ε‖ ≤ ρ) :
    inner ℝ g ε + (M : ℝ) / 2 * ‖ε‖ ^ 2 ≤ ‖g‖ * ρ + (M : ℝ) / 2 * ρ ^ 2 := by
  have hcs : inner ℝ g ε ≤ ‖g‖ * ρ := by
    calc inner ℝ g ε ≤ ‖g‖ * ‖ε‖ := real_inner_le_norm _ _
      _ ≤ ‖g‖ * ρ := mul_le_mul_of_nonneg_left h_norm (norm_nonneg _)
  have hsq : (M : ℝ) / 2 * ‖ε‖ ^ 2 ≤ (M : ℝ) / 2 * ρ ^ 2 := by
    apply mul_le_mul_of_nonneg_left (sq_le_sq.mpr (by
      simp [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hρ, h_norm]))
    positivity
  linarith

/-- **SAM Taylor Bound**: `sam_objective L w ρ ≤ L w + ‖∇L(w)‖ * ρ + M/2 * ρ²`. -/
theorem sam_taylor_bound (L : W d → ℝ) (w : W d) (ρ : ℝ)
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
    -- Step 1: Apply the smooth descent lemma to the perturbation ε
    have hdescent := smooth_descent L w ε M h_diff h_smooth
    -- Step 2: Use the SAM Taylor Terms Bound helper lemma
    have h_terms := sam_taylor_terms_bound M ρ hρ (gradient L w) ε hε_norm
    linarith [hdescent, h_terms]

/-- **One-Step Descent Radius Check**: Verifies that the learning rate $\eta$
multiplied by the Lipschitz constant $M$ is bounded by 1. -/
lemma one_step_descent_radius_check (M : ℝ≥0) (η : ℝ)
    (h_eta_bound : η ≤ 1 / (M : ℝ)) : (M : ℝ) * η ≤ 1 := by
  if hM : 0 < (M : ℝ) then
    linarith [((le_div_iff₀ hM).mp h_eta_bound : η * M ≤ 1)]
  else
    have : (M : ℝ) = 0 := by linarith [NNReal.coe_nonneg M]
    simp [this]

/-- **One-Step Descent Recurrence**: For an L-smooth function, a gradient descent step
with learning rate $\eta \le 1/L$ ensures a decrease proportional to the gradient norm squared:
$L(w - \eta \nabla L(w)) \le L(w) - \frac{\eta}{2} \|\nabla L(w)\|^2$. -/
theorem smooth_one_step_descent (L : W d → ℝ) (w : W d) (M : ℝ≥0) (η : ℝ)
    (h_diff : Differentiable ℝ L)
    (h_smooth : LipschitzWith M (gradient L))
    (h_eta : 0 < η)
    (h_eta_bound : η ≤ 1 / (M : ℝ)) :
    L (w - η • gradient L w) ≤ L w - (η / 2) * ‖gradient L w‖ ^ 2 := by
  set g := gradient L w
  have h_descent := smooth_descent L w (-(η • g)) M h_diff h_smooth
  have h_step : w - η • g = w + -(η • g) := sub_eq_add_neg w (η • g)
  -- Step 1: Verify the descent radius bound
  have h_bound := one_step_descent_radius_check M η h_eta_bound
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
