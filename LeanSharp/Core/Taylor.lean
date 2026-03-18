/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Landscape
import LeanSharp.Core.Objective
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.NNReal.Basic
import Mathlib.Tactic.Linarith

/-!
# Taylor Descent Lemma for SAM

This module proves a second-order Taylor bound for L-smooth loss functions,
which is critical for the convergence analysis of SAM variants.

## Theorems

* `smooth_descent`: The standard quadratic upper bound for L-smooth functions.
* `sam_taylor_bound`: Specifically adapts the descent lemma to the SAM objective.

## Definitions

* `SmoothObjective`: Bundles a function `L` with its smoothness constant `M` and
  differentiability properties.
-/

namespace LeanSharp

open Set InnerProductSpace Real NNReal

variable {ι : Type*} [Fintype ι]

/-- A structure bundling a function `L` with its smoothness property. -/
structure SmoothObjective (ι : Type*) [Fintype ι] where
  /-- The underlying loss function. -/
  toFun : W ι → ℝ
  /-- The L-smoothness constant. -/
  smoothness : ℝ≥0
  /-- Proof that the loss is differentiable. -/
  differentiable : Differentiable ℝ toFun
  /-- Proof that the gradient is L-Lipschitz. -/
  lipschitz : LipschitzWith smoothness (gradient toFun)

/-- Auxiliary: the derivative of `t ↦ L(p + t•ε)` is `inner ℝ (∇L) ε`. -/
private lemma path_hasDerivAt (L : W ι → ℝ) (p ε : W ι) (t : ℝ)
    (h_diff_at : DifferentiableAt ℝ L (p + t • ε)) :
    HasDerivAt (fun (t : ℝ) => L (p + t • ε))
      (inner ℝ (gradient L (p + t • ε)) ε) t := by
  have hf : HasDerivAt (fun (s : ℝ) => p + s • ε) ε t := by
    simpa only [hasDerivAt_const_add_iff, id_eq, one_smul]
      using (hasDerivAt_id t).smul_const ε |>.const_add p
  have hcomp := h_diff_at.hasFDerivAt.comp_hasDerivAt t hf
  simpa only [gradient, toDual_symm_apply] using hcomp

/-- **MVT Comparison Step**: Auxiliary lemma for the smooth descent bound. Concludes
$\phi(1) \le \phi(0)$ given that the derivative of $\phi$ is non-positive. -/
private lemma smooth_descent_mvt_step {φ : ℝ → ℝ} {f' : ℝ → ℝ}
    (hφ_cont : ContinuousOn φ (Icc 0 1))
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

/-- Auxiliary: the derivative of the φ function is non-positive. -/
private lemma smooth_descent_phi_deriv_nonpos (L : W ι → ℝ) (w ε : W ι) (M : ℝ≥0)
    (h_smooth : LipschitzWith M (gradient L)) (t : ℝ) (h0t : 0 ≤ t) (m : ℝ)
    (h_2tm : 2 * t * m = (M : ℝ) * t * ‖ε‖ ^ 2) :
    inner ℝ (gradient L (w + t • ε) - gradient L w) ε - 2 * t * m ≤ 0 := by
  have hcs : inner ℝ (gradient L (w + t • ε) - gradient L w) ε ≤
      ‖gradient L (w + t • ε) - gradient L w‖ * ‖ε‖ :=
    real_inner_le_norm _ _
  have hlip : ‖gradient L (w + t • ε) - gradient L w‖ ≤ (M : ℝ) * t * ‖ε‖ := by
    have := h_smooth.dist_le_mul (w + t • ε) w
    simpa only [
      mul_assoc,
      ge_iff_le,
      dist_eq_norm,
      add_sub_cancel_left,
      norm_smul,
      norm_eq_abs,
      abs_of_nonneg h0t
    ] using this
  have h_bound : inner ℝ (gradient L (w + t • ε) - gradient L w) ε ≤
      (M : ℝ) * t * ‖ε‖ ^ 2 := by
    calc inner ℝ (gradient L (w + t • ε) - gradient L w) ε
        ≤ ‖gradient L (w + t • ε) - gradient L w‖ * ‖ε‖ := hcs
      _ ≤ ((M : ℝ) * t * ‖ε‖) * ‖ε‖ :=
        mul_le_mul_of_nonneg_right hlip (norm_nonneg ε)
      _ = (M : ℝ) * t * ‖ε‖ ^ 2 := by ring
  linarith [h_bound, h_2tm]

/-- **Segment-local L-smooth descent**:
This local form exists so callers can prove descent with assumptions only along
the interpolation segment, instead of global differentiability. -/
theorem smooth_descent_on_segment (L : W ι → ℝ) (w ε : W ι) (M : ℝ≥0)
    (h_path_cont : ContinuousOn (fun t : ℝ => L (w + t • ε)) (Icc 0 1))
    (h_diff_path : ∀ t ∈ Ico (0 : ℝ) 1, DifferentiableAt ℝ L (w + t • ε))
    (h_smooth : LipschitzWith M (gradient L)) :
    L (w + ε) ≤ L w + inner ℝ (gradient L w) ε + (M : ℝ) / 2 * ‖ε‖ ^ 2 := by
  -- Step 1: Define the auxiliary path function
  -- φ(t) = L(w + tε) - t⟨∇L(w), ε⟩ - t²/2 * M‖ε‖²
  let c := inner ℝ (gradient L w) ε
  let m := (M : ℝ) / 2 * ‖ε‖ ^ 2
  let φ : ℝ → ℝ := fun t => L (w + t • ε) - t * c - t ^ 2 * m
  -- Step 2: Show that the derivative of φ is non-positive on [0, 1]
  have hφ' : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivAt φ
      (inner ℝ (gradient L (w + t • ε) - gradient L w) ε - 2 * t * m) t := by
    intro t ht
    have h1 := path_hasDerivAt L w ε t (h_diff_path t ht)
    have h2 := (hasDerivAt_id t).mul_const c
    have h3 := (hasDerivAt_id t).pow 2 |>.mul_const m
    simpa only [
      inner_sub_left,
      id_eq,
      Pi.pow_apply,
      one_mul,
      Nat.cast_ofNat,
      Nat.add_one_sub_one,
      pow_one,
      mul_one
    ] using h1.sub h2 |>.sub h3
  have hφ'_nonpos : ∀ (t : ℝ), 0 ≤ t → t ≤ 1 →
      inner ℝ (gradient L (w + t • ε) - gradient L w) ε - 2 * t * m ≤ 0 := by
    intro t h0t ht1
    apply smooth_descent_phi_deriv_nonpos L w ε M h_smooth t h0t m
    simp only [m]; ring
  -- Step 3: Use the Boundary Derivative Lemma to conclude φ(1) ≤ φ(0)
  have hφ_cont : ContinuousOn φ (Icc (0 : ℝ) 1) := by
    have h_lin : ContinuousOn (fun t : ℝ => t * c) (Icc (0 : ℝ) 1) :=
      (continuous_id.mul continuous_const).continuousOn
    have h_quad : ContinuousOn (fun t : ℝ => t ^ 2 * m) (Icc (0 : ℝ) 1) :=
      ((continuous_id.pow 2).mul continuous_const).continuousOn
    exact (h_path_cont.sub h_lin).sub h_quad
  have hφ'within : ∀ t ∈ Ico (0 : ℝ) 1, HasDerivWithinAt φ
      (inner ℝ (gradient L (w + t • ε) - gradient L w) ε - 2 * t * m) (Ici t) t := by
    intro t ht
    exact (hφ' t ht).hasDerivWithinAt
  have hφ_le : φ 1 ≤ φ 0 :=
    smooth_descent_mvt_step hφ_cont hφ'within
      (fun x hx => hφ'_nonpos x hx.1 (le_of_lt hx.2))
  -- Step 4: Recover the descent bound from φ(1) ≤ φ(0)
  have hφ0 : φ 0 = L w := by simp only [
    zero_smul,
    add_zero,
    zero_mul,
    sub_zero,
    ne_eq,
    OfNat.ofNat_ne_zero,
    not_false_eq_true,
    zero_pow,
    φ
  ]
  simp only [
    one_smul,
    one_mul,
    one_pow,
    hφ0,
    tsub_le_iff_right,
    φ,
    c,
    m
  ] at hφ_le
  linarith

/-- **The L-Smooth Descent Lemma**:
Global differentiability corollary of `smooth_descent_on_segment`. -/
theorem smooth_descent (L : SmoothObjective ι) (w ε : W ι) :
    L.toFun (w + ε) ≤
      L.toFun w + inner ℝ (gradient L.toFun w) ε + (L.smoothness : ℝ) / 2 * ‖ε‖ ^ 2 := by
  have h_path_cont : ContinuousOn (fun t : ℝ => L.toFun (w + t • ε)) (Icc (0 : ℝ) 1) := by
    exact
      (L.differentiable.continuous.comp
        (continuous_const.add (continuous_id.smul continuous_const))).continuousOn
  have h_diff_path : ∀ t ∈ Ico (0 : ℝ) 1, DifferentiableAt ℝ L.toFun (w + t • ε) := by
    intro t _
    exact L.differentiable (w + t • ε)
  exact smooth_descent_on_segment L.toFun w ε L.smoothness h_path_cont h_diff_path L.lipschitz

/-- **SAM Taylor Terms Bound**: Auxiliary lemma to bound the SAM objective terms. -/
private lemma sam_taylor_terms_bound (M : ℝ≥0) (ρ : ℝ) (hρ : 0 ≤ ρ) (g ε : W ι)
    (h_norm : ‖ε‖ ≤ ρ) :
    inner ℝ g ε + (M : ℝ) / 2 * ‖ε‖ ^ 2 ≤ ‖g‖ * ρ + (M : ℝ) / 2 * ρ ^ 2 := by
  have hcs : inner ℝ g ε ≤ ‖g‖ * ρ := by
    calc inner ℝ g ε ≤ ‖g‖ * ‖ε‖ := real_inner_le_norm _ _
      _ ≤ ‖g‖ * ρ := mul_le_mul_of_nonneg_left h_norm (norm_nonneg _)
  have hsq : (M : ℝ) / 2 * ‖ε‖ ^ 2 ≤ (M : ℝ) / 2 * ρ ^ 2 := by
    apply mul_le_mul_of_nonneg_left (sq_le_sq.mpr (by
      simp only [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hρ, h_norm]))
    apply div_nonneg (NNReal.coe_nonneg M)
    norm_num
  linarith

/-- **SAM Taylor Bound**: `samObjective L w ρ ≤ L w + ‖∇L(w)‖ * ρ + M/2 * ρ²`. -/
theorem sam_taylor_bound (L : SmoothObjective ι) (w : W ι) (ρ : ℝ)
    (hρ : 0 ≤ ρ) :
    samObjective L.toFun w ρ ≤
      L.toFun w + ‖gradient L.toFun w‖ * ρ + (L.smoothness : ℝ) / 2 * ρ ^ 2 := by
  unfold samObjective perturbationNeighborhood
  apply csSup_le
  · exact ⟨L.toFun w, w, ⟨
      0,
      by simpa only [Metric.mem_closedBall, dist_self] using hρ,
      by simp only [add_zero]
    ⟩, rfl⟩
  · rintro v ⟨_, ⟨ε, hε_norm, rfl⟩, rfl⟩
    rw [Metric.mem_closedBall, dist_zero_right] at hε_norm
    -- Step 1: Apply the smooth descent lemma to the perturbation ε
    have hdescent := smooth_descent L w ε
    -- Step 2: Use the SAM Taylor Terms Bound helper lemma
    have h_terms := sam_taylor_terms_bound L.smoothness ρ hρ (gradient L.toFun w) ε hε_norm
    linarith [hdescent, h_terms]

/-- **One-Step Descent Recurrence**: For an L-smooth function, a gradient descent step
with learning rate $\eta \le 1/L$ ensures a decrease proportional to the gradient norm squared:
$L(w - \eta \nabla L(w)) \le L(w) - \frac{\eta}{2} \|\nabla L(w)\|^2$. -/
theorem smooth_one_step_descent (L : SmoothObjective ι) (w : W ι) (η : ℝ)
    (h_eta_nonneg : 0 ≤ η)
    (h_eta_bound : η * (L.smoothness : ℝ) ≤ 1) :
    L.toFun (w - η • gradient L.toFun w) ≤
      L.toFun w - (η / 2) * ‖gradient L.toFun w‖ ^ 2 := by
  set g := gradient L.toFun w
  have h_descent := smooth_descent L w (-(η • g))
  have h_step : w - η • g = w + -(η • g) := sub_eq_add_neg w (η • g)
  -- Step 1: Verify the descent radius bound
  have h_bound : (L.smoothness : ℝ) * η ≤ 1 := by
    simpa only [mul_comm] using h_eta_bound
  have h_inner_desc : inner ℝ g (-(η • g)) = -η * ‖g‖ ^ 2 := by
    rw [
      inner_neg_right,
      inner_smul_right,
      inner_self_eq_norm_sq_to_K,
      RCLike.ofReal_real_eq_id,
      id_eq,
      neg_mul
    ]
  have h_norm_desc : ‖-(η • g)‖ ^ 2 = η ^ 2 * ‖g‖ ^ 2 := by
    rw [norm_neg, norm_smul, norm_eq_abs, mul_pow, sq_abs]
  calc L.toFun (w - η • g)
    _ = L.toFun (w + -(η • g)) := by rw [h_step]
    _ ≤ L.toFun w + inner ℝ g (-(η • g)) +
        (L.smoothness : ℝ) / 2 * ‖-(η • g)‖ ^ 2 :=
      h_descent
    _ ≤ L.toFun w - (η / 2) * ‖g‖ ^ 2 := by
      have hquad : (L.smoothness : ℝ) / 2 * ‖-(η • g)‖ ^ 2 ≤ (η / 2) * ‖g‖ ^ 2 := by
        rw [h_norm_desc]
        have hMη_norm : ((L.smoothness : ℝ) * η) * ‖g‖ ^ 2 ≤ ‖g‖ ^ 2 := by
          nlinarith [h_bound, sq_nonneg ‖g‖]
        calc
          (L.smoothness : ℝ) / 2 * (η ^ 2 * ‖g‖ ^ 2)
              = (η / 2) * (((L.smoothness : ℝ) * η) * ‖g‖ ^ 2) := by ring
          _ ≤ (η / 2) * ‖g‖ ^ 2 :=
            mul_le_mul_of_nonneg_left hMη_norm (by nlinarith [h_eta_nonneg])
      calc
        L.toFun w + inner ℝ g (-(η • g)) + (L.smoothness : ℝ) / 2 * ‖-(η • g)‖ ^ 2
            ≤ L.toFun w + inner ℝ g (-(η • g)) + (η / 2) * ‖g‖ ^ 2 := by
              nlinarith [hquad]
        _ = L.toFun w - (η / 2) * ‖g‖ ^ 2 := by
          rw [h_inner_desc]
          ring

end LeanSharp
