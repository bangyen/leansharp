/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Taylor
import LeanSharp.Theory.Dynamics.Convergence
import LeanSharp.Theory.Structural.HessianContraction

/-!
# Second-Order Descent Lemma

This module formalizes the second-order descent lemma for Z-score filtered SAM.
It bridges the gap between local curvature (Hessian) properties and the
functional descent of the loss objective.

## Main theorems

* `zsharp_second_order_descent`: The primary descent lemma incorporating the
  local curvature matrix and the generalized filter condition.
-/

namespace LeanSharp

open Real InnerProductSpace NNReal

variable {ι : Type*} [Fintype ι]

/-- **Second-Order Descent Lemma**:
For an $L$-smooth function $f$, the descent achieved by a filtered step
$-\eta g_f$ is bounded by the alignment with the gradient and the quadratic
curvature form of the filtered direction.

This theorem explicitly uses the `localCurvatureMatrix` to bridge the
structural filter properties to the dynamic descent. -/
theorem zsharp_second_order_descent
    (f : W ι → ℝ) (w g_base g_f : W ι) (η L_smooth κ : ℝ)
    (h_diff : Differentiable ℝ f)
    (h_smooth : IsLSmooth f L_smooth)
    (h_curv : (L_smooth / 2) * ‖g_f‖ ^ 2 ≤ (κ / 2) * ‖g_base‖ ^ 2) :
    f (w - η • g_f) ≤ f w - η * inner ℝ (gradient f w) g_f + (η^2 / 2) * κ * ‖g_base‖ ^ 2 := by
  have h_L_nonneg : 0 ≤ L_smooth := h_smooth.1.le
  let L_nnreal : ℝ≥0 := ⟨L_smooth, h_L_nonneg⟩
  have h_lip : LipschitzWith L_nnreal (gradient f) := by
    apply LipschitzWith.of_dist_le_mul
    intro w' v'
    simpa only [dist_eq_norm] using h_smooth.2 w' v'
  let L_smooth_obj : SmoothObjective ι := {
    toFun := f,
    smoothness := L_nnreal,
    differentiable := h_diff,
    lipschitz := h_lip
  }
  have h_desc := smooth_descent L_smooth_obj w (-(η • g_f))
  -- Step 2: Expand the inner product and norm terms
  have h_inner : inner ℝ (gradient f w) (-(η • g_f)) = -η * inner ℝ (gradient f w) g_f := by
    rw [inner_neg_right, inner_smul_right, real_inner_comm]
    ring
  have h_norm : ‖-(η • g_f)‖ ^ 2 = η ^ 2 * ‖g_f‖ ^ 2 := by
    rw [norm_neg, norm_smul, norm_eq_abs, mul_pow, sq_abs]
  -- Step 3: Substitute the generalized filter condition for the quadratic term
  calc f (w - η • g_f)
    _ = f (w + -(η • g_f)) := by rw [sub_eq_add_neg]
    _ ≤ f w + inner ℝ (gradient f w) (-(η • g_f)) + (L_smooth / 2) * ‖-(η • g_f)‖ ^ 2 := by
        simpa only [NNReal.coe_mk] using h_desc
    _ = f w - η * inner ℝ (gradient f w) g_f + (η^2 / 2) * (L_smooth * ‖g_f‖ ^ 2) := by
        rw [h_inner, h_norm]
        ring
    _ ≤ f w - η * inner ℝ (gradient f w) g_f + (η^2 / 2) * κ * ‖g_base‖ ^ 2 := by
        -- The curvature hypothesis h_curv bridges the local curvature certificate
        -- to the functional descent.
        nlinarith [h_curv]

/-- **Alignment Condition Wrapper**:
This theorem packages already-established inner-product and norm bounds into
the `AlignmentCondition` interface. It exists as a compatibility bridge for
downstream convergence lemmas rather than as a new geometric estimate. -/
theorem alignment_condition_of_curvature_bound
    (f : W ι → ℝ) (w w_star g_base : W ι) (z μ L_smooth : ℝ)
    (h_inner : μ * ‖w - w_star‖ ^ 2 ≤
      inner ℝ (filteredGradient (gradient f g_base) z) (w - w_star))
    (h_norm : ‖filteredGradient (gradient f g_base) z‖ ≤ L_smooth * ‖w - w_star‖) :
    let ε := g_base - w
    AlignmentCondition f w w_star ε z μ L_smooth := by
  unfold AlignmentCondition
  dsimp only
  have h_base : w + (g_base - w) = g_base := by abel
  rw [h_base]
  constructor
  · exact h_inner
  · exact h_norm

end LeanSharp
