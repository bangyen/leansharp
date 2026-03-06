/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Sam
import LeanSharp.Core.Filters
import Mathlib.Probability.Notation
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Stochastic ZSharp Modeling

This module extends the deterministic ZSharp algorithm to the stochastic setting,
where gradients are observed with zero-mean noise.

## Main definitions

* `is_stochastic_gradient`: Predicate for a random vector being an unbiased
  estimator of the true gradient.
* `has_bounded_variance`: Assumption that the stochastic gradient has variance
  bounded by $\sigma^2$.
* `stochastic_zsharp_step`: The stochastic parameter update rule for ZSharp.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {d : ℕ} [Fact (0 < d)]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- A stochastic gradient is a random vector `W d`.
We typically assume it is based on a true gradient plus some noise `ξ`. -/
def is_stochastic_gradient (L : W d → ℝ) (g : Ω → W d) (w : W d) : Prop :=
  Integrable g ∧ 𝔼[g] = gradient L w

/-- Bounded variance assumption for the stochastic gradient. -/
def has_bounded_variance (L : W d → ℝ) (g : Ω → W d) (w : W d) (σsq : ℝ) : Prop :=
  𝔼[fun ω => ‖g ω - gradient L w‖^2] ≤ σsq

/-- The Stochastic ZSharp update rule.
`w_{t+1} = w_t - η * filtered_gradient(g_adv, z)`
where `g_adv` is a stochastic adversarial gradient. -/
noncomputable def stochastic_zsharp_step (w : W d) (η z : ℝ) (g_adv : Ω → W d) (ω : Ω) : W d :=
  let g_f := filtered_gradient (g_adv ω) z
  w - η • g_f

/-- **L2 Bias-Variance Decomposition**: The standard identity
$𝔼[‖g‖^2] = 𝔼[‖g - 𝔼[g]‖^2] + ‖𝔼[g]‖^2$ for any random vector $g$. -/
theorem l2_bias_variance_decomposition {d : ℕ} [Fact (0 < d)] {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    (g : Ω → W d) (h_int : Integrable (fun ω => ‖g ω‖ ^ 2))
    (h_int_g : Integrable g) :
    𝔼[fun ω => ‖g ω‖ ^ 2] = 𝔼[fun ω => ‖g ω - 𝔼[g]‖ ^ 2] + ‖𝔼[g]‖ ^ 2 := by
  let c := 𝔼[g]
  -- Verify integrability for all expansion terms
  have h_int_c : Integrable (fun _ : Ω => c) := integrable_const c
  have h_int_c2 : Integrable (fun _ : Ω => ‖c‖ ^ 2) := integrable_const _
  have h_int_mc : Integrable (fun ω => g ω - c) := h_int_g.sub h_int_c
  have h_int_inner : Integrable (fun ω => 2 * inner ℝ (g ω - c) c) :=
    Integrable.const_mul (h_int_mc.inner_const c) 2
  have h_int_diff2 : Integrable (fun ω => ‖g ω - c‖ ^ 2) := by
    -- ‖g-c‖² = ‖g‖² + ‖c‖² - 2⟨g, c⟩
    have h1 : (fun ω => ‖g ω - c‖ ^ 2) =
              (fun ω => ‖g ω‖ ^ 2 + ‖c‖ ^ 2 - 2 * inner ℝ (g ω) c) := by
      ext ω; rw [norm_sub_sq_real]; ring
    rw [h1]; apply Integrable.sub (h_int.add h_int_c2)
    exact Integrable.const_mul (h_int_g.inner_const c) 2
  calc 𝔼[fun ω => ‖g ω‖ ^ 2]
      -- Expand ‖g‖² = ‖(g - c) + c‖²
      = 𝔼[fun ω => ‖g ω - c‖ ^ 2 + ‖c‖ ^ 2 + 2 * inner ℝ (g ω - c) c] := by
        apply integral_congr_ae; apply ae_of_all; intro ω
        dsimp; nth_rw 1 [← sub_add_cancel (g ω) c]; rw [norm_add_sq_real]; ring
      _ = 𝔼[fun ω => ‖g ω - c‖ ^ 2 + ‖c‖ ^ 2] +
          𝔼[fun ω => 2 * inner ℝ (g ω - c) c] := by
          apply integral_add (h_int_diff2.add h_int_c2) h_int_inner
      _ = 𝔼[fun ω => ‖g ω - c‖ ^ 2] + 𝔼[fun _ => ‖c‖ ^ 2] +
          𝔼[fun ω => 2 * inner ℝ (g ω - c) c] := by
          rw [integral_add h_int_diff2 h_int_c2]
      -- E[⟨g - E[g], c⟩] = ⟨E[g] - E[g], c⟩ = 0
      _ = 𝔼[fun ω => ‖g ω - c‖ ^ 2] + ‖c‖ ^ 2 + 0 := by
          congr
          · simp [integral_const]
          · rw [integral_const_mul]
            rw [integral_congr_ae (ae_of_all _ (fun ω => by rw [real_inner_comm]))]
            rw [integral_inner h_int_mc c, integral_sub h_int_g h_int_c]
            simp [c, integral_const]
      _ = 𝔼[fun ω => ‖g ω - c‖ ^ 2] + ‖c‖ ^ 2 := by rw [add_zero]

end LeanSharp
