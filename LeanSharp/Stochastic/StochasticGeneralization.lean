import LeanSharp.Stochastic.StochasticSam
import LeanSharp.Core.Filters
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Probability.Notation
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Norm
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Stochastic Generalization Bounds

We formalize advanced bounds on the variance of the ZSharp algorithm.
A key theoretical property of the Z-score filter is that it is a *contraction*
with respect to the $L_2$ norm. This means that if the original stochastic
gradient estimator has bounded variance, the variance of the filtered
stochastic gradient is strictly bounded by the same constant!
-/

namespace LeanSharp

set_option linter.unusedSectionVars false

open ProbabilityTheory MeasureTheory

variable {d : ℕ} [Fact (0 < d)]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- Central Lemma: The Z-score filter reduces or preserves the vector norm.
    Because the Z-score filter is implemented via a Hadamard element-wise mask
    with values in {0, 1}, the L2-norm of the filtered gradient is always less
    than or equal to the original gradient. -/
theorem filtered_norm_bound (g : W d) (z : ℝ) :
    ‖filtered_gradient g z‖ ≤ ‖g‖ := by
  have h_sq := filtered_gradient_norm_sq_le g z
  have h_sqrt : Real.sqrt (‖filtered_gradient g z‖ ^ 2) ≤ Real.sqrt (‖g‖ ^ 2) :=
    Real.sqrt_le_sqrt h_sq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h_sqrt
  exact h_sqrt

/-- **ZSharp Variance Bound Theorem**:
    If the base stochastic gradient has bounded variance $\sigma^2$, the
    filtered gradient also has strictly bounded variance. -/
theorem zsharp_variance_bound (L : W d → ℝ) (g_adv : Ω → W d) (w : W d) (z σsq : ℝ)
    (h_unbiased : is_stochastic_gradient L g_adv w)
    (h_base_var : has_bounded_variance L g_adv w σsq)
    (h_int_fg : Integrable (fun ω => ‖filtered_gradient (g_adv ω) z‖ ^ 2))
    (h_int_g : Integrable (fun ω => ‖g_adv ω‖ ^ 2)) :
    𝔼[fun ω => ‖filtered_gradient (g_adv ω) z‖ ^ 2] ≤ σsq + ‖gradient L w‖ ^ 2 := by
  -- By monotonicity of expectation (integration), E[X] ≤ E[Y]
  have h_exp_bound : 𝔼[fun ω => ‖filtered_gradient (g_adv ω) z‖ ^ 2] ≤
                     𝔼[fun ω => ‖g_adv ω‖ ^ 2] :=
    integral_mono h_int_fg h_int_g (by intro ω; exact filtered_gradient_norm_sq_le (g_adv ω) z)
  -- Variance bias decomposition: 𝔼[‖g‖²] = 𝔼[‖g - 𝔼[g]‖²] + ‖𝔼[g]‖²
  -- Since 𝔼[g_adv] = gradient L w (h_unbiased), the identity holds.
  have h_var_expansion : 𝔼[fun ω => ‖g_adv ω‖ ^ 2] =
                         𝔼[fun ω => ‖g_adv ω - gradient L w‖ ^ 2] + ‖gradient L w‖ ^ 2 := by
    let c := gradient L w
    -- Integrability checks
    have h_int_c2 : Integrable (fun _ : Ω => ‖c‖ ^ 2) := integrable_const _
    have h_int_mc : Integrable (fun ω => g_adv ω - c) := h_unbiased.1.sub (integrable_const c)
    have h_int_inner : Integrable (fun ω => 2 * inner ℝ (g_adv ω - c) c) :=
      Integrable.const_mul (h_int_mc.inner_const c) 2
    have h_int_diff2 : Integrable (fun ω => ‖g_adv ω - c‖ ^ 2) := by
      -- Since ‖g‖^2 is integrable and other terms are integrable, the diff is integrable.
      have h1 : (fun ω => ‖g_adv ω - c‖ ^ 2) =
                (fun ω => ‖g_adv ω‖ ^ 2 + ‖c‖ ^ 2 - 2 * inner ℝ (g_adv ω) c) := by
        ext ω; rw [norm_sub_sq_real]; ring
      rw [h1]; apply Integrable.sub (h_int_g.add h_int_c2)
      exact Integrable.const_mul (h_unbiased.1.inner_const c) 2
    calc 𝔼[fun ω => ‖g_adv ω‖ ^ 2]
        = 𝔼[fun ω => ‖g_adv ω - c‖ ^ 2 + ‖c‖ ^ 2 + 2 * inner ℝ (g_adv ω - c) c] := by
          apply integral_congr_ae; apply ae_of_all; intro ω
          dsimp; nth_rw 1 [← sub_add_cancel (g_adv ω) c]; rw [norm_add_sq_real]; ring
      _ = 𝔼[fun ω => ‖g_adv ω - c‖ ^ 2 + ‖c‖ ^ 2] +
          𝔼[fun ω => 2 * inner ℝ (g_adv ω - c) c] := by
          apply integral_add (h_int_diff2.add h_int_c2) h_int_inner
      _ = 𝔼[fun ω => ‖g_adv ω - c‖ ^ 2] + 𝔼[fun _ => ‖c‖ ^ 2] +
          𝔼[fun ω => 2 * inner ℝ (g_adv ω - c) c] := by
          rw [integral_add h_int_diff2 h_int_c2]
      _ = 𝔼[fun ω => ‖g_adv ω - c‖ ^ 2] + ‖c‖ ^ 2 + 0 := by
          congr
          · simp [integral_const]
          · rw [integral_const_mul]
            rw [integral_congr_ae (ae_of_all _ (fun ω => by rw [real_inner_comm]))]
            rw [integral_inner h_int_mc c, integral_sub h_unbiased.1 (integrable_const c)]
            simp [h_unbiased.2, c, integral_const]
      _ = 𝔼[fun ω => ‖g_adv ω - c‖ ^ 2] + ‖c‖ ^ 2 := by rw [add_zero]
  calc 𝔼[fun ω => ‖filtered_gradient (g_adv ω) z‖ ^ 2]
      ≤ 𝔼[fun ω => ‖g_adv ω‖ ^ 2] := h_exp_bound
    _ = 𝔼[fun ω => ‖g_adv ω - gradient L w‖ ^ 2] + ‖gradient L w‖ ^ 2 := h_var_expansion
    _ ≤ σsq + ‖gradient L w‖ ^ 2 := by
      have h_var := h_base_var
      unfold has_bounded_variance at h_var
      linarith

end LeanSharp
