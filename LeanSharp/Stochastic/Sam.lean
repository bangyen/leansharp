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
import Mathlib.Analysis.InnerProductSpace.Basic
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

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω]

/-- A stochastic gradient is a random vector `W ι`.
We typically assume it is based on a true gradient plus some noise `ξ`. -/
def is_stochastic_gradient (L : W ι → ℝ) (g : Ω → W ι) (w : W ι) : Prop :=
  Integrable g ∧ 𝔼[g] = gradient L w

/-- Bounded variance assumption for the stochastic gradient. -/
def has_bounded_variance (L : W ι → ℝ) (g : Ω → W ι) (w : W ι) (σsq : ℝ) : Prop :=
  𝔼[fun ω => ‖g ω - gradient L w‖^2] ≤ σsq

/-- The Stochastic ZSharp update rule with a learning rate schedule.
`w_{t+1} = w_t - η_t * filtered_gradient(g_adv, z)`
where `g_adv` is a stochastic adversarial gradient. -/
noncomputable def stochastic_zsharp_step (w : W ι) (η : ℕ → ℝ) (t : ℕ) (z : ℝ)
    (g_adv : Ω → W ι) (ω : Ω) : W ι :=
  let g_f := filtered_gradient (g_adv ω) z
  w - (η t) • g_f

/-- **L2 Bias-Variance Integrability**: Helper lemma containing the integrability checks
for the decomposition. -/
private lemma l2_bias_variance_integrability {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    (g : Ω → W ι) (h_int : Integrable (fun ω => ‖g ω‖ ^ 2))
    (h_int_g : Integrable g) :
    let c := 𝔼[g]
    Integrable (fun _ : Ω => c) ∧
    Integrable (fun _ : Ω => ‖c‖ ^ 2) ∧
    Integrable (fun ω => g ω - c) ∧
    Integrable (fun ω => 2 * inner ℝ (g ω - c) c) ∧
    Integrable (fun ω => ‖g ω - c‖ ^ 2) := by
  let c := 𝔼[g]
  have h_int_c : Integrable (fun _ : Ω => c) := integrable_const c
  have h_int_c2 : Integrable (fun _ : Ω => ‖c‖ ^ 2) := integrable_const _
  have h_int_mc : Integrable (fun ω => g ω - c) := h_int_g.sub h_int_c
  have h_int_inner : Integrable (fun ω => 2 * inner ℝ (g ω - c) c) :=
    Integrable.const_mul (h_int_mc.inner_const c) 2
  have h_int_diff2 : Integrable (fun ω => ‖g ω - c‖ ^ 2) := by
    have h1 : (fun ω => ‖g ω - c‖ ^ 2) =
              (fun ω => ‖g ω‖ ^ 2 + ‖c‖ ^ 2 - 2 * inner ℝ (g ω) c) := by
      ext ω; rw [norm_sub_sq_real]; ring
    rw [h1]; apply Integrable.sub (h_int.add h_int_c2)
    exact Integrable.const_mul (h_int_g.inner_const c) 2
  refine ⟨h_int_c, h_int_c2, h_int_mc, h_int_inner, h_int_diff2⟩

/-- **L2 Bias-Variance Decomposition**: The standard identity
$𝔼[‖g‖ ^ 2] = 𝔼[‖g - 𝔼[g]‖ ^ 2] + ‖𝔼[g]‖ ^ 2$ for any random vector $g$. -/
theorem l2_bias_variance_decomposition {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)]
    (g : Ω → W ι) (h_int : Integrable (fun ω => ‖g ω‖ ^ 2))
    (h_int_g : Integrable g) :
    𝔼[fun ω => ‖g ω‖ ^ 2] = 𝔼[fun ω => ‖g ω - 𝔼[g]‖ ^ 2] + ‖𝔼[g]‖ ^ 2 := by
  let c := 𝔼[g]
  obtain ⟨h_int_c, h_int_c2, h_int_mc, h_int_inner, h_int_diff2⟩ :=
    l2_bias_variance_integrability g h_int h_int_g
  calc 𝔼[fun ω => ‖g ω‖ ^ 2]
      = 𝔼[fun ω => ‖g ω - c‖ ^ 2 + ‖c‖ ^ 2 + 2 * inner ℝ (g ω - c) c] := by
        congr; ext ω; dsimp only; nth_rw 1 [← sub_add_cancel (g ω) c]; rw [norm_add_sq_real]; ring
    _ = 𝔼[fun ω => ‖g ω - c‖ ^ 2] + ‖c‖ ^ 2 := by
        have h_int_inner' : Integrable (fun ω => inner ℝ (g ω - c) c) :=
          h_int_mc.inner_const c
        have h_zero : 𝔼[fun ω => inner ℝ (g ω - c) c] = 0 := by
          simp_rw [real_inner_comm]
          erw [integral_inner h_int_mc c, integral_sub h_int_g h_int_c]
          simp only [
            integral_const,
            probReal_univ,
            one_smul,
            sub_self,
            inner_zero_right,
            c
          ]
        dsimp only [c] at *
        simp only [
          h_int_diff2,
          integrable_add_iff_integrable_right',
          h_int_c2,
          h_int_inner,
          integral_add,
          integral_const,
          probReal_univ,
          smul_eq_mul,
          one_mul,
          integral_const_mul,
          h_zero,
          mul_zero,
          add_zero
        ]

end LeanSharp
