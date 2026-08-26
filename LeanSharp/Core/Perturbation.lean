/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.PercentileFilters

/-!
# The ZSharp Ascent Step

This module defines the perturbation of *Sharpness-Aware Minimization with Z-Score
Gradient Filtering* (arXiv:2505.02369) over the percentile filter, which is the
paper's own thresholding rule.

The paper's numerical-stability term $\delta = 10^{-8}$ is omitted: it guards a
floating-point division that cannot underflow over $\mathbb{R}$, and both branches
here are already total.

## Main definitions

* `zsharpPerturbation`: the paper's ascent step.

## Main theorems

* `norm_zsharpPerturbation_le`: the ascent step stays in the radius-$\rho$ ball.
* `zsharpPerturbation_eq_samPerturbation_of_filtered_zero`: the fallback degenerates
  to the ordinary SAM perturbation.
-/

namespace LeanSharp

variable {ι : Type*} [Fintype ι] {Λ : Type*} [DecidableEq Λ]

/-- The ZSharp first-order perturbation of arXiv:2505.02369,

$$\varepsilon = \rho \cdot \nabla L(w)_\Omega / \lVert \nabla L(w)_\Omega \rVert_2,$$

with `∇L(w)_Ω` the percentile-filtered gradient and a fallback to the unfiltered
direction when the filter annihilates it. `Q_p` is the paper's single hyperparameter;
`π` names the layers. -/
noncomputable def zsharpPerturbation (L : W ι → ℝ) (w : W ι) (π : ι → Λ)
    (ρ Qp : ℝ) : W ι :=
  let g_f := percentileFilteredGradient (gradient L w) π Qp
  if ‖g_f‖ = 0 then samPerturbation L w ρ else (ρ / ‖g_f‖) • g_f

/-- **ZSharp Perturbation Radius**: like the SAM step, the ZSharp perturbation stays
inside the radius-`ρ` ball. -/
lemma norm_zsharpPerturbation_le (L : W ι → ℝ) (w : W ι) (π : ι → Λ) (ρ Qp : ℝ)
    (hρ : 0 ≤ ρ) : ‖zsharpPerturbation L w π ρ Qp‖ ≤ ρ := by
  simp only [zsharpPerturbation]
  split_ifs with h_zero
  · exact norm_samPerturbation_le L w ρ hρ
  · rw [norm_smul, Real.norm_eq_abs, abs_div, abs_of_nonneg hρ,
      abs_of_pos (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h_zero))]
    field_simp
    exact le_rfl

/-- **ZSharp Fallback**: when the percentile filter annihilates the gradient, the
perturbation degenerates to the ordinary SAM perturbation. -/
lemma zsharpPerturbation_eq_samPerturbation_of_filtered_zero (L : W ι → ℝ) (w : W ι)
    (π : ι → Λ) (ρ Qp : ℝ)
    (h_zero : ‖percentileFilteredGradient (gradient L w) π Qp‖ = 0) :
    zsharpPerturbation L w π ρ Qp = samPerturbation L w ρ := by
  simp only [zsharpPerturbation, h_zero, ite_true]

end LeanSharp
