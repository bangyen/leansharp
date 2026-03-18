/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Core.Filters
import LeanSharp.Core.Landscape
import LeanSharp.Core.Objective
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# SAM Differentiability

This module exists to prove differentiability conditions for SAM and z-sharp
update maps, which are required for higher-order structural analyses.

## Theorems

* `differentiable_at_sam_zsharp_update`.
-/

open Set Filter
open scoped Topology

namespace LeanSharp

variable {ι : Type*} [Fintype ι]
variable {L : W ι → ℝ} {w : W ι} {η ρ z : ℝ}

/-- The update function of SAM (z-sharp version) is differentiable at `w` if the loss
    is twice differentiable and the gradient is nonzero. -/
theorem differentiable_at_sam_zsharp_update
    (h_grad_diff_at_sam : DifferentiableAt ℝ (gradient L) (w + sam_perturbation L w ρ))
    (h_mask_stable : ∀ᶠ p in 𝓝 w, z_score_mask (gradient L (p + sam_perturbation L p ρ)) z =
      z_score_mask (gradient L (w + sam_perturbation L w ρ)) z)
    (h_sam_diff : DifferentiableAt ℝ (fun p => sam_perturbation L p ρ) w) :
    DifferentiableAt ℝ (fun p => sam_zsharp_update L p η ρ z) w := by
  unfold sam_zsharp_update
  apply DifferentiableAt.sub differentiableAt_id
  apply DifferentiableAt.smul (differentiableAt_const η)
  · -- Prove differentiability of the expression with constant mask
    let mask := z_score_mask (gradient L (w + sam_perturbation L w ρ)) z
    let f_hadam : W ι →L[ℝ] W ι :=
      (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm.toContinuousLinearEquiv.toContinuousLinearMap
      ∘L ((ContinuousLinearMap.pi fun i =>
        (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).smulRight (WithLp.equiv 2 (ι → ℝ) mask i))
      ∘L (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toContinuousLinearEquiv.toContinuousLinearMap)
    have hg : DifferentiableAt ℝ (fun p => gradient L (p + sam_perturbation L p ρ)) w := by
      have hg' : DifferentiableAt ℝ (fun p => p + sam_perturbation L p ρ) w :=
        differentiableAt_id.add h_sam_diff
      convert DifferentiableAt.comp w h_grad_diff_at_sam hg' using 1
    apply DifferentiableAt.congr_of_eventuallyEq (f_hadam.differentiableAt.comp w hg)
    · filter_upwards [h_mask_stable] with p hp
      unfold filtered_gradient hadamard
      simp only [hp]
      rfl

end LeanSharp
