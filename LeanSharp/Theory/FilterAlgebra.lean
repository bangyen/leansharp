/-
Copyright (c) 2024 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Z-Score Filter Algebra

This module contains lemmas regarding the algebraic properties of the Z-score filter.
These are "Green Zone" foundational proofs that do not require external axioms.
-/

namespace LeanSharp

variable {d : ℕ}

open BigOperators

/-- **Component Preservation**: If a component $i$ is within the Z-score threshold $z$,
the filtered gradient's $i$-th component is exactly the original gradient's $i$-th component. -/
theorem filtered_gradient_coord_preservation [Fact (0 < d)] (g : W d) (z : ℝ) (i : Fin d)
    (h_kept : (WithLp.equiv 2 (Fin d → ℝ) (z_score_mask g z)) i = 1) :
    (WithLp.equiv 2 (Fin d → ℝ) (filtered_gradient g z)) i =
    (WithLp.equiv 2 (Fin d → ℝ) g) i := by
  unfold filtered_gradient hadamard
  simp only [WithLp.equiv_apply, Equiv.apply_symm_apply]
  change _ * ((WithLp.equiv 2 (Fin d → ℝ) (z_score_mask g z)) i) = _
  rw [h_kept, mul_one]

/-- **Zero Outlier Amplification**: If the mean is zero, the filtered gradient
preserves all components exceeding $z \cdot \sigma$. -/
lemma outlier_preservation_zero_mean [Fact (0 < d)] (g : W d) (z : ℝ) (i : Fin d)
    (h_μ : vector_mean g = 0)
    (h_outlier : |(WithLp.equiv 2 (Fin d → ℝ) g) i| ≥ z * vector_std g) :
    (WithLp.equiv 2 (Fin d → ℝ) (filtered_gradient g z)) i =
    (WithLp.equiv 2 (Fin d → ℝ) g) i := by
  apply filtered_gradient_coord_preservation
  unfold z_score_mask
  simp only [WithLp.equiv_apply, Equiv.apply_symm_apply, h_μ]
  simp only [sub_zero]
  exact if_pos h_outlier

/-- **Non-Outlier Extraction**: If a component is NOT an outlier, it is zeroed out by the filter. -/
theorem filtered_gradient_zero_of_not_outlier [Fact (0 < d)] (g : W d) (z : ℝ) (i : Fin d)
    (h_not_outlier : |(WithLp.equiv 2 (Fin d → ℝ) g) i - vector_mean g| < z * vector_std g) :
    (WithLp.equiv 2 (Fin d → ℝ) (filtered_gradient g z)) i = 0 := by
  unfold filtered_gradient hadamard z_score_mask
  simp only [WithLp.equiv_apply, Equiv.apply_symm_apply]
  split_ifs with h_cond
  · -- Contradiction
    simp only [ge_iff_le] at h_cond
    -- Use change or have to unify if linarith fails
    have h_same : (WithLp.equiv 2 (Fin d → ℝ) g) i = g.ofLp i := rfl
    rw [← h_same] at h_cond
    linarith
  · rw [mul_zero]

/-- **Signal-to-Noise Amplification (Idealized)**: In the case where there is exactly
one outlier and the mean is zero, the filtered gradient is exactly that outlier. -/
theorem single_outlier_extraction [Fact (1 < d)] (g : W d) (z : ℝ) (i : Fin d)
    (h_μ : vector_mean g = 0)
    (h_outlier : |(WithLp.equiv 2 (Fin d → ℝ) g) i| ≥ z * vector_std g)
    (h_others : ∀ j : Fin d, j ≠ i → |(WithLp.equiv 2 (Fin d → ℝ) g) j| < z * vector_std g) :
    filtered_gradient g z = (WithLp.equiv 2 (Fin d → ℝ)).symm
      (fun j => if j = i then (WithLp.equiv 2 (Fin d → ℝ) g) i else 0) := by
  haveI : Fact (0 < d) := ⟨by linarith [Fact.out (p := 1 < d)]⟩
  apply (WithLp.equiv 2 (Fin d → ℝ)).injective
  ext j
  simp only [Equiv.apply_symm_apply, WithLp.equiv_apply]
  split_ifs with hj
  · rw [hj]; exact outlier_preservation_zero_mean g z i h_μ h_outlier
  · have h_not := h_others j hj
    have h_μ_j : |(WithLp.equiv 2 (Fin d → ℝ) g) j - vector_mean g| < z * vector_std g := by
      rw [h_μ, sub_zero]; exact h_not
    exact filtered_gradient_zero_of_not_outlier g z j h_μ_j

end LeanSharp
