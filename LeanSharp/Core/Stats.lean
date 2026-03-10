/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Sam
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Abs

namespace LeanSharp

open BigOperators

variable {d : ℕ}

/-- The mean of a vector in `W = ℝ^d`. -/
noncomputable def vector_mean (g : W d) : ℝ :=
  (∑ i : Fin d, (WithLp.equiv 2 (Fin d → ℝ) g) i) / (d : ℝ)

/-- The variance of a vector in $W = ℝ^d$. -/
noncomputable def vector_variance (g : W d) : ℝ :=
  let μ := vector_mean g
  (∑ i : Fin d, ((WithLp.equiv 2 (Fin d → ℝ) g) i - μ)^2) / (d : ℝ)

/-- The standard deviation `σ` is the square root of the variance. -/
noncomputable def vector_std (g : W d) : ℝ :=
  Real.sqrt (vector_variance g)

/-- The mean of a scalar-multiple vector is the scalar multiple of the original mean. -/
@[simp]
lemma vector_mean_smul (k : ℝ) (g : W d) :
    vector_mean (k • g) = k * vector_mean g := by
  unfold vector_mean
  have h_smul (i : Fin d) :
    (WithLp.equiv 2 (Fin d → ℝ) (k • g)) i = k * (WithLp.equiv 2 (Fin d → ℝ) g) i := rfl
  simp only [h_smul, ← Finset.mul_sum]
  rw [mul_div_assoc]

/-- The standard deviation scales linearly with a non-negative scalar. -/
@[simp]
lemma vector_std_smul {k : ℝ} (hk : 0 ≤ k) (g : W d) :
    vector_std (k • g) = k * vector_std g := by
  unfold vector_std
  have h_var_smul : vector_variance (k • g) = k^2 * vector_variance g := by
    unfold vector_variance; simp only [vector_mean_smul]
    have h_inner (i : Fin d) : ((WithLp.equiv 2 (Fin d → ℝ) (k • g)) i - k * vector_mean g)^2 =
      k^2 * ((WithLp.equiv 2 (Fin d → ℝ) g) i - vector_mean g)^2 := by
      have : (WithLp.equiv 2 (Fin d → ℝ) (k • g)) i = k * (WithLp.equiv 2 (Fin d → ℝ) g) i := rfl
      rw [this, ← mul_sub, mul_pow]
    simp only [h_inner, ← Finset.mul_sum, mul_div_assoc]
  rw [h_var_smul]
  have h_nonneg : 0 ≤ vector_variance g := by
    unfold vector_variance
    positivity
  rw [Real.sqrt_mul (sq_nonneg k), Real.sqrt_sq hk]

end LeanSharp
