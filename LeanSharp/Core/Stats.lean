/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Core.Objective
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Basic

/-!
# Statistical Primitives

This module exists to define means, variances, z-scores, and masking lemmas for
gradient vectors so filtering proofs can share a common statistical foundation.

The geometric median lives in `LeanSharp.Core.GeometricMedian`.

## Definitions

* `vectorMean`.
* `vectorVariance`.
* `vectorStd`.

## Theorems

* `contDiff_vectorMean`: The mean of a vector is $C^\infty$.
* `contDiff_vectorNormalize`: Normalizing a vector is $C^\infty$.
* `contDiff_vectorVariance`: The variance of a vector is $C^\infty$.
* `vectorMean_normalize`: The mean of a normalized vector is zero.
* `vectorMean_smul`.
* `vectorMean_sub_mean`: The mean of a vector shifted by its own mean is zero.
* `vectorVariance_nonneg`.
* `vectorVariance_smul`.
* `vectorStd_smul`.
* `eq_mean_of_vectorVariance_eq_zero`.
-/

namespace LeanSharp

open BigOperators

variable {ι : Type*} [Fintype ι]

/-- The mean of a vector in `W = ℝ^d`. -/
noncomputable def vectorMean (g : W ι) : ℝ :=
  (∑ i : ι, (WithLp.equiv 2 (ι → ℝ) g) i) / (Fintype.card ι : ℝ)

/-- The variance of a vector in $W = ℝ^d$. -/
noncomputable def vectorVariance (g : W ι) : ℝ :=
  let μ := vectorMean g
  (∑ i : ι, ((WithLp.equiv 2 (ι → ℝ) g) i - μ)^2) / (Fintype.card ι : ℝ)

/-- The standard deviation `σ` is the square root of the variance. -/
noncomputable def vectorStd (g : W ι) : ℝ :=
  Real.sqrt (vectorVariance g)

/-- The mean of a scalar-multiple vector is the scalar multiple of the original mean. -/
@[simp]
lemma vectorMean_smul (k : ℝ) (g : W ι) :
    vectorMean (k • g) = k * vectorMean g := by
  unfold vectorMean
  have h_smul (i : ι) :
    (WithLp.equiv 2 (ι → ℝ) (k • g)) i = k * (WithLp.equiv 2 (ι → ℝ) g) i := rfl
  simp only [h_smul, ← Finset.mul_sum]
  rw [mul_div_assoc]

/-- The variance is always non-negative. -/
lemma vectorVariance_nonneg (g : W ι) : 0 ≤ vectorVariance g := by
  unfold vectorVariance; positivity

/-- The variance of a scalar-multiple vector. -/
@[simp]
lemma vectorVariance_smul (k : ℝ) (g : W ι) :
    vectorVariance (k • g) = k^2 * vectorVariance g := by
  unfold vectorVariance
  rw [vectorMean_smul]
  have h_inner (i : ι) : ((WithLp.equiv 2 (ι → ℝ) (k • g)) i - k * vectorMean g)^2 =
      k^2 * ((WithLp.equiv 2 (ι → ℝ) g) i - vectorMean g)^2 := by
    have : (WithLp.equiv 2 (ι → ℝ) (k • g)) i =
        k * (WithLp.equiv 2 (ι → ℝ) g) i := rfl
    rw [this, ← mul_sub, mul_pow]
  simp only [h_inner, ← Finset.mul_sum, mul_div_assoc]

/-- The standard deviation scales with the absolute value of the scalar. -/
@[simp]
lemma vectorStd_smul (k : ℝ) (g : W ι) :
    vectorStd (k • g) = |k| * vectorStd g := by
  unfold vectorStd
  rw [vectorVariance_smul, Real.sqrt_mul (sq_nonneg k), Real.sqrt_sq_eq_abs]

/-- If the variance of a vector is zero, then all its components are equal to the mean. -/
lemma eq_mean_of_vectorVariance_eq_zero [Nonempty ι] (g : W ι) (h : vectorVariance g = 0) :
    ∀ i : ι, (WithLp.equiv 2 (ι → ℝ) g) i = vectorMean g := by
  unfold vectorVariance at h
  have h_card : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  have h_sum : ∑ i : ι, ((WithLp.equiv 2 (ι → ℝ) g) i - vectorMean g)^2 = 0 := by
    field_simp [h_card] at h; simp only [mul_zero] at h; exact h
  intro i
  have : ((WithLp.equiv 2 (ι → ℝ) g) i - vectorMean g)^2 = 0 := by
    apply Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _) |>.mp h_sum
    exact Finset.mem_univ i
  exact sub_eq_zero.mp (sq_eq_zero_iff.mp this)

/-- The mean of a vector shifted by its own mean is zero. -/
lemma vectorMean_sub_mean [Nonempty ι] (g : W ι) :
    vectorMean (WithLp.equiv 2 (ι → ℝ) |>.symm fun i =>
      (WithLp.equiv 2 _ g) i - vectorMean g) = 0 := by
  unfold vectorMean
  simp only [WithLp.equiv_apply, WithLp.equiv_symm_apply]
  have h_card : (Fintype.card ι : ℝ) ≠ 0 := by positivity
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp [h_card]
  ring

/-- Normalize a vector using its mean and variance with a stability epsilon. -/
noncomputable def vectorNormalize (x : W ι) (ε : ℝ) : W ι :=
  let μ := vectorMean x
  let σ_inv := 1 / Real.sqrt (vectorVariance x + ε)
  WithLp.equiv 2 _ |>.symm fun i =>
    σ_inv * ((WithLp.equiv 2 _ x) i - μ)

/-- The mean of a normalized vector is zero. -/
theorem vectorMean_normalize [Nonempty ι] (x : W ι) (ε : ℝ) :
    vectorMean (vectorNormalize x ε) = 0 := by
  unfold vectorNormalize
  let σ_inv := 1 / Real.sqrt (vectorVariance x + ε)
  have h_lp : (WithLp.equiv 2 (ι → ℝ)).symm (fun i =>
      σ_inv * ((WithLp.equiv 2 (ι → ℝ) x) i - vectorMean x)) =
      σ_inv • (WithLp.equiv 2 (ι → ℝ)).symm (fun i =>
      (WithLp.equiv 2 (ι → ℝ) x) i - vectorMean x) := by
    apply (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm.map_smul
  rw [h_lp, vectorMean_smul, vectorMean_sub_mean, mul_zero]

/-- **Vector Mean Smoothness**: The mean of a vector is $C^\infty$. -/
theorem contDiff_vectorMean (ι : Type*) [Fintype ι] :
    ContDiff ℝ ⊤ (vectorMean (ι := ι)) := by
  unfold vectorMean
  apply ContDiff.div_const
  apply ContDiff.sum
  intro i _
  exact contDiff_piLp_apply (p := 2) (i := i)

/-- **Vector Variance Smoothness**: The variance of a vector is $C^\infty$. -/
theorem contDiff_vectorVariance (ι : Type*) [Fintype ι] :
    ContDiff ℝ ⊤ (vectorVariance (ι := ι)) := by
  unfold vectorVariance
  apply ContDiff.div_const
  apply ContDiff.sum
  intro i _
  apply ContDiff.pow
  apply ContDiff.sub
  · exact contDiff_piLp_apply (p := 2) (i := i)
  · exact contDiff_vectorMean (ι := ι)

/-- **Vector Normalize Smoothness**: Normalizing a vector is $C^\infty$ (and thus $C^2$)
    provided the stability epsilon is strictly positive. -/
theorem contDiff_vectorNormalize (ι : Type*) [Fintype ι] {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ ⊤ (fun (x : W ι) => vectorNormalize x ε) := by
  unfold vectorNormalize
  apply contDiff_piLp' (p := 2)
  intro i
  apply ContDiff.mul
  · apply ContDiff.div
    · exact contDiff_const
    · apply ContDiff.sqrt
      · apply ContDiff.add
        · apply contDiff_vectorVariance
        · exact contDiff_const
      · intro x; linarith [vectorVariance_nonneg x]
    · intro x; apply ne_of_gt; apply Real.sqrt_pos.mpr; linarith [vectorVariance_nonneg x]
  · apply ContDiff.sub
    · exact contDiff_piLp_apply (p := 2) (i := i)
    · apply contDiff_vectorMean

end LeanSharp
