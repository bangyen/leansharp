/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Core.Objective
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.Basic

/-!
# Statistical Primitives

This module exists to define means, variances, z-scores, and masking lemmas for
gradient vectors so filtering proofs can share a common statistical foundation.

## Definitions

* `vectorMean`.
* `vectorVariance`.
* `vectorStd`.
* `geometricMedian`.

## Theorems

* `vectorMean_smul`.
* `vectorVariance_nonneg`.
* `vectorVariance_smul`.
* `vectorStd_smul`.
* `continuous_sum_distances`.
* `tendsto_sum_distances_cocompact`.
* `exists_isMin_on_finite_sum_norm`.
* `geometricMedian_eq_choose`.
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

/-- The sum of Euclidean distances from `m` to a set of vectors `g_i` is continuous. -/
lemma continuous_sum_distances {α : Type*} (s : Finset α) (g : α → W ι) :
    Continuous (fun m : W ι => ∑ i ∈ s, ‖g i - m‖) := by
  apply continuous_finset_sum
  intro i _
  apply continuous_norm.comp
  apply continuous_const.sub continuous_id

/-- The sum of distances is coercive: it tends to infinity as `m` grows. -/
lemma tendsto_sum_distances_cocompact {α : Type*} (s : Finset α)
    (g : α → W ι) (hs : s.Nonempty) :
    Filter.Tendsto (fun m : W ι => ∑ i ∈ s, ‖g i - m‖)
      (Filter.cocompact (W ι)) Filter.atTop := by
  let i0 := hs.choose
  have hi0 : i0 ∈ s := hs.choose_spec
  apply Filter.tendsto_atTop_mono (α := W ι) (f := fun m => ‖g i0 - m‖)
  · intro m
    apply Finset.single_le_sum (f := fun i => ‖g i - m‖) (fun i _ => norm_nonneg _) hi0
  · -- tendsto ‖g i0 - m‖ cocompact implies it grows.
    apply Filter.tendsto_atTop_mono (f := fun m => ‖m‖ - ‖g i0‖)
    · intro m; rw [norm_sub_rev]; apply norm_sub_norm_le
    · rw [Filter.tendsto_atTop]
      intro b
      filter_upwards [tendsto_norm_cocompact_atTop.eventually_ge_atTop (b + ‖g i0‖)] with m hm
      linarith

/-- The geometric median objective possesses a minimizer for every finite index set. -/
lemma exists_isMin_on_finite_sum_norm {α : Type*} (s : Finset α) (g : α → W ι) :
    ∃ m : W ι, IsMinOn (fun m => ∑ i ∈ s, ‖g i - m‖) Set.univ m := by
  by_cases hs : s.Nonempty
  · let f := fun m : W ι => ∑ i ∈ s, ‖g i - m‖
    have hf : Continuous f := continuous_sum_distances s g
    have h_coercive := tendsto_sum_distances_cocompact s g hs
    let m0 : W ι := g hs.choose
    have hev : ∀ᶠ (x : W ι) in Filter.cocompact (W ι), f m0 ≤ f x :=
      h_coercive.eventually (Filter.eventually_ge_atTop (f m0))
    have ⟨m, hm⟩ := hf.exists_forall_le' m0 hev
    exact ⟨m, fun x _ => hm x⟩
  · use 0
    have h_empty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    intro x hx
    simp only [h_empty, Finset.sum_empty, le_refl] at *
    exact hx

/-- The Multivariate (Geometric) Median minimizes the sum of Euclidean distances. -/
noncomputable def geometricMedian {α : Type*} (s : Finset α) (g : α → W ι) : W ι :=
  if _ : s.Nonempty then
    Classical.choose (exists_isMin_on_finite_sum_norm s g)
  else
    0

/-- When `s` is nonempty, `geometricMedian` equals the chosen minimizer; used to apply
`Classical.choose_spec` in robustness proofs. -/
lemma geometricMedian_eq_choose {α : Type*} (s : Finset α) (g : α → W ι) (h : s.Nonempty) :
    geometricMedian s g = Classical.choose (exists_isMin_on_finite_sum_norm s g) := by
  unfold geometricMedian; rw [dif_pos h]

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

end LeanSharp
