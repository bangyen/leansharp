/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Stats
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Sqrt

/-!
# Statistical Norm Bounds

This module establishes that the empirical mean and standard deviation of a
vector are bounded by its norm. These are the finite-dimensional handles used
by the infinite-width stability theorems in `Theory/InfiniteLimit`.

## Main Theorems

* `abs_vectorMean_le_norm`: $|\mathrm{mean}(g)| \le \|g\|$.
* `vectorStd_le_norm`: $\mathrm{std}(g) \le \|g\|$.
-/

namespace LeanSharp

open BigOperators

variable {ι : Type*} [Fintype ι]

/-- **Mean is bounded by the norm**: $|\mathrm{mean}(g)| \le \|g\|$. By the
Cauchy-Schwarz inequality, $|\sum_i g_i| \le \sqrt{n}\|g\|$, and dividing by $n$
gives $|\mathrm{mean}(g)| \le \|g\|/\sqrt{n} \le \|g\|$. -/
lemma abs_vectorMean_le_norm (g : W ι) : |vectorMean g| ≤ ‖g‖ := by
  unfold vectorMean
  rw [EuclideanSpace.norm_eq]
  simp only [WithLp.equiv_apply, Real.norm_eq_abs, sq_abs]
  apply Real.abs_le_sqrt
  have h_card_nonneg : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  have h_cs : (∑ i, (WithLp.equiv 2 (ι → ℝ) g) i) ^ 2 ≤
      (Fintype.card ι : ℝ) * ∑ i, ((WithLp.equiv 2 (ι → ℝ) g) i) ^ 2 := by
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq (R := ℝ) (Finset.univ : Finset ι)
      (fun i => |(WithLp.equiv 2 (ι → ℝ) g) i|) (fun _ => (1 : ℝ))
    have h2 : (∑ i, |(WithLp.equiv 2 (ι → ℝ) g) i|) ^ 2 ≤
        (∑ i, ((WithLp.equiv 2 (ι → ℝ) g) i) ^ 2) * (Fintype.card ι : ℝ) := by
      simpa only [sq_abs, mul_one, one_pow, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul] using h1
    have htri : |(∑ i, (WithLp.equiv 2 (ι → ℝ) g) i)| ≤
        ∑ i, |(WithLp.equiv 2 (ι → ℝ) g) i| := Finset.abs_sum_le_sum_abs _ _
    have hs2 : (∑ i, (WithLp.equiv 2 (ι → ℝ) g) i) ^ 2 ≤
        (∑ i, |(WithLp.equiv 2 (ι → ℝ) g) i|) ^ 2 := by
      refine sq_le_sq.mpr ?_
      calc
        |(∑ i, (WithLp.equiv 2 (ι → ℝ) g) i)| ≤
            ∑ i, |(WithLp.equiv 2 (ι → ℝ) g) i| := htri
        _ = |(∑ i, |(WithLp.equiv 2 (ι → ℝ) g) i|)| := by
          rw [abs_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _))]
    simpa only [mul_comm] using hs2.trans h2
  have hstep1 : ((∑ i, (WithLp.equiv 2 (ι → ℝ) g) i) / (Fintype.card ι : ℝ)) ^ 2 ≤
      ((Fintype.card ι : ℝ) * ∑ i, ((WithLp.equiv 2 (ι → ℝ) g) i) ^ 2) /
        (Fintype.card ι : ℝ) ^ 2 := by
    rw [div_pow]
    exact div_le_div_of_nonneg_right h_cs (sq_nonneg _)
  have hstep2 : ((Fintype.card ι : ℝ) * ∑ i, ((WithLp.equiv 2 (ι → ℝ) g) i) ^ 2) /
      (Fintype.card ι : ℝ) ^ 2 ≤ ∑ i, ((WithLp.equiv 2 (ι → ℝ) g) i) ^ 2 := by
    by_cases hn : (Fintype.card ι : ℝ) = 0
    · have hq : 0 ≤ ∑ i, ((WithLp.equiv 2 (ι → ℝ) g) i) ^ 2 :=
        Finset.sum_nonneg (fun i _ => sq_nonneg _)
      simpa only [hn, div_zero, pow_two, mul_zero] using hq
    · have hq : 0 ≤ ∑ i, ((WithLp.equiv 2 (ι → ℝ) g) i) ^ 2 :=
        Finset.sum_nonneg (fun i _ => sq_nonneg _)
      have h1n : 1 ≤ (Fintype.card ι : ℝ) :=
        (Fintype.card ι).one_le_cast_iff_ne_zero.mpr (by exact_mod_cast hn)
      calc
        ((Fintype.card ι : ℝ) * ∑ i, ((WithLp.equiv 2 (ι → ℝ) g) i) ^ 2) /
            (Fintype.card ι : ℝ) ^ 2
            = (∑ i, ((WithLp.equiv 2 (ι → ℝ) g) i) ^ 2) / (Fintype.card ι : ℝ) := by
              field_simp [hn]
        _ ≤ ∑ i, ((WithLp.equiv 2 (ι → ℝ) g) i) ^ 2 := div_le_self hq h1n
  exact hstep1.trans hstep2

/-- **Standard deviation is bounded by the norm**: $\mathrm{std}(g) \le \|g\|$,
since the variance of a vector is at most its mean squared norm (the mean
minimizes the sum of squared deviations). -/
lemma vectorStd_le_norm (g : W ι) : vectorStd g ≤ ‖g‖ := by
  unfold vectorStd vectorVariance vectorMean
  rw [EuclideanSpace.norm_eq]
  simp only [WithLp.equiv_apply, Real.norm_eq_abs, sq_abs]
  let m : ℝ := (∑ j, (WithLp.equiv 2 (ι → ℝ) g) j) / (Fintype.card ι : ℝ)
  have hm : m = (∑ j, (WithLp.equiv 2 (ι → ℝ) g) j) / (Fintype.card ι : ℝ) := rfl
  have h_card_nonneg : 0 ≤ (Fintype.card ι : ℝ) := Nat.cast_nonneg _
  apply Real.sqrt_le_sqrt
  change (∑ i, ((WithLp.equiv 2 (ι → ℝ) g) i - m)^2) / (Fintype.card ι : ℝ) ≤
    ∑ i, ((WithLp.equiv 2 (ι → ℝ) g) i)^2
  by_cases hn : (Fintype.card ι : ℝ) = 0
  · have hq : 0 ≤ ∑ i, ((WithLp.equiv 2 (ι → ℝ) g) i)^2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    simpa only [hn, div_zero] using hq
  · have hnsum : (Fintype.card ι : ℝ) * m = ∑ i, (WithLp.equiv 2 (ι → ℝ) g) i := by
      rw [hm, mul_comm, div_mul_cancel₀ _ hn]
    have h_exp : ∑ i, ((WithLp.equiv 2 (ι → ℝ) g) i - m)^2 =
        ∑ i, (((WithLp.equiv 2 (ι → ℝ) g) i)^2 - 2*(WithLp.equiv 2 (ι → ℝ) g) i*m + m^2) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    have h_dist : ∑ i, (((WithLp.equiv 2 (ι → ℝ) g) i)^2 - 2*(WithLp.equiv 2 (ι → ℝ) g) i*m + m^2)
        = (∑ i, ((WithLp.equiv 2 (ι → ℝ) g) i)^2) - 2*m*(∑ i, (WithLp.equiv 2 (ι → ℝ) g) i)
            + (Fintype.card ι : ℝ)*m^2 := by
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      congr 1
      · rw [← Finset.sum_mul, ← Finset.mul_sum]
        ring
      · rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hvar_id : ∑ i, ((WithLp.equiv 2 (ι → ℝ) g) i - m)^2 =
        (∑ i, ((WithLp.equiv 2 (ι → ℝ) g) i)^2) - (Fintype.card ι : ℝ)*m^2 := by
      rw [h_exp, h_dist]
      rw [← hnsum]
      ring
    have hvar_le : ∑ i, ((WithLp.equiv 2 (ι → ℝ) g) i - m)^2 ≤
        ∑ i, ((WithLp.equiv 2 (ι → ℝ) g) i)^2 := by
      rw [hvar_id]
      exact sub_le_self _ (mul_nonneg h_card_nonneg (sq_nonneg m))
    have hdiv : (∑ i, ((WithLp.equiv 2 (ι → ℝ) g) i - m)^2) / (Fintype.card ι : ℝ) ≤
        (∑ i, ((WithLp.equiv 2 (ι → ℝ) g) i)^2) / (Fintype.card ι : ℝ) :=
      div_le_div_of_nonneg_right hvar_le h_card_nonneg
    have hq : 0 ≤ ∑ i, ((WithLp.equiv 2 (ι → ℝ) g) i)^2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have h1n : 1 ≤ (Fintype.card ι : ℝ) :=
      (Fintype.card ι).one_le_cast_iff_ne_zero.mpr (by exact_mod_cast hn)
    exact hdiv.trans (div_le_self hq h1n)

end LeanSharp
