/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Landscape
import LeanSharp.Theory.Robustness.BreakdownPoint
import LeanSharp.Theory.Robustness.ComparisonResults
import LeanSharp.Theory.Robustness.FilterBias
import LeanSharp.Theory.Robustness.FilteredMeanProps.Basic
import LeanSharp.Theory.Robustness.SensitivityBounds

/-!
# Robustness Tests

This module verifies the breakdown point theorems for the empirical mean
and the geometric median, as well as high-level comparison results.

## Examples
-/

namespace LeanSharp.Tests

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Test witness: for a non-empty dataset, the mean breakdown point is bounded by 1/n. -/
example [Nonempty ι] (s : Finset ℕ) (g : ℕ → W ι) (hs : s.Nonempty) :
    finiteSampleBreakdownPoint s g (empiricalMean s) ≤ 1 / (s.card : ℝ) :=
  mean_breakdown_point_zero s g hs

/-- Test witness: for any dataset, the geometric median has a breakdown point of at least 1/2. -/
example (s : Finset ℕ) (g : ℕ → W ι) (hs : s.Nonempty) :
    finiteSampleBreakdownPoint s g (geometricMedian s) ≥ 1 / 2 :=
  geometric_median_breakdown_point_ge_half s g hs

/-- Test witness (majority separation): for a single movable point and a strict
majority of fixed points, the empirical mean can be made arbitrarily large
while the geometric median stays bounded. -/
example [Nonempty ι] (s : Finset ℕ) (g : ℕ → W ι) (i0 : ℕ) (hi0 : i0 ∈ s)
    (h_maj : 2 * (s.erase i0).card > s.card) (C : ℝ) :
    (∃ R : ℝ, ∀ g' : ℕ → W ι, (∀ i ≠ i0, g' i = g i) → ‖geometricMedian s g'‖ ≤ R) ∧
    (∃ g' : ℕ → W ι, (∀ i ≠ i0, g' i = g i) ∧ ‖empiricalMean s g'‖ > C) :=
  median_bounded_mean_unbounded_one_outlier_of_majority s g i0 hi0 h_maj C

/-- Test witness (threshold limit): for a strictly negative Z threshold and a
non-constant gradient, the filter zeroes every component. -/
example (g : W ι) {z : ℝ} (hz : z < 0) (hσ : vectorStd g ≠ 0) :
    filteredGradient g z = 0 :=
  filtered_gradient_eq_zero_of_neg_threshold g hz hσ

/-- Test witness (majority safety): both the median and filtered mean stay bounded
when a strict majority of points are fixed and outliers are bounded. -/
example (s s_fixed : Finset ℕ) (g : ℕ → W ι) (h_sub : s_fixed ⊆ s)
    (h_maj : 2 * s_fixed.card > s.card) (z R_fixed R_out : ℝ) (hs : s.Nonempty)
    (h_fixed_bound : ∀ i ∈ s_fixed, ‖g i‖ ≤ R_fixed) :
    ∃ R_med : ℝ, ∀ g' : ℕ → W ι, (∀ i ∈ s_fixed, g' i = g i) →
      (∀ i ∈ s \ s_fixed, ‖g' i‖ ≤ R_out) →
      ‖geometricMedian s g'‖ ≤ R_med ∧ ‖zFilteredEmpiricalMean s g' z‖ ≤ max R_fixed R_out :=
  median_and_zfiltered_mean_bounded_subset s g s_fixed h_sub h_maj z R_fixed R_out hs h_fixed_bound

/-- Test witness (mask is even): the Z-score mask is invariant under negation. -/
example (g : W ι) (z : ℝ) :
    zScoreMask (-g) z = zScoreMask g z :=
  zScoreMask_neg g z

/-- Test witness (filtered gradient is odd): filtering the negation of a gradient is
the negation of the filtered gradient. -/
example (g : W ι) (z : ℝ) :
    filteredGradient (-g) z = -filteredGradient g z :=
  filteredGradient_neg g z

/-- Test witness (filter bias): filtering noise from a symmetric law is unbiased —
the expected filtered gradient is zero. -/
example (D : Measure (W ι)) (z : ℝ)
    (h_sym : D.map (fun g => -g) = D)
    (h_int : Integrable (fun g => filteredGradient g z) D) :
    (∫ g, filteredGradient g z ∂D) = 0 :=
  filtered_noise_mean_zero D z h_sym h_int

/-- Test witness (sample filter bias): the filtered empirical mean of an i.i.d. sample
from a symmetric law has zero expectation. -/
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (s : Finset ℕ) (η : ℕ → Ω → W ι) (z : ℝ)
    (D : Measure (W ι)) (h_sym : D.map (fun g => -g) = D)
    (h_law : ∀ i ∈ s, HasLaw (η i) D P)
    (h_int : ∀ i ∈ s, Integrable (fun g => filteredGradient g z) D) :
    (∫ ω, zFilteredEmpiricalMean s (fun i => η i ω) z ∂P) = 0 :=
  zFilteredEmpiricalMean_symmetric_noise_mean_zero s η z D h_sym h_law h_int

/-- Test witness (sample satisfiability): a concrete `RobustSample` exists — three
points with a strict-majority fixed subset and bounded fixed points — so the
robustness structure's hypotheses are non-vacuous. -/
example :
    ∃ S : RobustSample (Fin 3) (Fin 2), 2 * S.s_fixed.card > S.s.card := by
  let u : W (Fin 2) := (WithLp.equiv 2 (Fin 2 → ℝ)).symm (fun _ => (1 : ℝ))
  let S : RobustSample (Fin 3) (Fin 2) := {
    s := Finset.univ
    g := fun _ => u
    s_fixed := ({0, 1} : Finset (Fin 3))
    h_sub := by intro i hi; exact Finset.mem_univ i
    R_fixed := ‖u‖
    R_out := 0
    h_fixed_bound := by intro i hi; exact le_rfl
  }
  refine ⟨S, ?_⟩
  norm_num [S, Finset.card_univ]

/-- Test witness (`SignalNoiseModel` satisfiability): the zero-noise model discharges
both structure fields — `h_mean` (the noise integrates to zero) and `h_int`
(integrability) — so the signal-noise interface used by the alignment bridge is
non-vacuous. Its observed gradient is exactly the ground truth, and it meets the
variance bound at `σsq = 0`. -/
example {Ω : Type*} [MeasureSpace Ω] (g : W ι) :
    ∃ m : SignalNoiseModel ι Ω, m.g_true = g
      ∧ (∀ ω, m.observed ω = g) ∧ NoiseVarianceBound m 0 := by
  refine ⟨{ g_true := g
            noise := fun _ => 0
            h_mean := by simp only [integral_zero]
            h_int := integrable_zero _ _ _ }, rfl, ?_, ?_⟩
  · intro ω
    simp only [SignalNoiseModel.observed, add_zero]
  · intro i
    simp only [WithLp.ofLp_zero, Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, integral_zero, le_refl]

end LeanSharp.Tests
