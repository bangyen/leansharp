/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Landscape
import LeanSharp.Layers.Basic.Linear
import LeanSharp.Theory.Robustness.BreakdownPoint
import LeanSharp.Theory.Robustness.ComparisonResults
import LeanSharp.Theory.Robustness.LinearPacBayes
import LeanSharp.Theory.Robustness.LocalPacBayes
import LeanSharp.Theory.Robustness.PacBayesMcAllesterBound

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

/-- Test witness (threshold limit): for nonpositive Z thresholds, every coordinate
passes the mask test, so the filtered mean equals the ordinary empirical mean. -/
example (s : Finset ℕ) (g : ℕ → W ι) {z : ℝ} (hz : z ≤ 0) :
    zFilteredEmpiricalMean s g z = empiricalMean s g :=
  z_filtered_empirical_mean_eq_empirical_mean_of_nonpos_threshold s g hz

/-- Test witness (majority safety): both the median and filtered mean stay bounded
when a strict majority of points are fixed and outliers are bounded. -/
example (s s_fixed : Finset ℕ) (g : ℕ → W ι) (h_sub : s_fixed ⊆ s)
    (h_maj : 2 * s_fixed.card > s.card) (z R_fixed R_out : ℝ) (hs : s.Nonempty)
    (h_fixed_bound : ∀ i ∈ s_fixed, ‖g i‖ ≤ R_fixed) :
    ∃ R_med : ℝ, ∀ g' : ℕ → W ι, (∀ i ∈ s_fixed, g' i = g i) →
      (∀ i ∈ s \ s_fixed, ‖g' i‖ ≤ R_out) →
      ‖geometricMedian s g'‖ ≤ R_med ∧ ‖zFilteredEmpiricalMean s g' z‖ ≤ max R_fixed R_out :=
  median_and_zfiltered_mean_bounded_subset s g s_fixed h_sub h_maj z R_fixed R_out hs h_fixed_bound

/-- Test witness (localized PAC-Bayes): under a sub-Gaussian loss excess, the
localized Gibbs posterior over a `StabilityCertificate` region is a probability
measure and the localized PAC-Bayes inequality holds. -/
example (L_D L_S : W ι → ℝ) (μ_prior : Measure (W ι)) (σ : ℝ)
    {ι' : Type*} [Fintype ι'] (cert : StabilityCertificate (W ι) (W ι'))
    [IsProbabilityMeasure μ_prior] [SigmaFinite μ_prior]
    (h_S_pos : μ_prior cert.S > 0)
    (h_int_LS : Integrable (fun w => exp (-1 * L_S w)) (μ_prior.restrict cert.S))
    (h_int_LD : Integrable L_D (localizedPosterior L_S μ_prior cert))
    (h_int_LS_post : Integrable L_S (localizedPosterior L_S μ_prior cert))
    (h_subg : ∀ l : ℝ, 0 < l →
      log (∫ w, exp (l * (L_D w - L_S w)) ∂μ_prior) ≤ l ^ 2 * σ ^ 2 / 2)
    (h_int_exp : ∀ l : ℝ, Integrable (fun w => exp (l * (L_D w - L_S w))) μ_prior)
    (hllr : Integrable (llr (localizedPosterior L_S μ_prior cert) μ_prior)
      (localizedPosterior L_S μ_prior cert))
    (hσ : 0 < σ) (hKL : 0 < (klDivergenceW (localizedPosterior L_S μ_prior cert) μ_prior).toReal) :
    IsProbabilityMeasure (localizedPosterior L_S μ_prior cert) ∧
    ∫ w, L_D w ∂(localizedPosterior L_S μ_prior cert) ≤
      ∫ w, L_S w ∂(localizedPosterior L_S μ_prior cert) +
        Real.sqrt (2 * (klDivergenceW (localizedPosterior L_S μ_prior cert) μ_prior).toReal
          * σ ^ 2) :=
  stabilityPacBayesBound_provability L_D L_S μ_prior σ cert h_S_pos h_int_LS h_int_LD
    h_int_LS_post h_subg h_int_exp hllr hσ hKL

/-- Test witness (linear-layer instantiation): the linear layer certificate's
domain is `Set.univ`, so any probability prior has positive mass there. -/
example {ι_in ι_out : Type} [Fintype ι_in] [Fintype ι_out]
    (μ_prior : Measure (W ι_in)) [IsProbabilityMeasure μ_prior]
    (w : W (LinearParam ι_in ι_out)) :
    μ_prior (linearCertificate w).S > 0 :=
  linearCertificate_prior_pos μ_prior w

end LeanSharp.Tests
