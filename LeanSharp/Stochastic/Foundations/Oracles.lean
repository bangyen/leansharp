/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Landscape
import Mathlib.Probability.Notation

/-!
# Probability Oracle Interfaces

This module introduces reusable probability-oracle interfaces for stochastic noise
models. It exists to provide explicit contracts for heavy-tailed regimes (including
Cauchy-style tails) without hardcoding a single distribution family into convergence
theorems.

## Definitions

* `normTailEvent`.
* `CauchyProbabilityOracle`.
* `NonGaussianProbabilityOracle`.
* `CauchyProbabilityOracleProcess`.
* `NonGaussianProbabilityOracleProcess`.
* `AlphaStableProbabilityOracle`.
* `AlphaStableProbabilityOracleProcess`.

## Theorems

* `cauchy_probability_oracle_is_non_gaussian`.
* `alpha_stable_is_non_gaussian`.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω]

/-- Tail event at radius `r` for a vector-valued random variable `ξ`.
This event abstraction exists so oracle contracts can share a stable event API
across different tail models. -/
def normTailEvent (ξ : Ω → W ι) (r : ℝ) : Set Ω :=
  {ω | r ≤ ‖ξ ω‖}

/-- Cauchy-style probability oracle for vector-valued noise.
This contract exists to model heavy-tailed behavior through an inverse-radius tail
bound, which is the canonical asymptotic profile for Cauchy-like laws. -/
def CauchyProbabilityOracle (ξ : Ω → W ι) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧
    ∀ r : ℝ, 0 < r →
      (ℙ (normTailEvent ξ r)).toReal ≤ γ / r

/-- Non-Gaussian probability oracle for vector-valued noise.
This contract exists to expose a broad polynomial-tail family (with exponent at
least one), so downstream theorems can reason about non-Gaussian noise without
committing to a single distribution. -/
def NonGaussianProbabilityOracle (ξ : Ω → W ι) : Prop :=
  ∃ p : ℕ, ∃ C : ℝ, 1 ≤ p ∧ 0 < C ∧
    ∀ r : ℝ, 0 < r →
      (ℙ (normTailEvent ξ r)).toReal ≤ C / r ^ p

/-- Process-level Cauchy oracle: every time index satisfies a Cauchy-style tail
certificate. This wrapper exists so sequence theorems can quantify over one
hypothesis instead of repeatedly threading per-time assumptions. -/
def CauchyProbabilityOracleProcess (ξ : ℕ → Ω → W ι) : Prop :=
  ∀ t : ℕ, CauchyProbabilityOracle (ξ t)

/-- Process-level non-Gaussian oracle: every time index satisfies the polynomial-tail
oracle contract. This wrapper exists to align non-Gaussian tail assumptions with
Robbins-Monro style sequence interfaces. -/
def NonGaussianProbabilityOracleProcess (ξ : ℕ → Ω → W ι) : Prop :=
  ∀ t : ℕ, NonGaussianProbabilityOracle (ξ t)

/-- Alpha-stable probability oracle for vector-valued noise.
This contract models heavy-tailed behavior typical of alpha-stable distributions
with exponent `α ∈ (0, 2]`. -/
def AlphaStableProbabilityOracle (ξ : Ω → W ι) (α : ℝ) : Prop :=
  0 < α ∧ α ≤ 2 ∧ ∃ C : ℝ, 0 < C ∧
    ∀ r : ℝ, 0 < r →
      (ℙ (normTailEvent ξ r)).toReal ≤ C / r ^ α

/-- Process-level alpha-stable oracle: every time index satisfies an alpha-stable
tail certificate for a fixed `α`. -/
def AlphaStableProbabilityOracleProcess (ξ : ℕ → Ω → W ι) (α : ℝ) : Prop :=
  ∀ t : ℕ, AlphaStableProbabilityOracle (ξ t) α

/-- Any alpha-stable oracle with α ≥ 1 is a valid instance of the non-Gaussian oracle. -/
theorem alpha_stable_is_non_gaussian {α : ℝ}
    (h_alpha_ge_one : 1 ≤ α) (ξ : Ω → W ι) (h_stable : AlphaStableProbabilityOracle ξ α)
    [IsProbabilityMeasure (volume : Measure Ω)] :
    NonGaussianProbabilityOracle ξ := by
  rcases h_stable with ⟨-, -, C, hC_pos, h_tail⟩
  refine ⟨1, max C 1, le_rfl, lt_max_iff.mpr (Or.inr zero_lt_one), ?_⟩
  intro r hr
  by_cases h_r_ge_1 : 1 ≤ r
  · have h_pow_le : r ^ (1 : ℝ) ≤ r ^ α :=
      Real.rpow_le_rpow_of_exponent_le h_r_ge_1 h_alpha_ge_one
    have h_inv_le : (r ^ α)⁻¹ ≤ (r ^ (1 : ℝ))⁻¹ :=
      (inv_le_inv₀ (Real.rpow_pos_of_pos hr _) (Real.rpow_pos_of_pos hr _)).mpr h_pow_le
    have h_C_inv_le : C * (r ^ α)⁻¹ ≤ C * (r ^ (1 : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_left h_inv_le (le_of_lt hC_pos)
    have h_tail_le : (ℙ (normTailEvent ξ r)).toReal ≤ C * (r ^ (1 : ℝ))⁻¹ :=
      le_trans (h_tail r hr) h_C_inv_le
    have h_max : C * (r ^ (1 : ℝ))⁻¹ ≤ (max C 1) / r ^ (1 : ℕ) := by
      rw [Real.rpow_one, pow_one, div_eq_mul_one_div, one_div]
      exact mul_le_mul_of_nonneg_right (le_max_left C 1) (by positivity)
    exact le_trans h_tail_le h_max
  · have h_r_lt_1 : r < 1 := not_le.mp h_r_ge_1
    have h_prob_le_one : (ℙ (normTailEvent ξ r)).toReal ≤ 1 := by
      have h1 : ℙ (normTailEvent ξ r) ≤ ENNReal.ofReal 1 := by
        rw [ENNReal.ofReal_one]
        exact prob_le_one
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one h1
    have h_inv_gt_one : 1 ≤ 1 / r := by exact one_le_div hr |>.mpr (le_of_lt h_r_lt_1)
    have h_max : 1 ≤ (max C 1) / r ^ (1 : ℕ) := by
      rw [pow_one]
      calc
        1 ≤ 1 / r := h_inv_gt_one
        _ ≤ (max C 1) / r := by exact div_le_div_of_nonneg_right (le_max_right C 1) (le_of_lt hr)
    exact le_trans h_prob_le_one h_max

/-- Any Cauchy-style oracle is a valid instance of the broader non-Gaussian oracle.
This theorem exists to make distribution refinements compositional: specialized
heavy-tail assumptions can automatically feed into generic non-Gaussian interfaces. -/
theorem cauchy_probability_oracle_is_non_gaussian
    (ξ : Ω → W ι) (h_cauchy : CauchyProbabilityOracle ξ) :
    NonGaussianProbabilityOracle ξ := by
  rcases h_cauchy with ⟨γ, hγ_pos, h_tail⟩
  refine ⟨1, γ, le_rfl, hγ_pos, ?_⟩
  intro r hr
  simpa only [pow_one] using h_tail r hr

end LeanSharp
