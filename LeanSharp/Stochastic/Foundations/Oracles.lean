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

* `norm_tail_event`.
* `cauchy_probability_oracle`.
* `non_gaussian_probability_oracle`.
* `cauchy_probability_oracle_process`.
* `non_gaussian_probability_oracle_process`.

## Theorems

* `cauchy_probability_oracle_is_non_gaussian`.
* `cauchy_probability_oracle_process_is_non_gaussian`.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω]

/-- Tail event at radius `r` for a vector-valued random variable `ξ`.
This event abstraction exists so oracle contracts can share a stable event API
across different tail models. -/
def norm_tail_event (ξ : Ω → W ι) (r : ℝ) : Set Ω :=
  {ω | r ≤ ‖ξ ω‖}

/-- Cauchy-style probability oracle for vector-valued noise.
This contract exists to model heavy-tailed behavior through an inverse-radius tail
bound, which is the canonical asymptotic profile for Cauchy-like laws. -/
def cauchy_probability_oracle (ξ : Ω → W ι) : Prop :=
  ∃ γ : ℝ, 0 < γ ∧
    ∀ r : ℝ, 0 < r →
      (ℙ (norm_tail_event ξ r)).toReal ≤ γ / r

/-- Non-Gaussian probability oracle for vector-valued noise.
This contract exists to expose a broad polynomial-tail family (with exponent at
least one), so downstream theorems can reason about non-Gaussian noise without
committing to a single distribution. -/
def non_gaussian_probability_oracle (ξ : Ω → W ι) : Prop :=
  ∃ p : ℕ, ∃ C : ℝ, 1 ≤ p ∧ 0 < C ∧
    ∀ r : ℝ, 0 < r →
      (ℙ (norm_tail_event ξ r)).toReal ≤ C / r ^ p

/-- Process-level Cauchy oracle: every time index satisfies a Cauchy-style tail
certificate. This wrapper exists so sequence theorems can quantify over one
hypothesis instead of repeatedly threading per-time assumptions. -/
def cauchy_probability_oracle_process (ξ : ℕ → Ω → W ι) : Prop :=
  ∀ t : ℕ, cauchy_probability_oracle (ξ t)

/-- Process-level non-Gaussian oracle: every time index satisfies the polynomial-tail
oracle contract. This wrapper exists to align non-Gaussian tail assumptions with
Robbins-Monro style sequence interfaces. -/
def non_gaussian_probability_oracle_process (ξ : ℕ → Ω → W ι) : Prop :=
  ∀ t : ℕ, non_gaussian_probability_oracle (ξ t)

/-- Any Cauchy-style oracle is a valid instance of the broader non-Gaussian oracle.
This theorem exists to make distribution refinements compositional: specialized
heavy-tail assumptions can automatically feed into generic non-Gaussian interfaces. -/
theorem cauchy_probability_oracle_is_non_gaussian
    (ξ : Ω → W ι) (h_cauchy : cauchy_probability_oracle ξ) :
    non_gaussian_probability_oracle ξ := by
  rcases h_cauchy with ⟨γ, hγ_pos, h_tail⟩
  refine ⟨1, γ, le_rfl, hγ_pos, ?_⟩
  intro r hr
  simpa only [pow_one] using h_tail r hr

/-- Process-level lifting of `cauchy_probability_oracle_is_non_gaussian`.
This theorem exists so time-indexed Cauchy-tail assumptions can be consumed by
interfaces that only require non-Gaussian polynomial-tail control. -/
theorem cauchy_probability_oracle_process_is_non_gaussian
    (ξ : ℕ → Ω → W ι)
    (h_cauchy : cauchy_probability_oracle_process ξ) :
    non_gaussian_probability_oracle_process ξ := by
  intro t
  exact cauchy_probability_oracle_is_non_gaussian (ξ t) (h_cauchy t)

end LeanSharp
