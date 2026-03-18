/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.Convergence.Bridges
import Mathlib.Probability.Martingale.Basic

/-!
# Robbins-Monro Martingale Update Model

This module introduces a concrete interface for modeling Robbins-Monro style
stochastic updates as a deterministic drift term plus martingale noise.

## Definitions

* `robbins_monro_partial_noise_sum`.
* `robbins_monro_update_martingale_model`.

## Theorems

This module provides the `robbins_monro_update_martingale_model` structure; users
should consume its fields directly (`h_update`, `h_noise_martingale`).
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- Partial-sum process of vector-valued Robbins-Monro noise increments. -/
noncomputable def robbins_monro_partial_noise_sum
    (ξ : ℕ → Ω → W ι) (t : ℕ) (ω : Ω) : W ι :=
  Finset.sum (Finset.range t) (fun k => ξ k ω)

/-- **Robbins-Monro Martingale Update Model**: packages a decomposition of the
stochastic update into deterministic drift plus martingale noise. This exists to
expose a reusable, theorem-backed interface for downstream convergence proofs
that explicitly track martingale structure of stochastic updates. -/
structure robbins_monro_update_martingale_model
    (f : W ι → ℝ)
    (w : ℕ → Ω → W ι)
    (η : ℕ → ℝ)
    (ℱ : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace) where
  /-- Per-step stochastic noise increment. -/
  ξ : ℕ → Ω → W ι
  /-- Martingale witness for the cumulative noise process. -/
  h_noise_martingale :
    Martingale (robbins_monro_partial_noise_sum ξ) ℱ ℙ
  /-- Update recursion expressed as drift plus noise increment. -/
  h_update :
    ∀ t, ∀ᵐ ω ∂ℙ,
      w (t + 1) ω =
        w t ω - η t • (gradient f (w t ω) + ξ t ω)

end LeanSharp
