/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Theory.Robustness.PacBayesMcAllesterBound

/-!
# McAllester PAC-Bayes Bound Verification Tests

These tests verify the type-correctness and wiring of the finite-sample McAllester
bound with confidence: the per-hypothesis Hoeffding moment bound, the posterior
exponential-moment bound, Markov's inequality, the optimal-`λ` arithmetic, and the
final probabilistic statement.
-/

namespace LeanSharp.Tests

open MeasureTheory ProbabilityTheory Real

variable {ι : Type*}
variable {Ω X : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  {PΩ : Measure Ω} [IsProbabilityMeasure PΩ]
  {D : Measure X} [IsProbabilityMeasure D]
  {n : ℕ} {Xᵢ : Fin n → Ω → X}
  {ℓ : W ι → X → ℝ} {L_D : W ι → ℝ}

/-- Test witness (per-hypothesis Hoeffding moment): the exponential moment of the
risk excess of a single hypothesis is bounded by `exp (l²n/8)`. -/
example (C : RiskExcessCtx PΩ D n Xᵢ ℓ L_D) (w : W ι) (l : ℝ) :
    (∫ ω : Ω, exp (l * ((n : ℝ) * (L_D w - empiricalRisk n Xᵢ ℓ w ω))) ∂PΩ) ≤
      exp (l ^ 2 * (n : ℝ) / 8) :=
  empiricalExcessMomentBound C w l

/-- Test witness (posterior exponential moment): the Fubini step bounds the
exponential moment of the posterior risk excess by `exp (KL + l²n/8)`. -/
example (C : RiskExcessCtx PΩ D n Xᵢ ℓ L_D) (P μ : Measure (W ι))
    [IsProbabilityMeasure P] [IsProbabilityMeasure μ] [SigmaFinite μ]
    (hPQ : P ≪ μ) (hL_D_int : Integrable L_D P) (hℓ_w_int : ∀ x, Integrable (fun w => ℓ w x) P)
    (hllr : Integrable (llr P μ) P) (hL_D_meas : Measurable L_D)
    (hℓ_prod : Measurable (fun p : W ι × X => ℓ p.1 p.2))
    (l : ℝ) (hl : 0 < l) :
    (∫ ω : Ω, exp (l * ((n : ℝ) * (∫ w, L_D w ∂P - ∫ w, empiricalRisk n Xᵢ ℓ w ω ∂P))) ∂PΩ) ≤
      exp ((klDivergenceW P μ).toReal + l ^ 2 * (n : ℝ) / 8) :=
  posteriorMomentBound C hPQ hL_D_int hℓ_w_int hllr hL_D_meas hℓ_prod l hl

/-- Test witness (Markov's inequality): a nonnegative variable with expectation at
most `c` exceeds `c/δ` with probability at most `δ`. -/
example {α : Type*} [MeasurableSpace α] (P : Measure α) [IsProbabilityMeasure P]
    (g : α → ℝ) (hg_int : Integrable g P) (hg_nonneg : ∀ᵐ ω ∂P, 0 ≤ g ω)
    (c : ℝ) (hc : 0 < c) (h_int : (∫ ω, g ω ∂P) ≤ c) (δ : ℝ) (hδ : 0 < δ) :
    P.real {ω | c / δ ≤ g ω} ≤ δ :=
  expMarkov hg_int hg_nonneg hc h_int hδ

/-- Test witness (optimal-`λ` arithmetic): at `λ = √(8a/n)`, the Markov bound
collapses to `√(a/(2n))`. -/
example (a n : ℝ) (ha : 0 < a) (hn : 0 < n) :
    a / (Real.sqrt (8 * a / n) * n) + Real.sqrt (8 * a / n) / 8 = Real.sqrt (a / (2 * n)) :=
  mcAllesterOptimization a n ha hn

/-- Test witness (McAllester bound with confidence): with probability at least `1 - δ`
over the sample, the population risk of a fixed posterior is at most its empirical
risk plus `√((KL + log(1/δ)) / (2n))`. -/
example (C : RiskExcessCtx PΩ D n Xᵢ ℓ L_D) (P μ : Measure (W ι))
    [IsProbabilityMeasure P] [IsProbabilityMeasure μ] [SigmaFinite μ]
    (hPQ : P ≪ μ) (hL_D_int : Integrable L_D P) (hℓ_w_int : ∀ x, Integrable (fun w => ℓ w x) P)
    (hllr : Integrable (llr P μ) P) (hL_D_meas : Measurable L_D)
    (hℓ_prod : Measurable (fun p : W ι × X => ℓ p.1 p.2))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hKL : 0 < (klDivergenceW P μ).toReal) :
    (1 : ℝ) - δ ≤
      PΩ.real {ω | (∫ w, L_D w ∂P) ≤
        (∫ w, empiricalRisk n Xᵢ ℓ w ω ∂P) +
          Real.sqrt (((klDivergenceW P μ).toReal + log (1 / δ)) / (2 * n))} :=
  pacBayesMcAllesterBound C P μ hPQ hL_D_int hℓ_w_int hllr hL_D_meas hℓ_prod δ hδ0 hδ1 hKL

end LeanSharp.Tests
