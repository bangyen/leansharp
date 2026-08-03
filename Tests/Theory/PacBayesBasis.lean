/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Theory.Robustness.PacBayesBasis
import LeanSharp.Theory.Robustness.PacBayesHoeffding
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# PAC-Bayes Basis Verification Tests

These tests verify the type-correctness and basic properties of the PAC-Bayes basis.
-/

namespace LeanSharp.Tests

open MeasureTheory ProbabilityTheory Real

variable {ι : Type*} [Fintype ι]

/-- Test that KL divergence is defined and measurable space is found. -/
noncomputable example (P Q : Measure (W ι)) : klDivergenceW P Q = klDivergenceW P Q := rfl

/-- Test Gibbs measure construction. -/
noncomputable example (L : W ι → ℝ) (μ_prior : Measure (W ι)) (temp : ℝ) :
    Measure (W ι) := gibbsMeasure L μ_prior temp

/-- Test PAC-Bayes generalization bound predicate. -/
noncomputable example (L_D L_S : W ι → ℝ) (P μ_prior : Measure (W ι)) (n : ℕ) (δ : ℝ) :
    Prop := PacBayesGeneralizationBound L_D L_S P μ_prior n δ

/-- Test Donsker-Varadhan inequality predicate. -/
noncomputable example (P Q : Measure (W ι)) (f : W ι → ℝ) :
    Prop := DonskerVaradhanInequality P Q f

/-- Test the λ-parametrized PAC-Bayes-Hoeffding inequality wiring. -/
noncomputable example (L_D L_S : W ι → ℝ) (P μ : Measure (W ι)) (σ : ℝ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure μ] [SigmaFinite μ]
    (hPQ : P ≪ μ)
    (h_int_LD : Integrable L_D P)
    (h_int_LS : Integrable L_S P)
    (h_subg : ∀ l : ℝ, 0 < l →
      log (∫ w, exp (l * (L_D w - L_S w)) ∂μ) ≤ l ^ 2 * σ ^ 2 / 2)
    (h_int_exp : ∀ l : ℝ, Integrable (fun w => exp (l * (L_D w - L_S w))) μ)
    (hllr : Integrable (llr P μ) P) :
    ∀ l : ℝ, 0 < l →
      ∫ w, L_D w ∂P ≤ ∫ w, L_S w ∂P + (klDivergenceW P μ).toReal / l + l * σ ^ 2 / 2 :=
  pacBayesHoeffdingInequality L_D L_S P μ σ hPQ h_int_LD h_int_LS h_subg h_int_exp hllr

/-- Test the √KL PAC-Bayes bound wiring. -/
noncomputable example (L_D L_S : W ι → ℝ) (P μ : Measure (W ι)) (σ : ℝ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure μ] [SigmaFinite μ]
    (hPQ : P ≪ μ)
    (h_int_LD : Integrable L_D P)
    (h_int_LS : Integrable L_S P)
    (h_subg : ∀ l : ℝ, 0 < l →
      log (∫ w, exp (l * (L_D w - L_S w)) ∂μ) ≤ l ^ 2 * σ ^ 2 / 2)
    (h_int_exp : ∀ l : ℝ, Integrable (fun w => exp (l * (L_D w - L_S w))) μ)
    (hllr : Integrable (llr P μ) P)
    (hσ : 0 < σ) (hKL : 0 < (klDivergenceW P μ).toReal) :
    ∫ w, L_D w ∂P ≤ ∫ w, L_S w ∂P +
      Real.sqrt (2 * (klDivergenceW P μ).toReal * σ ^ 2) :=
  pacBayesBoundSqrtKL L_D L_S P μ σ hPQ h_int_LD h_int_LS h_subg h_int_exp hllr hσ hKL

/-- Test the bounded-loss Hoeffding bridge wiring: a zero-mean loss excess in `[0, 1]`
yields the sub-Gaussian MGF hypothesis with parameter `1/4`. -/
example (μ : Measure (W ι)) [IsProbabilityMeasure μ]
    (X : W ι → ℝ)
    (hm : AEMeasurable X μ)
    (hb : ∀ᵐ w ∂μ, X w ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∫ w, X w ∂μ = 0) (l : ℝ) :
    log (∫ w, exp (l * X w) ∂μ) ≤ l ^ 2 / 8 := by
  have hbnd := boundedLossSubGaussian (μ := μ) X hm hb hmean l
  have hnorm : (‖(1 : ℝ) - 0‖₊ : ℝ) / 2 = 1 / 2 := by norm_num
  rw [hnorm] at hbnd
  convert hbnd using 1
  ring

end LeanSharp.Tests
