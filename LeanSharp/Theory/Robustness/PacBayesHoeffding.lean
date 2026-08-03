/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Theory.Robustness.PacBayesBasis
import Mathlib.Probability.Moments.SubGaussian

/-!
# PAC-Bayes-Hoeffding Bounds

This module derives the classical PAC-Bayes population-risk bounds from the
Donsker-Varadhan variational inequality under a sub-Gaussian (Hoeffding-style)
moment-generating-function assumption on the loss excess.

## Main Theorems

* `pacBayesHoeffdingInequality`: The λ-parametrized PAC-Bayes bound from DV.
* `pacBayesBoundSqrtKL`: The √KL PAC-Bayes bound at the optimal λ.
* `boundedLossSubGaussian`: Hoeffding's bridge from bounded losses to the
  sub-Gaussian MGF hypothesis, making the PAC-Bayes bound applicable to $[0,1]$-losses.
-/

namespace LeanSharp

open MeasureTheory ProbabilityTheory Real

variable {ι : Type*} [Fintype ι]

omit [Fintype ι] in
/-- **PAC-Bayes-Hoeffding Inequality**: For a posterior `P` and prior `μ` over the
parameter space, if the loss excess `L_D - L_S` has a sub-Gaussian moment-generating
function with parameter `σ²` under the prior, then the population risk of the posterior
is bounded by its empirical risk plus a complexity term.

    **Proof**: Apply `DonskerVaradhanInequality` to `f = l · (L_D - L_S)`, bound the
    exponential moment by the sub-Gaussian hypothesis, and divide by `l > 0`. This
    derives the classical PAC-Bayes bound from DV instead of assuming it. -/
theorem pacBayesHoeffdingInequality (L_D L_S : W ι → ℝ) (P μ : Measure (W ι)) (σ : ℝ)
    [IsProbabilityMeasure P] [IsProbabilityMeasure μ] [SigmaFinite μ]
    (hPQ : P ≪ μ)
    (h_int_LD : Integrable L_D P)
    (h_int_LS : Integrable L_S P)
    (h_subg : ∀ l : ℝ, 0 < l →
      log (∫ w, exp (l * (L_D w - L_S w)) ∂μ) ≤ l ^ 2 * σ ^ 2 / 2)
    (h_int_exp : ∀ l : ℝ, Integrable (fun w => exp (l * (L_D w - L_S w))) μ)
    (hllr : Integrable (llr P μ) P) :
    ∀ l : ℝ, 0 < l →
      ∫ w, L_D w ∂P ≤ ∫ w, L_S w ∂P + (klDivergenceW P μ).toReal / l + l * σ ^ 2 / 2 := by
  intro l hl
  have hDV := DonskerVaradhanInequality_holds P μ (fun w => l * (L_D w - L_S w))
    hPQ (by
      apply (h_int_LD.sub h_int_LS).const_mul
    ) (h_int_exp l) hllr
  have hdv : ∫ w, l * (L_D w - L_S w) ∂P ≤
      log (∫ w, exp (l * (L_D w - L_S w)) ∂μ) + (klDivergenceW P μ).toReal := hDV.2.2
  have hlin : ∫ w, l * (L_D w - L_S w) ∂P = l * (∫ w, L_D w ∂P - ∫ w, L_S w ∂P) := by
    rw [integral_const_mul]
    rw [integral_sub h_int_LD h_int_LS]
  have hlog : log (∫ w, exp (l * (L_D w - L_S w)) ∂μ) ≤ l ^ 2 * σ ^ 2 / 2 :=
    h_subg l hl
  have hbound : l * (∫ w, L_D w ∂P - ∫ w, L_S w ∂P) ≤
      l ^ 2 * σ ^ 2 / 2 + (klDivergenceW P μ).toReal := by
    rw [hlin] at hdv
    linarith
  have hrewrite : l * (l * σ ^ 2 / 2 + (klDivergenceW P μ).toReal / l) =
      l ^ 2 * σ ^ 2 / 2 + (klDivergenceW P μ).toReal := by
    field_simp [hl.ne']
  have hdiv : ∫ w, L_D w ∂P - ∫ w, L_S w ∂P ≤
      l * σ ^ 2 / 2 + (klDivergenceW P μ).toReal / l := by
    have hgoal_mul : l * (∫ w, L_D w ∂P - ∫ w, L_S w ∂P) ≤
        l * (l * σ ^ 2 / 2 + (klDivergenceW P μ).toReal / l) := by
      rw [hrewrite]
      exact hbound
    exact le_of_mul_le_mul_left hgoal_mul hl
  linarith

omit [Fintype ι] in
/-- **Square-root KL PAC-Bayes bound**: Optimizing the parameter `l` in
`pacBayesHoeffdingInequality` yields the classical √KL bound: the population risk of
the posterior is bounded by its empirical risk plus `sqrt(2 · KL(P ‖ μ) · σ²)`. -/
theorem pacBayesBoundSqrtKL (L_D L_S : W ι → ℝ) (P μ : Measure (W ι)) (σ : ℝ)
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
      Real.sqrt (2 * (klDivergenceW P μ).toReal * σ ^ 2) := by
  let lam0 : ℝ := Real.sqrt (2 * (klDivergenceW P μ).toReal / σ ^ 2)
  have hlam0 : 0 < lam0 := by
    dsimp only [lam0]
    exact Real.sqrt_pos.mpr (by positivity)
  have hbd := pacBayesHoeffdingInequality L_D L_S P μ σ hPQ h_int_LD h_int_LS h_subg
    h_int_exp hllr lam0 hlam0
  have hopt : (klDivergenceW P μ).toReal / lam0 + lam0 * σ ^ 2 / 2 =
      Real.sqrt (2 * (klDivergenceW P μ).toReal * σ ^ 2) := by
    have hσ2_pos : 0 < σ ^ 2 := sq_pos_of_pos hσ
    have hsq : lam0 ^ 2 = 2 * (klDivergenceW P μ).toReal / σ ^ 2 := by
      dsimp only [lam0]
      rw [Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) hKL.le) (sq_nonneg σ))]
    have hKL_eq : (klDivergenceW P μ).toReal = lam0 ^ 2 * σ ^ 2 / 2 := by
      have hσ2_ne : σ ^ 2 ≠ 0 := hσ2_pos.ne'
      have hmul : lam0 ^ 2 * σ ^ 2 = 2 * (klDivergenceW P μ).toReal := by
        rw [hsq]
        exact div_mul_cancel₀ (2 * (klDivergenceW P μ).toReal) hσ2_ne
      nlinarith
    have hmid : (klDivergenceW P μ).toReal / lam0 + lam0 * σ ^ 2 / 2 = lam0 * σ ^ 2 := by
      calc
        (klDivergenceW P μ).toReal / lam0 + lam0 * σ ^ 2 / 2
            = (lam0 ^ 2 * σ ^ 2 / 2) / lam0 + lam0 * σ ^ 2 / 2 := by rw [hKL_eq]
        _ = lam0 * σ ^ 2 := by
          field_simp [hlam0.ne']
          ring
    have hsq2 : (lam0 * σ ^ 2) ^ 2 = 2 * (klDivergenceW P μ).toReal * σ ^ 2 := by
      rw [hKL_eq]
      ring
    calc
      (klDivergenceW P μ).toReal / lam0 + lam0 * σ ^ 2 / 2 = lam0 * σ ^ 2 := hmid
      _ = Real.sqrt (2 * (klDivergenceW P μ).toReal * σ ^ 2) := by
        rw [← hsq2]
        rw [Real.sqrt_sq_eq_abs]
        rw [abs_of_nonneg]
        positivity
  linarith

omit [Fintype ι] in
/-- **Bounded-Loss Sub-Gaussian Bridge (Hoeffding)**: If the loss excess `X = L_D - L_S`
is almost surely in the interval `[a, b]` under the prior `μ` and has zero mean, then it
satisfies the sub-Gaussian moment-generating-function hypothesis required by
`pacBayesHoeffdingInequality` with parameter `σ² = ((b - a) / 2)²`. In the classical
setting $0 \le L \le 1$, this gives `σ² = 1/4`.

    **Proof**: `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` (Hoeffding's lemma)
    bounds the centered MGF by `exp(σ² t² / 2)` for all `t`; taking logarithms yields
    the `h_subg` form. -/
theorem boundedLossSubGaussian {μ : Measure (W ι)} [IsProbabilityMeasure μ]
    (X : W ι → ℝ) {a b : ℝ}
    (hm : AEMeasurable X μ)
    (hb : ∀ᵐ w ∂μ, X w ∈ Set.Icc a b)
    (hmean : ∫ w, X w ∂μ = 0) :
    ∀ l : ℝ,
      log (∫ w, exp (l * X w) ∂μ) ≤ l ^ 2 * (((‖b - a‖₊ : ℝ) / 2) ^ 2) / 2 := by
  intro l
  have hsub := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (μ := μ) (X := X) (a := a) (b := b) hm hb hmean
  have hmgf : ∫ w, exp (l * X w) ∂μ ≤
      Real.exp (((‖b - a‖₊ : ℝ) / 2) ^ 2 * l ^ 2 / 2) := by
    exact hsub.mgf_le l
  have hpos : 0 < ∫ w, exp (l * X w) ∂μ :=
    integral_exp_pos (μ := μ) (f := fun w => l * X w) (by
      have h_int : Integrable (fun w => exp (l * X w)) μ :=
        (hsub.integrable_exp_mul l).congr (Filter.Eventually.of_forall (fun w => by ring))
      exact h_int)
  have hlog_le : log (∫ w, exp (l * X w) ∂μ) ≤
      log (Real.exp (((‖b - a‖₊ : ℝ) / 2) ^ 2 * l ^ 2 / 2)) := by
    exact Real.log_le_log hpos hmgf
  rw [Real.log_exp] at hlog_le
  nlinarith [hlog_le]

end LeanSharp
