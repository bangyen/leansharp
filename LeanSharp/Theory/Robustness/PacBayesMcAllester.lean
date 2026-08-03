/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Theory.Robustness.PacBayesBasis
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Probability.HasLawExists
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.SubGaussian

/-!
# McAllester PAC-Bayes Bound with Confidence

This module develops the finite-sample concentration that underlies the McAllester
PAC-Bayes bound with confidence parameter `δ`, on bounded losses over an i.i.d.
sample of size `n`. It completes the per-hypothesis half of the chain
`DV → λ-PAC-Bayes → √KL → McAllester-with-(n, δ)`; the confidence statement itself
is derived in `PacBayesMcAllesterConfidence`.

## Main Definitions

* `empiricalRisk`: the average loss of a hypothesis over an i.i.d. sample.
* `RiskExcessCtx`: the hypotheses of the per-hypothesis Hoeffding concentration:
  an i.i.d. sample and a pointwise-bounded loss whose population expectation is `L_D`.

## Main Theorems

* `n_mul_riskExcess_eq_sum`: the sample risk excess `n · (L_D - L_S)` is the sum of
  the centered per-sample losses.
* `integrable_loss_sample`: a bounded loss is integrable over the sample.
* `integrable_loss_pop`: a bounded loss is integrable under the population law.
* `populationRisk_mem_Icc`: a bounded loss has population risk in `[0, 1]`.
* `riskExcess_mean_zero`: the centered per-sample loss has zero mean.
* `riskExcessSubGaussian`: Hoeffding's lemma: the centered per-sample loss is
  sub-Gaussian with parameter `1/4`.
* `empiricalExcessMomentBound`: Hoeffding's bound on the exponential moment of the
  risk excess of a single hypothesis: `E[exp(l · n · (L_D - L_S))] ≤ exp(l²n/8)`.
-/

namespace LeanSharp

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

noncomputable section

/-- Empirical risk of a hypothesis `w` on an i.i.d. sample of size `n` at outcome `ω`. -/
def empiricalRisk (n : ℕ) {Ω X : Type*}
    (Xᵢ : Fin n → Ω → X) (ℓ : W ι → X → ℝ) (w : W ι) (ω : Ω) : ℝ :=
  (∑ i, ℓ w (Xᵢ i ω)) / (n : ℝ)

/-- The per-sample risk excess `n · (L_D - L_S)` equals the sum of the centered
    per-sample losses. -/
lemma n_mul_riskExcess_eq_sum {Ω X : Type*}
    (n : ℕ) (Xᵢ : Fin n → Ω → X) (ℓ : W ι → X → ℝ) (L_D : W ι → ℝ)
    (w : W ι) (ω : Ω) (hn : (n : ℝ) ≠ 0) :
    (n : ℝ) * (L_D w - empiricalRisk n Xᵢ ℓ w ω) = ∑ i, (L_D w - ℓ w (Xᵢ i ω)) := by
  calc
    (n : ℝ) * (L_D w - (∑ i, ℓ w (Xᵢ i ω)) / (n : ℝ))
        = (n : ℝ) * L_D w - (n : ℝ) * ((∑ i, ℓ w (Xᵢ i ω)) / (n : ℝ)) := by ring
    _ = (n : ℝ) * L_D w - ∑ i, ℓ w (Xᵢ i ω) := by rw [mul_div_cancel₀ _ hn]
    _ = ∑ i, (L_D w - ℓ w (Xᵢ i ω)) := by
      rw [Finset.sum_sub_distrib]
      congr 1
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Context of the per-hypothesis Hoeffding concentration: an i.i.d. sample of size `n`
    from `D` and a pointwise-bounded loss whose population expectation is `L_D`. -/
structure RiskExcessCtx {Ω X : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (PΩ : Measure Ω) (D : Measure X) (n : ℕ) (Xᵢ : Fin n → Ω → X)
    (ℓ : W ι → X → ℝ) (L_D : W ι → ℝ) : Prop where
  hn0 : 0 < n
  hindep : iIndepFun Xᵢ PΩ
  hlaw : ∀ i, HasLaw (Xᵢ i) D PΩ
  hX_meas : ∀ i, Measurable (Xᵢ i)
  h_mean : ∀ w, ∫ x, ℓ w x ∂D = L_D w
  h_meas : ∀ w, Measurable (ℓ w)
  hℓ_b : ∀ w x, ℓ w x ∈ Set.Icc (0 : ℝ) 1

section Hoeffding

variable {Ω X : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  {PΩ : Measure Ω} [IsProbabilityMeasure PΩ]
  {D : Measure X} [IsProbabilityMeasure D]
  {n : ℕ} {Xᵢ : Fin n → Ω → X}
  {ℓ : W ι → X → ℝ} {L_D : W ι → ℝ}

omit [IsProbabilityMeasure D] in
/-- The bounded loss is integrable over the sample at any outcome-indexed datum. -/
lemma integrable_loss_sample (C : RiskExcessCtx PΩ D n Xᵢ ℓ L_D) (w : W ι) (i : Fin n) :
    Integrable (fun ω : Ω => ℓ w (Xᵢ i ω)) PΩ := by
  refine ⟨?_, ?_⟩
  · show AEStronglyMeasurable (fun ω : Ω => ℓ w (Xᵢ i ω)) PΩ
    have h₁ : AEMeasurable (fun ω : Ω => ℓ w (Xᵢ i ω)) PΩ :=
      (C.h_meas w).comp_aemeasurable (C.hlaw i).aemeasurable
    exact h₁.aestronglyMeasurable
  · exact HasFiniteIntegral.of_bounded (by
      filter_upwards with ω
      have hℓ0 : (0 : ℝ) ≤ ℓ w (Xᵢ i ω) := (C.hℓ_b w (Xᵢ i ω)).1
      have hℓ1 : ℓ w (Xᵢ i ω) ≤ 1 := (C.hℓ_b w (Xᵢ i ω)).2
      have habs : |ℓ w (Xᵢ i ω)| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      simpa only [Real.norm_eq_abs] using habs)

omit [IsProbabilityMeasure PΩ] in
/-- The bounded loss is integrable under the population distribution. -/
lemma integrable_loss_pop (C : RiskExcessCtx PΩ D n Xᵢ ℓ L_D) (w : W ι) :
    Integrable (ℓ w) D := by
  refine ⟨?_, ?_⟩
  · exact (C.h_meas w).aestronglyMeasurable
  · exact HasFiniteIntegral.of_bounded (by
      filter_upwards with x
      have hℓ0 : (0 : ℝ) ≤ ℓ w x := (C.hℓ_b w x).1
      have hℓ1 : ℓ w x ≤ 1 := (C.hℓ_b w x).2
      have habs : |ℓ w x| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      simpa only [Real.norm_eq_abs] using habs)

omit [IsProbabilityMeasure PΩ] in
/-- The population risk is bounded in `[0, 1]` when the loss is. -/
lemma populationRisk_mem_Icc (C : RiskExcessCtx PΩ D n Xᵢ ℓ L_D) (w : W ι) :
    L_D w ∈ Set.Icc (0 : ℝ) 1 := by
  have hb := C.h_mean w
  rw [← hb]
  constructor
  · exact integral_nonneg (fun x => (C.hℓ_b w x).1)
  · have hle : (∫ x, ℓ w x ∂D) ≤ (∫ x, (1 : ℝ) ∂D) :=
      integral_mono (integrable_loss_pop C w) (integrable_const (1 : ℝ)) (fun x => (C.hℓ_b w x).2)
    have hconst : (∫ x, (1 : ℝ) ∂D) = 1 := by
      simp only [integral_const, probReal_univ, one_smul]
    linarith

omit [IsProbabilityMeasure D] in
/-- The centered per-sample loss `L_D w - ℓ w (Xᵢ ω)` has zero mean over the sample. -/
lemma riskExcess_mean_zero (C : RiskExcessCtx PΩ D n Xᵢ ℓ L_D) (w : W ι) (i : Fin n) :
    (∫ ω : Ω, (L_D w - ℓ w (Xᵢ i ω)) ∂PΩ) = 0 := by
  calc
    (∫ ω, (L_D w - ℓ w (Xᵢ i ω)) ∂PΩ)
        = L_D w - (∫ ω, ℓ w (Xᵢ i ω) ∂PΩ) := by
          rw [integral_sub (integrable_const _) (integrable_loss_sample C w i)]
          congr 1
          simp only [integral_const, probReal_univ, one_smul]
    _ = L_D w - (∫ x, ℓ w x ∂D) := by
      congr 1
      simpa only using (HasLaw.integral_comp (C.hlaw i) (C.h_meas w).aestronglyMeasurable)
    _ = 0 := by rw [C.h_mean w]; ring

omit [IsProbabilityMeasure D] in
/-- Hoeffding's lemma per sample point: `L_D w - ℓ w (Xᵢ ω)` is sub-Gaussian with
    parameter `1/4`. -/
lemma riskExcessSubGaussian (C : RiskExcessCtx PΩ D n Xᵢ ℓ L_D) (w : W ι) (i : Fin n) :
    HasSubgaussianMGF (fun ω : Ω => L_D w - ℓ w (Xᵢ i ω)) (1 / 4 : ℝ≥0) PΩ := by
  have hz : HasSubgaussianMGF (fun ω : Ω => L_D w - ℓ w (Xᵢ i ω))
      ((‖L_D w - (L_D w - 1)‖₊ / 2) ^ 2) PΩ :=
    hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (μ := PΩ) (X := fun ω : Ω => L_D w - ℓ w (Xᵢ i ω))
      (a := L_D w - 1) (b := L_D w)
      (by
        show AEMeasurable (fun ω : Ω => L_D w - ℓ w (Xᵢ i ω)) PΩ
        have h₁ : AEMeasurable (fun ω : Ω => ℓ w (Xᵢ i ω)) PΩ :=
          (C.h_meas w).comp_aemeasurable (C.hlaw i).aemeasurable
        exact h₁.const_sub (L_D w))
      (by
        filter_upwards with ω
        have hℓ0 : (0 : ℝ) ≤ ℓ w (Xᵢ i ω) := (C.hℓ_b w (Xᵢ i ω)).1
        have hℓ1 : ℓ w (Xᵢ i ω) ≤ 1 := (C.hℓ_b w (Xᵢ i ω)).2
        constructor <;> linarith)
      (by
        simpa only using riskExcess_mean_zero C w i)
  have hparam : (‖L_D w - (L_D w - 1)‖₊ / 2) ^ 2 = (1 / 4 : ℝ≥0) := by
    have hnorm : ‖L_D w - (L_D w - 1)‖₊ = 1 := by
      rw [show L_D w - (L_D w - 1) = 1 by ring]
      norm_num
    rw [hnorm]
    norm_num
  simpa only [hparam] using hz

omit [IsProbabilityMeasure D] in
/-- **Hoeffding moment bound for a single hypothesis**: the exponential moment of the
    risk excess is bounded by `exp (l² n / 8)`. -/
lemma empiricalExcessMomentBound (C : RiskExcessCtx PΩ D n Xᵢ ℓ L_D) (w : W ι) (l : ℝ) :
    (∫ ω : Ω, exp (l * ((n : ℝ) * (L_D w - empiricalRisk n Xᵢ ℓ w ω))) ∂PΩ) ≤
      exp (l ^ 2 * (n : ℝ) / 8) := by
  let Z : Fin n → Ω → ℝ := fun i ω => L_D w - ℓ w (Xᵢ i ω)
  have hZ_indep : iIndepFun Z PΩ := by
    simpa only [Z] using C.hindep.comp (g := fun _ x => L_D w - ℓ w x)
      (hg := fun _ => by
        have hmℓ : Measurable (ℓ w) := C.h_meas w
        fun_prop)
  have h_subG : ∀ i : Fin n, HasSubgaussianMGF (Z i) (1 / 4 : ℝ≥0) PΩ := by
    intro i
    simpa only [Z] using riskExcessSubGaussian C w i
  have h_sum := HasSubgaussianMGF.sum_of_iIndepFun (h_indep := hZ_indep)
    (c := fun _ : Fin n => (1 / 4 : ℝ≥0))
    (s := Finset.univ) (by intro i hi; exact h_subG i)
  have h_mgf := h_sum.mgf_le l
  have h_param : (↑(∑ _ : Fin n, (1 / 4 : ℝ≥0)) : ℝ) * l ^ 2 / 2 = l ^ 2 * (n : ℝ) / 8 := by
    have hsum : (∑ _ : Fin n, (1 / 4 : ℝ≥0)) = (n : ℝ≥0) / 4 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [one_div, div_eq_mul_inv]
    rw [hsum]
    norm_num
    ring
  have h_excess : (fun ω : Ω => exp (l * ((n : ℝ) * (L_D w - empiricalRisk n Xᵢ ℓ w ω))))
      =ᵐ[PΩ] fun ω => exp (l * (∑ i ∈ Finset.univ, Z i ω)) := by
    filter_upwards with ω
    congr 1
    rw [n_mul_riskExcess_eq_sum n Xᵢ ℓ L_D w ω (Nat.cast_ne_zero.mpr C.hn0.ne')]
  calc
    (∫ ω, exp (l * ((n : ℝ) * (L_D w - empiricalRisk n Xᵢ ℓ w ω))) ∂PΩ)
        = (∫ ω, exp (l * (∑ i ∈ Finset.univ, Z i ω)) ∂PΩ) := by
          rw [integral_congr_ae h_excess]
    _ ≤ exp (↑(∑ _ : Fin n, (1 / 4 : ℝ≥0)) * l ^ 2 / 2) := by
      simpa only using h_mgf
    _ = exp (l ^ 2 * (n : ℝ) / 8) := by rw [h_param]

end Hoeffding

end

end LeanSharp
