/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Theory.Robustness.PacBayesMcAllesterSample
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod

/-!
# McAllester PAC-Bayes: Donsker-Varadhan over the Sample

This module runs the Donsker-Varadhan inequality pointwise in the sample and pushes it
through a Fubini step, producing the exponential-moment bound on the posterior risk
excess. It is the core of the finite-sample McAllester bound: for a fixed posterior `P`
and prior `μ`, `E_S[exp(l·n·(E_P[L_D] - E_P[L_S]))] ≤ exp (KL + l²n/8)`.

## Main Theorems

* `posteriorRiskExcess_exp_le`: the posterior risk excess is exponentially bounded by `l · n`.
* `integrable_posteriorExp`: the exponential of the posterior risk excess is integrable.
* `dvExponentiated`: the exponentiated Donsker-Varadhan inequality, pointwise in the sample.
* `integrable_prod_exp`: the Fubini integrand is integrable on `PΩ.prod μ`.
* `posteriorMomentBound`: the exponential moment of the posterior risk excess is bounded
  by `exp (KL + l²n/8)`; the Fubini step.
-/

namespace LeanSharp

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

noncomputable section

variable {ι : Type*}
variable {Ω X : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  {PΩ : Measure Ω} [IsProbabilityMeasure PΩ]
  {D : Measure X} [IsProbabilityMeasure D]
  {n : ℕ} {Xᵢ : Fin n → Ω → X}
  {ℓ : W ι → X → ℝ} {L_D : W ι → ℝ}

section Dv

variable {P μ : Measure (W ι)} [IsProbabilityMeasure P] [IsProbabilityMeasure μ] [SigmaFinite μ]

omit [IsProbabilityMeasure PΩ] in
/-- The posterior risk excess is exponentially bounded by `l · n` at every outcome. -/
lemma posteriorRiskExcess_exp_le (C : RiskExcessCtx PΩ D n Xᵢ ℓ L_D) (l : ℝ) (hl : 0 < l)
    (hL_D_int : Integrable L_D P) (hℓ_w_int : ∀ x, Integrable (fun w => ℓ w x) P)
    (ω : Ω) :
    exp (l * ((n : ℝ) * (∫ w, L_D w ∂P - ∫ w, empiricalRisk n Xᵢ ℓ w ω ∂P))) ≤
      exp (l * (n : ℝ)) :=
  riskExcess_exp_le l hl (posteriorRiskExcess_le_one C P hL_D_int hℓ_w_int ω)

/-- The exponential of the posterior risk excess is integrable over the sample. -/
lemma integrable_posteriorExp (C : RiskExcessCtx PΩ D n Xᵢ ℓ L_D) (l : ℝ) (hl : 0 < l)
    (hL_D_int : Integrable L_D P) (hℓ_w_int : ∀ x, Integrable (fun w => ℓ w x) P)
    (hℓ_prod : Measurable (fun p : W ι × X => ℓ p.1 p.2)) :
    Integrable (fun ω : Ω =>
        exp (l * ((n : ℝ) * (∫ w, L_D w ∂P - ∫ w, empiricalRisk n Xᵢ ℓ w ω ∂P)))) PΩ := by
  refine ⟨?_, ?_⟩
  · show AEStronglyMeasurable (fun ω : Ω =>
        exp (l * ((n : ℝ) * (∫ w, L_D w ∂P - ∫ w, empiricalRisk n Xᵢ ℓ w ω ∂P)))) PΩ
    have hLS_prod : Measurable (fun z : Ω × W ι => empiricalRisk n Xᵢ ℓ z.2 z.1) :=
      measurable_empiricalRisk_prod C hℓ_prod
    have hLS_int : AEStronglyMeasurable (fun ω : Ω => ∫ w, empiricalRisk n Xᵢ ℓ w ω ∂P) PΩ :=
      hLS_prod.aestronglyMeasurable.integral_prod_right'
    have hconst : Measurable (fun _ : Ω => ∫ w, L_D w ∂P) := measurable_const
    have hsub : AEStronglyMeasurable (fun ω : Ω =>
        (∫ w, L_D w ∂P) - (∫ w, empiricalRisk n Xᵢ ℓ w ω ∂P)) PΩ :=
      hconst.aestronglyMeasurable.sub hLS_int
    have hmul : AEStronglyMeasurable (fun ω : Ω =>
        (n : ℝ) * ((∫ w, L_D w ∂P) - (∫ w, empiricalRisk n Xᵢ ℓ w ω ∂P))) PΩ :=
      hsub.const_mul (n : ℝ)
    have hmul' : AEStronglyMeasurable (fun ω : Ω =>
        l * ((n : ℝ) * ((∫ w, L_D w ∂P) - (∫ w, empiricalRisk n Xᵢ ℓ w ω ∂P)))) PΩ :=
      hmul.const_mul l
    exact (measurable_exp.comp_aemeasurable hmul'.aemeasurable).aestronglyMeasurable
  · exact HasFiniteIntegral.of_bounded (by
      filter_upwards with ω
      have hle1 : (∫ w, L_D w ∂P - ∫ w, empiricalRisk n Xᵢ ℓ w ω ∂P) ≤ 1 :=
        posteriorRiskExcess_le_one C P hL_D_int hℓ_w_int ω
      rw [Real.norm_of_nonneg (exp_nonneg _)]
      exact riskExcess_exp_le l hl hle1)

omit [IsProbabilityMeasure PΩ] in
/-- **Exponentiated Donsker-Varadhan**, pointwise in the sample: for each outcome `ω`,
    `exp(l·n·(E_P[L_D] - E_P[L_S(·,ω)]))` is bounded by `exp(KL) · E_μ[exp(l·n·(L_D - L_S))]`. -/
lemma dvExponentiated (C : RiskExcessCtx PΩ D n Xᵢ ℓ L_D)
    (hPQ : P ≪ μ)
    (hL_D_int : Integrable L_D P) (hℓ_w_int : ∀ x, Integrable (fun w => ℓ w x) P)
    (hllr : Integrable (llr P μ) P) (hL_D_meas : Measurable L_D)
    (hℓ_prod : Measurable (fun p : W ι × X => ℓ p.1 p.2))
    (l : ℝ) (hl : 0 < l) (ω : Ω) :
    exp (l * ((n : ℝ) * (∫ w, L_D w ∂P - ∫ w, empiricalRisk n Xᵢ ℓ w ω ∂P))) ≤
      exp ((klDivergenceW P μ).toReal) *
        (∫ w, exp (l * ((n : ℝ) * (L_D w - empiricalRisk n Xᵢ ℓ w ω))) ∂μ) := by
  let f : W ι → ℝ := fun w => l * ((n : ℝ) * (L_D w - empiricalRisk n Xᵢ ℓ w ω))
  have hf : Integrable f P := by
    have hLS : Integrable (fun w : W ι => empiricalRisk n Xᵢ ℓ w ω) P :=
      integrable_empiricalRisk P hℓ_w_int ω
    have hsub : Integrable (fun w => L_D w - empiricalRisk n Xᵢ ℓ w ω) P := hL_D_int.sub hLS
    simpa only [f, mul_assoc] using (hsub.const_mul (l * (n : ℝ)))
  have hef : Integrable (fun w => exp (f w)) μ := by
    have hmeas : Measurable (fun w => exp (f w)) := by
      dsimp only [f]
      have hLS_m : Measurable (fun w : W ι => empiricalRisk n Xᵢ ℓ w ω) :=
        measurable_empiricalRisk_w hℓ_prod ω
      have hm : Measurable (fun w => (l * (n : ℝ)) * (L_D w - empiricalRisk n Xᵢ ℓ w ω)) :=
        (hL_D_meas.sub hLS_m).const_mul (l * (n : ℝ))
      convert hm.exp using 1
      ext w
      ring
    have hbounded : ∀ᵐ w ∂μ, ‖exp (f w)‖ ≤ exp (l * (n : ℝ)) := by
      filter_upwards with w
      have hsub : L_D w - empiricalRisk n Xᵢ ℓ w ω ≤ 1 := by
        have h1 : L_D w ∈ Set.Icc (0 : ℝ) 1 := populationRisk_mem_Icc C w
        have h2 : empiricalRisk n Xᵢ ℓ w ω ∈ Set.Icc (0 : ℝ) 1 := empiricalRisk_mem_Icc C w ω
        linarith [h1.2, h2.1]
      rw [Real.norm_of_nonneg (exp_nonneg _)]
      simpa only [f] using (riskExcess_exp_le l hl hsub)
    refine ⟨hmeas.aestronglyMeasurable, HasFiniteIntegral.of_bounded hbounded⟩
  have hdv := DonskerVaradhanInequality_holds P μ f hPQ hf hef hllr
  have hlin : (∫ w, f w ∂P) =
      l * ((n : ℝ) * (∫ w, L_D w ∂P - ∫ w, empiricalRisk n Xᵢ ℓ w ω ∂P)) := by
    have hsub : (∫ w, (L_D w - empiricalRisk n Xᵢ ℓ w ω) ∂P) =
        (∫ w, L_D w ∂P) - (∫ w, empiricalRisk n Xᵢ ℓ w ω ∂P) :=
      integral_riskExcess P hL_D_int hℓ_w_int ω
    dsimp only [f]
    rw [integral_const_mul]
    congr 1
    rw [integral_const_mul]
    rw [hsub]
  have hpos : 0 < ∫ w, exp (f w) ∂μ := by
    exact integral_exp_pos (f := fun w => f w) hef
  calc
    exp (l * ((n : ℝ) * (∫ w, L_D w ∂P - ∫ w, empiricalRisk n Xᵢ ℓ w ω ∂P)))
        = exp (∫ w, f w ∂P) := by rw [hlin]
    _ ≤ exp (log (∫ w, exp (f w) ∂μ) + (klDivergenceW P μ).toReal) := by
      exact exp_le_exp.mpr hdv.2.2
    _ = exp (log (∫ w, exp (f w) ∂μ)) * exp ((klDivergenceW P μ).toReal) := by rw [exp_add]
    _ = (∫ w, exp (f w) ∂μ) * exp ((klDivergenceW P μ).toReal) := by rw [Real.exp_log hpos]
    _ = exp ((klDivergenceW P μ).toReal) * (∫ w, exp (f w) ∂μ) := by ring

omit [SigmaFinite μ] in
/-- The double integrand of the Fubini step is integrable on `PΩ.prod μ`. -/
lemma integrable_prod_exp (C : RiskExcessCtx PΩ D n Xᵢ ℓ L_D) (l : ℝ) (hl : 0 < l)
    (hL_D_meas : Measurable L_D) (hℓ_prod : Measurable (fun p : W ι × X => ℓ p.1 p.2)) :
    Integrable (fun z : Ω × W ι =>
        exp (l * ((n : ℝ) * (L_D z.2 - empiricalRisk n Xᵢ ℓ z.2 z.1)))) (PΩ.prod μ) := by
  refine ⟨?_, ?_⟩
  · show AEStronglyMeasurable (fun z : Ω × W ι =>
        exp (l * ((n : ℝ) * (L_D z.2 - empiricalRisk n Xᵢ ℓ z.2 z.1)))) (PΩ.prod μ)
    have hLS_z : Measurable (fun z : Ω × W ι => empiricalRisk n Xᵢ ℓ z.2 z.1) :=
      measurable_empiricalRisk_prod C hℓ_prod
    have hLD_z : Measurable (fun z : Ω × W ι => L_D z.2) := hL_D_meas.comp measurable_snd
    have hsub : Measurable (fun z : Ω × W ι => L_D z.2 - empiricalRisk n Xᵢ ℓ z.2 z.1) :=
      hLD_z.sub hLS_z
    have hmul : Measurable (fun z : Ω × W ι =>
        l * ((n : ℝ) * (L_D z.2 - empiricalRisk n Xᵢ ℓ z.2 z.1))) :=
      (hsub.const_mul (n : ℝ)).const_mul l
    exact hmul.exp.aestronglyMeasurable
  · exact HasFiniteIntegral.of_bounded (by
      filter_upwards with z
      have hsub : L_D z.2 - empiricalRisk n Xᵢ ℓ z.2 z.1 ≤ 1 := by
        have h1 : L_D z.2 ∈ Set.Icc (0 : ℝ) 1 := populationRisk_mem_Icc C z.2
        have h2 : empiricalRisk n Xᵢ ℓ z.2 z.1 ∈ Set.Icc (0 : ℝ) 1 :=
          empiricalRisk_mem_Icc C z.2 z.1
        linarith [h1.2, h2.1]
      rw [Real.norm_of_nonneg (exp_nonneg _)]
      exact riskExcess_exp_le l hl hsub)

/-- **Exponential moment of the posterior risk excess**: the Fubini step yields
    `E_S[exp(l·n·(E_P[L_D] - E_P[L_S]))] ≤ exp (KL + l²n/8)`. -/
lemma posteriorMomentBound (C : RiskExcessCtx PΩ D n Xᵢ ℓ L_D)
    (hPQ : P ≪ μ)
    (hL_D_int : Integrable L_D P) (hℓ_w_int : ∀ x, Integrable (fun w => ℓ w x) P)
    (hllr : Integrable (llr P μ) P) (hL_D_meas : Measurable L_D)
    (hℓ_prod : Measurable (fun p : W ι × X => ℓ p.1 p.2))
    (l : ℝ) (hl : 0 < l) :
    (∫ ω : Ω, exp (l * ((n : ℝ) * (∫ w, L_D w ∂P - ∫ w, empiricalRisk n Xᵢ ℓ w ω ∂P))) ∂PΩ) ≤
      exp ((klDivergenceW P μ).toReal + l ^ 2 * (n : ℝ) / 8) := by
  let h : Ω → ℝ := fun ω => exp (l * ((n : ℝ) * (∫ w, L_D w ∂P - ∫ w, empiricalRisk n Xᵢ ℓ w ω ∂P)))
  let hh : Ω → ℝ := fun ω => ∫ w, exp (l * ((n : ℝ) * (L_D w - empiricalRisk n Xᵢ ℓ w ω))) ∂μ
  have h_prod : Integrable (fun z : Ω × W ι =>
      exp (l * ((n : ℝ) * (L_D z.2 - empiricalRisk n Xᵢ ℓ z.2 z.1)))) (PΩ.prod μ) :=
    integrable_prod_exp C l hl hL_D_meas hℓ_prod
  have h_int_hh : Integrable hh PΩ := by
    simpa only [hh] using h_prod.integral_prod_left
  have h_int_h : Integrable h PΩ :=
    integrable_posteriorExp C l hl hL_D_int hℓ_w_int hℓ_prod
  have h_pt : ∀ ω, h ω ≤ exp (klDivergenceW P μ).toReal * hh ω := fun ω =>
    (dvExponentiated C hPQ hL_D_int hℓ_w_int hllr hL_D_meas hℓ_prod l hl ω)
  have h_markov_input : (∫ ω, h ω ∂PΩ) ≤
      exp (klDivergenceW P μ).toReal * (∫ ω, hh ω ∂PΩ) := by
    have h_int_hh' : Integrable (fun ω => exp (klDivergenceW P μ).toReal * hh ω) PΩ :=
      h_int_hh.const_mul (exp (klDivergenceW P μ).toReal)
    have h_pt_ae : h ≤ᵐ[PΩ] fun ω => exp (klDivergenceW P μ).toReal * hh ω :=
      Filter.Eventually.of_forall h_pt
    have h₁ := integral_mono_ae h_int_h h_int_hh' h_pt_ae
    have h₂ : (∫ ω, exp (klDivergenceW P μ).toReal * hh ω ∂PΩ) =
        exp (klDivergenceW P μ).toReal * (∫ ω, hh ω ∂PΩ) := by
      rw [integral_const_mul]
    linarith
  have h_fubini : (∫ ω, hh ω ∂PΩ) =
      (∫ w, (∫ ω, exp (l * ((n : ℝ) * (L_D w - empiricalRisk n Xᵢ ℓ w ω))) ∂PΩ) ∂μ) := by
    simpa only [hh] using (integral_integral_swap h_prod)
  have h_inner : ∀ w : W ι, (∫ ω, exp (l * ((n : ℝ) * (L_D w - empiricalRisk n Xᵢ ℓ w ω))) ∂PΩ) ≤
      exp (l ^ 2 * (n : ℝ) / 8) := fun w => empiricalExcessMomentBound C w l
  have h_int_inner : Integrable (fun w : W ι =>
      ∫ ω, exp (l * ((n : ℝ) * (L_D w - empiricalRisk n Xᵢ ℓ w ω))) ∂PΩ) μ := by
    simpa only using h_prod.integral_prod_right
  have h_mu : (∫ w, (∫ ω, exp (l * ((n : ℝ) * (L_D w - empiricalRisk n Xᵢ ℓ w ω))) ∂PΩ) ∂μ) ≤
      exp (l ^ 2 * (n : ℝ) / 8) := by
    have hle := integral_mono_ae h_int_inner (integrable_const (exp (l ^ 2 * (n : ℝ) / 8)))
      (Filter.Eventually.of_forall h_inner)
    have hconst : (∫ w : W ι, exp (l ^ 2 * (n : ℝ) / 8) ∂μ) = exp (l ^ 2 * (n : ℝ) / 8) := by
      simp only [integral_const, probReal_univ, one_smul]
    linarith
  calc
    (∫ ω, h ω ∂PΩ) ≤ exp (klDivergenceW P μ).toReal * (∫ ω, hh ω ∂PΩ) := h_markov_input
    _ = exp (klDivergenceW P μ).toReal *
        (∫ w, (∫ ω, exp (l * ((n : ℝ) * (L_D w - empiricalRisk n Xᵢ ℓ w ω))) ∂PΩ) ∂μ) := by
          rw [h_fubini]
    _ ≤ exp (klDivergenceW P μ).toReal * exp (l ^ 2 * (n : ℝ) / 8) := by
      exact mul_le_mul_of_nonneg_left h_mu (exp_nonneg _)
    _ = exp ((klDivergenceW P μ).toReal + l ^ 2 * (n : ℝ) / 8) := by
      rw [exp_add]

end Dv

end

end LeanSharp
