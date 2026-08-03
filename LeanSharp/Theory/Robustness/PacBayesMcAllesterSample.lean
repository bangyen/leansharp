/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Theory.Robustness.PacBayesMcAllester
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# McAllester PAC-Bayes: Sample-Level Integrals

This module collects the sample-level integral facts used by the McAllester bound:
the empirical risk is bounded in `[0, 1]`, integrable under a posterior, measurable in
the hypothesis and jointly over sample/hypothesis, and the posterior risk excess is
at most `1`.

## Main Theorems

* `empiricalRisk_mem_Icc`: the empirical risk of a bounded loss lies in `[0, 1]`.
* `integrable_empiricalRisk`: the empirical risk is integrable under the posterior.
* `integral_riskExcess`: the integral of the per-sample risk excess splits.
* `riskExcess_exp_le`: the pointwise risk excess, bounded by `1`, is exponentially
  bounded by `l · n`.
* `measurable_empiricalRisk_w`: the empirical risk is measurable in the hypothesis.
* `measurable_empiricalRisk_prod`: the empirical risk is jointly measurable.
* `posteriorRiskExcess_le_one`: the posterior risk excess satisfies `E_P[L_D] - E_P[L_S] ≤ 1`.
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

omit [IsProbabilityMeasure PΩ] [IsProbabilityMeasure D] in
/-- The empirical risk of a pointwise-bounded loss lies in `[0, 1]`. -/
lemma empiricalRisk_mem_Icc (C : RiskExcessCtx PΩ D n Xᵢ ℓ L_D) (w : W ι) (ω : Ω) :
    empiricalRisk n Xᵢ ℓ w ω ∈ Set.Icc (0 : ℝ) 1 := by
  rw [empiricalRisk]
  have hn : (0 : ℝ) < n := by exact_mod_cast C.hn0
  constructor
  · exact div_nonneg (Finset.sum_nonneg (fun i _ => (C.hℓ_b w (Xᵢ i ω)).1)) hn.le
  · have hsum_le : (∑ i, ℓ w (Xᵢ i ω)) ≤ (n : ℝ) := by
      calc
        (∑ i, ℓ w (Xᵢ i ω)) ≤ ∑ i, (1 : ℝ) := by
          exact Finset.sum_le_sum (fun i _ => (C.hℓ_b w (Xᵢ i ω)).2)
        _ = (n : ℝ) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact (div_le_iff₀ hn).mpr (by simpa only [one_mul] using hsum_le)

omit [IsProbabilityMeasure PΩ] [IsProbabilityMeasure D] [MeasurableSpace Ω] [MeasurableSpace X] in
/-- The empirical risk is integrable under the posterior `P`. -/
lemma integrable_empiricalRisk
    (P : Measure (W ι))
    (hℓ_w_int : ∀ x, Integrable (fun w => ℓ w x) P) (ω : Ω) :
    Integrable (fun w : W ι => empiricalRisk n Xᵢ ℓ w ω) P := by
  unfold empiricalRisk
  have hsum : Integrable (fun w : W ι => ∑ i, ℓ w (Xᵢ i ω)) P := by
    exact integrable_finset_sum Finset.univ (fun i _ => hℓ_w_int (Xᵢ i ω))
  exact hsum.div_const (n : ℝ)

omit [IsProbabilityMeasure PΩ] [IsProbabilityMeasure D] [MeasurableSpace Ω] [MeasurableSpace X] in
/-- The integral of the per-sample risk excess splits into a difference of integrals. -/
lemma integral_riskExcess
    (P : Measure (W ι))
    (hL_D_int : Integrable L_D P) (hℓ_w_int : ∀ x, Integrable (fun w => ℓ w x) P)
    (ω : Ω) :
    (∫ w, (L_D w - empiricalRisk n Xᵢ ℓ w ω) ∂P) =
      (∫ w, L_D w ∂P) - (∫ w, empiricalRisk n Xᵢ ℓ w ω ∂P) := by
  rw [integral_sub hL_D_int (integrable_empiricalRisk P hℓ_w_int ω)]

omit [IsProbabilityMeasure PΩ] [IsProbabilityMeasure D] in
/-- The pointwise risk excess, bounded by `1`, is exponentially bounded by `l · n`. -/
lemma riskExcess_exp_le (l : ℝ) (hl : 0 < l)
    {x : ℝ} (hx : x ≤ 1) :
    exp (l * ((n : ℝ) * x)) ≤ exp (l * (n : ℝ)) := by
  have hsubn : (n : ℝ) * x ≤ (n : ℝ) := by
    calc
      (n : ℝ) * x ≤ (n : ℝ) * 1 := by exact mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg _)
      _ = (n : ℝ) := by ring
  have hle : l * ((n : ℝ) * x) ≤ l * (n : ℝ) := mul_le_mul_of_nonneg_left hsubn hl.le
  exact exp_le_exp.mpr hle

omit [IsProbabilityMeasure PΩ] [IsProbabilityMeasure D] [MeasurableSpace Ω] in
/-- The empirical risk is measurable in the hypothesis variable. -/
lemma measurable_empiricalRisk_w
    (hℓ_prod : Measurable (fun p : W ι × X => ℓ p.1 p.2)) (ω : Ω) :
    Measurable (fun w : W ι => empiricalRisk n Xᵢ ℓ w ω) := by
  unfold empiricalRisk
  have hℓw : ∀ i : Fin n, Measurable (fun w : W ι => ℓ w (Xᵢ i ω)) := by
    intro i
    have hmap : Measurable (fun w : W ι => (w, Xᵢ i ω)) := by
      exact measurable_id.prodMk measurable_const
    exact hℓ_prod.comp hmap
  have hsum : Measurable (fun w : W ι => ∑ i, ℓ w (Xᵢ i ω)) :=
    Finset.measurable_sum Finset.univ (fun i _ => hℓw i)
  exact hsum.div_const (n : ℝ)

omit [IsProbabilityMeasure PΩ] [IsProbabilityMeasure D] in
/-- The empirical risk is jointly measurable over the sample and the hypothesis. -/
lemma measurable_empiricalRisk_prod (C : RiskExcessCtx PΩ D n Xᵢ ℓ L_D)
    (hℓ_prod : Measurable (fun p : W ι × X => ℓ p.1 p.2)) :
    Measurable (fun z : Ω × W ι => empiricalRisk n Xᵢ ℓ z.2 z.1) := by
  unfold empiricalRisk
  have hℓz : ∀ i : Fin n, Measurable (fun z : Ω × W ι => ℓ z.2 (Xᵢ i z.1)) := by
    intro i
    have hmap : Measurable (fun z : Ω × W ι => (z.2, Xᵢ i z.1)) := by
      exact measurable_snd.prodMk ((C.hX_meas i).comp measurable_fst)
    exact hℓ_prod.comp hmap
  have hsum : Measurable (fun z : Ω × W ι => ∑ i, ℓ z.2 (Xᵢ i z.1)) :=
    Finset.measurable_sum Finset.univ (fun i _ => hℓz i)
  exact hsum.div_const (n : ℝ)

omit [IsProbabilityMeasure PΩ] in
/-- The posterior risk excess is at most `1`: `E_P[L_D] - E_P[L_S] ≤ 1`. -/
lemma posteriorRiskExcess_le_one (C : RiskExcessCtx PΩ D n Xᵢ ℓ L_D)
    (P : Measure (W ι)) [IsProbabilityMeasure P]
    (hL_D_int : Integrable L_D P) (hℓ_w_int : ∀ x, Integrable (fun w => ℓ w x) P)
    (ω : Ω) :
    (∫ w, L_D w ∂P - ∫ w, empiricalRisk n Xᵢ ℓ w ω ∂P) ≤ 1 := by
  have hpt : ∀ w, L_D w - empiricalRisk n Xᵢ ℓ w ω ≤ 1 := fun w => by
    have h1 : L_D w ∈ Set.Icc (0 : ℝ) 1 := populationRisk_mem_Icc C w
    have h2 : empiricalRisk n Xᵢ ℓ w ω ∈ Set.Icc (0 : ℝ) 1 := empiricalRisk_mem_Icc C w ω
    linarith [h1.2, h2.1]
  have h_one : (∫ w, (1 : ℝ) ∂P) = 1 := by
    simp only [integral_const, probReal_univ, one_smul]
  have h_int : Integrable (fun w => L_D w - empiricalRisk n Xᵢ ℓ w ω) P :=
    hL_D_int.sub (integrable_empiricalRisk P hℓ_w_int ω)
  have hle : (∫ w, (L_D w - empiricalRisk n Xᵢ ℓ w ω) ∂P) ≤ 1 := by
    calc
      (∫ w, (L_D w - empiricalRisk n Xᵢ ℓ w ω) ∂P) ≤ ∫ w, (1 : ℝ) ∂P :=
        integral_mono h_int (integrable_const (1 : ℝ)) hpt
      _ = 1 := h_one
  have hsplit : (∫ w, (L_D w - empiricalRisk n Xᵢ ℓ w ω) ∂P) =
      (∫ w, L_D w ∂P) - (∫ w, empiricalRisk n Xᵢ ℓ w ω ∂P) :=
    integral_riskExcess P hL_D_int hℓ_w_int ω
  rw [hsplit] at hle
  linarith

end

end LeanSharp
