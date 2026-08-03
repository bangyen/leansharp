/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Theory.Robustness.PacBayesMcAllesterConfidence
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Prod

/-!
# McAllester PAC-Bayes Bound with Confidence

This module assembles the finite-sample McAllester PAC-Bayes bound with confidence
parameter `δ`: with probability at least `1 - δ` over an i.i.d. sample of size `n`,
the population risk of a fixed posterior `P` is bounded by its empirical risk plus
`√((KL(P ‖ μ) + log (1 / δ)) / (2 n))`. The exponential-moment bound of
`PacBayesMcAllesterConfidence` is converted into a probabilistic statement via
Markov's inequality, and the parameter `λ = √(8a/n)` is optimized.

The theorem is stated for a *fixed* posterior `P` (chosen independently of the
sample); the simultaneous "for all posteriors" form requires a discretization/union
bound and is left as further work.

## Main Theorems

* `expMarkov`: Markov's inequality for a nonnegative variable with bounded expectation.
* `mcAllesterOptimization`: the optimal-`λ` arithmetic yielding `√((KL + log(1/δ))/(2n))`.
* `pacBayesMcAllesterBound`: with probability at least `1 - δ`, the population risk of a
  fixed posterior is at most its empirical risk plus `√((KL(P‖μ) + log(1/δ))/(2n))`.
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

/-- **Markov's inequality** for a nonnegative variable with bounded expectation. -/
lemma expMarkov {α : Type*} [MeasurableSpace α] {P : Measure α} [IsProbabilityMeasure P]
    {g : α → ℝ} (hg_int : Integrable g P) (hg_nonneg : ∀ᵐ ω ∂P, 0 ≤ g ω)
    {c : ℝ} (hc : 0 < c) (h_int : (∫ ω, g ω ∂P) ≤ c) {δ : ℝ} (hδ : 0 < δ) :
    P.real {ω | c / δ ≤ g ω} ≤ δ := by
  have hc_nonneg : 0 ≤ c := le_of_lt hc
  have hcd : 0 < c / δ := div_pos hc hδ
  have hlintegral : (∫⁻ ω, ENNReal.ofReal (g ω) ∂P) ≤ ENNReal.ofReal c := by
    rw [← ofReal_integral_eq_lintegral_ofReal hg_int hg_nonneg]
    exact ENNReal.ofReal_le_ofReal h_int
  have hg_aem : AEMeasurable (fun ω => ENNReal.ofReal (g ω)) P := by fun_prop
  have hmarkov := MeasureTheory.meas_ge_le_lintegral_div hg_aem
    (ε := ENNReal.ofReal (c / δ))
    ((ENNReal.ofReal_eq_zero.not.mpr (not_le.mpr hcd))) ENNReal.ofReal_ne_top
  have hcomb : P {ω | ENNReal.ofReal (c / δ) ≤ ENNReal.ofReal (g ω)} ≤
      ENNReal.ofReal c / ENNReal.ofReal (c / δ) :=
    le_trans hmarkov (ENNReal.div_le_div hlintegral (le_of_eq rfl))
  have hset : {ω | ENNReal.ofReal (c / δ) ≤ ENNReal.ofReal (g ω)} =ᵐ[P]
      {ω | c / δ ≤ g ω} := by
    filter_upwards [hg_nonneg] with ω hω
    exact propext (ENNReal.ofReal_le_ofReal_iff (p := c / δ) (q := g ω) hω)
  have hmeas : P {ω | ENNReal.ofReal (c / δ) ≤ ENNReal.ofReal (g ω)} = P {ω | c / δ ≤ g ω} :=
    measure_congr hset
  have hreal_div : (ENNReal.ofReal c / ENNReal.ofReal (c / δ)).toReal = δ := by
    rw [ENNReal.toReal_div]
    rw [ENNReal.toReal_ofReal hc_nonneg, ENNReal.toReal_ofReal hcd.le]
    field_simp [hc.ne', hδ.ne']
  have hfin : P {ω | c / δ ≤ g ω} ≠ ⊤ := measure_ne_top P {ω | c / δ ≤ g ω}
  have hreal : (P {ω | c / δ ≤ g ω}).toReal ≤ δ := by
    have hdiv_top : (ENNReal.ofReal c / ENNReal.ofReal (c / δ)) ≠ ⊤ :=
      ENNReal.div_ne_top ENNReal.ofReal_ne_top
        ((ENNReal.ofReal_eq_zero.not.mpr (not_le.mpr hcd)))
    have hle := (ENNReal.toReal_le_toReal hfin hdiv_top).mpr
      (by simpa only [hmeas] using hcomb)
    rw [hreal_div] at hle
    exact hle
  change (P {ω | c / δ ≤ g ω}).toReal ≤ δ
  exact hreal

/-- **Optimal-`λ` arithmetic**: at `λ = √(8a/n)`, the Markov bound becomes `√(a/(2n))`. -/
lemma mcAllesterOptimization (a : ℝ) (n : ℝ) (ha : 0 < a) (hn : 0 < n) :
    a / (Real.sqrt (8 * a / n) * n) + Real.sqrt (8 * a / n) / 8 = Real.sqrt (a / (2 * n)) := by
  have ha8n : 0 ≤ a / (8 * n) := div_nonneg ha.le (mul_pos (by norm_num) hn).le
  have ha2n : 0 ≤ a / (2 * n) := div_nonneg ha.le (mul_pos (by norm_num) hn).le
  have hsq1 : (a / (Real.sqrt (8 * a / n) * n)) ^ 2 = a / (8 * n) := by
    have h_sqrt : Real.sqrt (8 * a / n) ^ 2 = 8 * a / n :=
      Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) ha.le) hn.le)
    rw [div_pow, mul_pow, h_sqrt]
    field_simp [ne_of_gt hn]
  have hsq2 : (Real.sqrt (8 * a / n) / 8) ^ 2 = a / (8 * n) := by
    have h_sqrt : Real.sqrt (8 * a / n) ^ 2 = 8 * a / n :=
      Real.sq_sqrt (div_nonneg (mul_nonneg (by norm_num) ha.le) hn.le)
    rw [div_pow, h_sqrt]
    field_simp [ne_of_gt hn]
  have hterm1 : a / (Real.sqrt (8 * a / n) * n) = Real.sqrt (a / (8 * n)) := by
    have hsq : (a / (Real.sqrt (8 * a / n) * n)) ^ 2 = (Real.sqrt (a / (8 * n))) ^ 2 := by
      rw [hsq1, Real.sq_sqrt ha8n]
    have hnn1 : 0 ≤ a / (Real.sqrt (8 * a / n) * n) :=
      div_nonneg ha.le (mul_nonneg (Real.sqrt_nonneg _) (le_of_lt hn))
    have hnn2 : 0 ≤ Real.sqrt (a / (8 * n)) := Real.sqrt_nonneg _
    have habs : |a / (Real.sqrt (8 * a / n) * n)| = |Real.sqrt (a / (8 * n))| :=
      (sq_eq_sq_iff_abs_eq_abs _ _).mp hsq
    rw [abs_of_nonneg hnn1, abs_of_nonneg hnn2] at habs
    exact habs
  have hterm2 : Real.sqrt (8 * a / n) / 8 = Real.sqrt (a / (8 * n)) := by
    have hsq : (Real.sqrt (8 * a / n) / 8) ^ 2 = (Real.sqrt (a / (8 * n))) ^ 2 := by
      rw [hsq2, Real.sq_sqrt ha8n]
    have hnn1 : 0 ≤ Real.sqrt (8 * a / n) / 8 := div_nonneg (Real.sqrt_nonneg _) (by norm_num)
    have hnn2 : 0 ≤ Real.sqrt (a / (8 * n)) := Real.sqrt_nonneg _
    have habs : |Real.sqrt (8 * a / n) / 8| = |Real.sqrt (a / (8 * n))| :=
      (sq_eq_sq_iff_abs_eq_abs _ _).mp hsq
    rw [abs_of_nonneg hnn1, abs_of_nonneg hnn2] at habs
    exact habs
  have h3 : Real.sqrt (a / (8 * n)) + Real.sqrt (a / (8 * n)) = Real.sqrt (a / (2 * n)) := by
    have hk : (2 * Real.sqrt (a / (8 * n))) ^ 2 = a / (2 * n) := by
      rw [mul_pow, Real.sq_sqrt ha8n]
      field_simp [ne_of_gt hn]
      ring
    have hnn : 0 ≤ 2 * Real.sqrt (a / (8 * n)) := mul_nonneg (by norm_num) (Real.sqrt_nonneg _)
    have h2 : 2 * Real.sqrt (a / (8 * n)) = Real.sqrt (a / (2 * n)) := by
      have hsq : (2 * Real.sqrt (a / (8 * n))) ^ 2 = (Real.sqrt (a / (2 * n))) ^ 2 := by
        rw [Real.sq_sqrt ha2n, hk]
      have hnn2 : 0 ≤ Real.sqrt (a / (2 * n)) := Real.sqrt_nonneg _
      have habs : |2 * Real.sqrt (a / (8 * n))| = |Real.sqrt (a / (2 * n))| :=
        (sq_eq_sq_iff_abs_eq_abs _ _).mp hsq
      rw [abs_of_nonneg hnn, abs_of_nonneg hnn2] at habs
      exact habs
    calc
      Real.sqrt (a / (8 * n)) + Real.sqrt (a / (8 * n)) = 2 * Real.sqrt (a / (8 * n)) := by ring
      _ = Real.sqrt (a / (2 * n)) := h2
  calc
    a / (Real.sqrt (8 * a / n) * n) + Real.sqrt (8 * a / n) / 8
        = Real.sqrt (a / (8 * n)) + Real.sqrt (a / (8 * n)) := by rw [hterm1, hterm2]
    _ = Real.sqrt (a / (2 * n)) := h3

/-- **McAllester PAC-Bayes bound with confidence**: with probability at least `1 - δ`
    over the i.i.d. sample, the population risk of a fixed posterior `P` is at most its
    empirical risk plus `√((KL(P ‖ μ) + log (1 / δ)) / (2 n))`. -/
theorem pacBayesMcAllesterBound (C : RiskExcessCtx PΩ D n Xᵢ ℓ L_D)
    (P μ : Measure (W ι)) [IsProbabilityMeasure P] [IsProbabilityMeasure μ] [SigmaFinite μ]
    (hPQ : P ≪ μ)
    (hL_D_int : Integrable L_D P) (hℓ_w_int : ∀ x, Integrable (fun w => ℓ w x) P)
    (hllr : Integrable (llr P μ) P) (hL_D_meas : Measurable L_D)
    (hℓ_prod : Measurable (fun p : W ι × X => ℓ p.1 p.2))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hKL : 0 < (klDivergenceW P μ).toReal) :
    (1 : ℝ) - δ ≤
      PΩ.real {ω | (∫ w, L_D w ∂P) ≤
        (∫ w, empiricalRisk n Xᵢ ℓ w ω ∂P) +
          Real.sqrt (((klDivergenceW P μ).toReal + log (1 / δ)) / (2 * n))} := by
  let a : ℝ := (klDivergenceW P μ).toReal + log (1 / δ)
  let lam0 : ℝ := Real.sqrt (8 * a / (n : ℝ))
  have ha : 0 < a := by
    have hlog : 0 < log (1 / δ) := by
      have h : 1 < 1 / δ := one_lt_one_div hδ0 hδ1
      exact Real.log_pos h
    linarith
  have hlam0 : 0 < lam0 := by
    dsimp only [lam0]
    exact Real.sqrt_pos.mpr (div_pos (mul_pos (by norm_num) ha) (Nat.cast_pos.mpr C.hn0))
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr C.hn0.ne'
  have h_moment := posteriorMomentBound C hPQ hL_D_int hℓ_w_int hllr hL_D_meas hℓ_prod lam0 hlam0
  let g : Ω → ℝ := fun ω =>
    exp (lam0 * ((n : ℝ) * (∫ w, L_D w ∂P - ∫ w, empiricalRisk n Xᵢ ℓ w ω ∂P)))
  have hg_nonneg : ∀ᵐ ω ∂PΩ, 0 ≤ g ω := Filter.Eventually.of_forall (fun ω => exp_nonneg _)
  have hg_int : Integrable g PΩ := by
    simpa only [g] using (integrable_posteriorExp C lam0 hlam0 hL_D_int hℓ_w_int hℓ_prod)
  have h_markov := expMarkov hg_int hg_nonneg (by positivity) h_moment hδ0
  let M : ℝ := exp ((klDivergenceW P μ).toReal + lam0 ^ 2 * (n : ℝ) / 8) / δ
  have h_markov' : PΩ.real {ω | M ≤ g ω} ≤ δ := by
    simpa only [M, g] using h_markov
  have h_good : PΩ.real {ω | g ω ≤ M} ≥ (1 : ℝ) - δ := by
    have hsub : {ω | g ω ≤ M} = {ω | M < g ω}ᶜ := by
      ext ω
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
      exact (not_lt (α := ℝ)).symm
    rw [hsub]
    have h_neg : PΩ.real {ω | M < g ω} ≤ δ := by
      have hmono : PΩ.real {ω | M < g ω} ≤ PΩ.real {ω | M ≤ g ω} := by
        refine measureReal_mono ?_
        intro ω hω
        exact le_of_lt (by simpa only [Set.mem_setOf_eq] using hω)
      exact le_trans hmono h_markov'
    have h_comp : PΩ.real {ω | M < g ω}ᶜ = 1 - PΩ.real {ω | M < g ω} := by
      have hc : PΩ.real {ω | M < g ω}ᶜ = PΩ.real Set.univ - PΩ.real {ω | M < g ω} :=
        measureReal_compl₀ (by
          exact nullMeasurableSet_lt measurable_const.aemeasurable hg_int.aemeasurable)
      have huniv : PΩ.real Set.univ = 1 := probReal_univ
      rwa [huniv] at hc
    linarith
  have h_implies : ∀ ω, g ω ≤ M →
      (∫ w, L_D w ∂P) ≤ (∫ w, empiricalRisk n Xᵢ ℓ w ω ∂P) +
        Real.sqrt (((klDivergenceW P μ).toReal + log (1 / δ)) / (2 * n)) := by
    intro ω hω
    let xp : ℝ := (∫ w, L_D w ∂P) - (∫ w, empiricalRisk n Xᵢ ℓ w ω ∂P)
    have hX : exp (lam0 * ((n : ℝ) * xp)) ≤ M := by simpa only [xp, M, g] using hω
    have hstep1 : lam0 * ((n : ℝ) * xp) ≤
        (klDivergenceW P μ).toReal + lam0 ^ 2 * (n : ℝ) / 8 + log (1 / δ) := by
      have hlog' : exp (lam0 * ((n : ℝ) * xp)) ≤
          exp ((klDivergenceW P μ).toReal + lam0 ^ 2 * (n : ℝ) / 8) / δ := by
        simpa only [M] using hX
      have hlog1 : exp ((klDivergenceW P μ).toReal + lam0 ^ 2 * (n : ℝ) / 8) / δ =
          exp ((klDivergenceW P μ).toReal + lam0 ^ 2 * (n : ℝ) / 8 + log (1 / δ)) := by
        rw [div_eq_mul_inv]
        conv_lhs =>
          rw [show δ⁻¹ = exp (log (1 / δ)) by
            rw [← one_div, exp_log (by positivity : 0 < 1 / δ)]]
        rw [← exp_add]
      have : exp (lam0 * ((n : ℝ) * xp)) ≤
          exp ((klDivergenceW P μ).toReal + lam0 ^ 2 * (n : ℝ) / 8 + log (1 / δ)) := by
        simpa only [hlog1] using hlog'
      exact exp_le_exp.mp this
    have hstep2 : lam0 * ((n : ℝ) * xp) ≤ a + lam0 ^ 2 * (n : ℝ) / 8 := by
      dsimp only [a] at *
      linarith
    have hstep3 : xp ≤ a / (lam0 * (n : ℝ)) + lam0 / 8 := by
      have hln : 0 < lam0 * (n : ℝ) := mul_pos hlam0 (Nat.cast_pos.mpr C.hn0)
      have hdiv : lam0 * ((n : ℝ) * xp) / (lam0 * (n : ℝ)) ≤
          (a + lam0 ^ 2 * (n : ℝ) / 8) / (lam0 * (n : ℝ)) :=
        div_le_div_of_nonneg_right hstep2 hln.le
      have hcancel : lam0 * ((n : ℝ) * xp) / (lam0 * (n : ℝ)) = xp := by
        field_simp [hlam0.ne', hn_ne]
      have hsplit : (a + lam0 ^ 2 * (n : ℝ) / 8) / (lam0 * (n : ℝ)) =
          a / (lam0 * (n : ℝ)) + lam0 / 8 := by
        field_simp [hlam0.ne', hn_ne]
      rwa [hcancel, hsplit] at hdiv
    have hfinal : xp ≤ Real.sqrt (a / (2 * n)) := by
      have hopt := mcAllesterOptimization a (n : ℝ) ha (Nat.cast_pos.mpr C.hn0)
      have hopt' : a / (lam0 * (n : ℝ)) + lam0 / 8 = Real.sqrt (a / (2 * n)) := by
        simpa only [lam0] using hopt
      linarith
    dsimp only [xp, a] at hfinal
    linarith
  have h_big : {ω | (∫ w, L_D w ∂P) ≤ (∫ w, empiricalRisk n Xᵢ ℓ w ω ∂P) +
      Real.sqrt (((klDivergenceW P μ).toReal + log (1 / δ)) / (2 * n))} ⊇
    {ω | g ω ≤ M} := by
    intro ω hω
    exact h_implies ω hω
  exact le_trans h_good (measureReal_mono h_big)

end

end LeanSharp
