/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Theory.Robustness.PacBayes
import LeanSharp.Theory.Robustness.PacBayesMcAllesterBound

/-!
# ZSharp McAllester Instantiation

This module instantiates the finite-sample McAllester bound on the Z-Score filtered
objective. The Z-Score sharpness predicate `ZSharpPacBayesBound` gives a pointwise
sharpness bound on the population risk (tightened by the filter's gradient
contraction), while `pacBayesMcAllesterBound` gives the sample-confidence bound.
On the McAllester good event both hold, so the posterior risk is bounded by the
empirical risk plus the *better* of the two penalties.

## Main Theorems

* `zSharpMcAllesterInstantiation`: with probability at least `1 - δ` over the sample,
  the posterior population risk is at most the empirical risk plus the minimum of the
  √KL sample term and the filtered-sharpness term.
-/

namespace LeanSharp

open MeasureTheory ProbabilityTheory Real

noncomputable section

variable {ι : Type*} [Fintype ι]
variable {Ω X : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  {PΩ : Measure Ω} [IsProbabilityMeasure PΩ]
  {D : Measure X} [IsProbabilityMeasure D]
  {n : ℕ} {Xᵢ : Fin n → Ω → X}
  {ℓ : W ι → X → ℝ} {L_D : W ι → ℝ}

/-- **ZSharp-McAllester Instantiation**: with probability at least `1 - δ` over the
    i.i.d. sample, the posterior population risk is bounded by the empirical risk plus
    the better of the √KL sample term `√((KL + log(1/δ)) / (2n))` and the Z-Score
    filtered-sharpness penalty `∫ ‖filteredGradient ∇L_S‖ ρ dP + C`.

    **Proof**: `pacBayesMcAllesterBound` yields the √KL term on the good event, while
    `z_sharp_pac_bayes_expected` integrates the pointwise `ZSharpPacBayesBound` into the
    sharpness penalty; both hold simultaneously, so `le_min` bounds the posterior risk
    by their minimum. -/
theorem zSharpMcAllesterInstantiation (C : RiskExcessCtx PΩ D n Xᵢ ℓ L_D)
    (P μ : Measure (W ι)) [IsProbabilityMeasure P] [IsProbabilityMeasure μ] [SigmaFinite μ]
    (hPQ : P ≪ μ)
    (hL_D_int : Integrable L_D P) (hℓ_w_int : ∀ x, Integrable (fun w => ℓ w x) P)
    (hllr : Integrable (llr P μ) P) (hL_D_meas : Measurable L_D)
    (hℓ_prod : Measurable (fun p : W ι × X => ℓ p.1 p.2))
    (ρ z c0 : ℝ)
    (hZSharp : ∀ w ω,
      ZSharpPacBayesBound L_D (fun u => empiricalRisk n Xᵢ ℓ u ω) w ρ z c0)
    (hZSharp_int : ∀ ω, Integrable (fun w =>
      ‖filteredGradient (gradient (fun u => empiricalRisk n Xᵢ ℓ u ω) w) z‖ * ρ) P)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (hKL : 0 < (klDivergenceW P μ).toReal) :
    (1 : ℝ) - δ ≤
      PΩ.real {ω |
        (∫ w, L_D w ∂P) ≤
          min (∫ w, empiricalRisk n Xᵢ ℓ w ω ∂P +
                Real.sqrt (((klDivergenceW P μ).toReal + log (1 / δ)) / (2 * n)))
              ((∫ w, empiricalRisk n Xᵢ ℓ w ω ∂P) +
                (∫ w, ‖filteredGradient
                  (gradient (fun u => empiricalRisk n Xᵢ ℓ u ω) w) z‖ * ρ ∂P) + c0)} := by
  let term : ℝ :=
    Real.sqrt (((klDivergenceW P μ).toReal + log (1 / δ)) / (2 * n))
  let G : Set Ω :=
    {ω | (∫ w, L_D w ∂P) ≤ (∫ w, empiricalRisk n Xᵢ ℓ w ω ∂P) + term}
  have h_mcallester := pacBayesMcAllesterBound C P μ hPQ hL_D_int hℓ_w_int hllr
    hL_D_meas hℓ_prod δ hδ0 hδ1 hKL
  have h_zsharp : ∀ ω, (∫ w, L_D w ∂P) ≤
      (∫ w, empiricalRisk n Xᵢ ℓ w ω ∂P) +
        (∫ w, ‖filteredGradient
          (gradient (fun u => empiricalRisk n Xᵢ ℓ u ω) w) z‖ * ρ ∂P) + c0 :=
    fun ω => z_sharp_pac_bayes_expected P ρ z c0 (fun w => hZSharp w ω) hL_D_int
      (integrable_empiricalRisk P hℓ_w_int ω) (hZSharp_int ω)
  have h_good : ∀ ω, ω ∈ G →
      (∫ w, L_D w ∂P) ≤
        min (∫ w, empiricalRisk n Xᵢ ℓ w ω ∂P + term)
            ((∫ w, empiricalRisk n Xᵢ ℓ w ω ∂P) +
              (∫ w, ‖filteredGradient
                (gradient (fun u => empiricalRisk n Xᵢ ℓ u ω) w) z‖ * ρ ∂P) + c0) := by
    intro ω hω
    have h1 : (∫ w, L_D w ∂P) ≤ (∫ w, empiricalRisk n Xᵢ ℓ w ω ∂P) + term := by
      simpa only [G, term] using hω
    exact (le_min_iff).mpr ⟨h1, h_zsharp ω⟩
  have h_contain : {ω |
      (∫ w, L_D w ∂P) ≤
        min (∫ w, empiricalRisk n Xᵢ ℓ w ω ∂P + term)
            ((∫ w, empiricalRisk n Xᵢ ℓ w ω ∂P) +
              (∫ w, ‖filteredGradient
                (gradient (fun u => empiricalRisk n Xᵢ ℓ u ω) w) z‖ * ρ ∂P) + c0)} ⊇ G := by
    intro ω hω
    exact h_good ω hω
  have h_mcallester' : (1 : ℝ) - δ ≤ PΩ.real G := by
    simpa only [G, term] using h_mcallester
  exact le_trans h_mcallester' (measureReal_mono h_contain)

end

end LeanSharp
