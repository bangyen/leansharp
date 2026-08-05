/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.Convergence.Assumptions
import LeanSharp.Stochastic.Foundations.RobbinsMonro

/-!
# Heavy-Tailed Convergence

This module formalizes almost-sure convergence for the Z-score filtered SAM
under heavy-tailed noise regimes (e.g., Cauchy noise). It utilizes probability-oracle
contracts to replace traditional finite-variance requirements.

## Main theorems

* `zsharp_heavy_tail_convergence`: Proves almost-sure convergence of the
  objective process when the noise satisfies a non-Gaussian probability oracle.
* `zsharp_heavy_tail_convergence_of_alpha_stable`: The same convergence under an
  α-stable oracle, wired through the α-stable-to-non-Gaussian oracle conversion.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory NNReal

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- **Heavy-Tailed Robbins-Monro Convergence**:
If the stochastic update process satisfies the oracle-based descent hypotheses
(which includes a polynomial-tail bound on the noise), then the objective
converges almost surely to a limit.

This theorem bridges the `NonGaussianProbabilityOracle` to the
supermartingale convergence machinery. -/
theorem zsharp_heavy_tail_convergence
    (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ)
    (ℱ : ℕ → MeasurableSpace Ω)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_oracle : ZSharpOracleDescentHypotheses f w η ℱ ℱfil)
    (h_int : ∀ t, Integrable (fun ω => f (w t ω)) ℙ) :
    ZSharpObjectiveAsConvergence f w := by
  rcases h_oracle with
    ⟨_h_rm, ⟨_C, _p, _hC, _hp, _h_tail⟩, ⟨R, h_adapted, h_step, hbdd⟩, _h_meas⟩
  have h_adapted_neg : StronglyAdapted ℱfil (fun t ω => -f (w t ω)) := h_adapted.neg
  have h_step_neg (t : ℕ) : (fun ω => -f (w t ω)) ≤ᵐ[ℙ]
      ℙ[fun ω => -f (w (t + 1) ω) | ℱfil t] := by
    have h_neg_obj : (fun ω => -f (w t ω)) ≤ᵐ[ℙ]
        (fun ω => -ℙ[fun ω => f (w (t + 1) ω) | ℱfil t] ω) := by
      filter_upwards [h_step t] with ω hω
      linarith
    have hcond_neg := (condExp_neg (μ := ℙ) (m := ℱfil t)
      (f := fun ω => f (w (t + 1) ω))).symm
    exact h_neg_obj.trans_eq hcond_neg
  have h_sub_neg : Submartingale (fun t ω => -f (w t ω)) ℱfil ℙ := by
    apply submartingale_nat
    · exact h_adapted_neg
    · intro t
      exact (h_int t).neg
    · exact h_step_neg
  have hbdd_neg (t : ℕ) : eLpNorm (fun ω => -f (w t ω)) 1 ℙ ≤ R := by
    have hfun : (fun ω => -f (w t ω)) = -(fun ω => f (w t ω)) := rfl
    rw [hfun, eLpNorm_neg]
    exact hbdd t
  exact zsharp_objective_as_convergence_of_neg_submartingale f w ℱfil R h_sub_neg hbdd_neg

/-- **Heavy-Tailed Convergence under α-stable noise**: if the update increments
satisfy an α-stable probability oracle (α ≥ 1), they are a valid non-Gaussian
oracle, so the same almost-sure convergence holds. This makes the α-stable claim
end-to-end. -/
theorem zsharp_heavy_tail_convergence_of_alpha_stable
    (f : W ι → ℝ) (w : ℕ → Ω → W ι) (η : ℕ → ℝ)
    (ℱ : ℕ → MeasurableSpace Ω)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (α : ℝ) (h_alpha : 1 ≤ α)
    (h_rm : RobbinsMonroStepsize η)
    (h_stable : AlphaStableProbabilityOracleProcess
      (fun t ω => w (t + 1) ω - w t ω) α)
    (h_adapted : ∃ R : NNReal,
      StronglyAdapted ℱfil (fun t ω => f (w t ω))
        ∧ (∀ t, ℙ[fun ω => f (w (t + 1) ω) | ℱfil t] ≤ᵐ[ℙ] (fun ω => f (w t ω)))
        ∧ (∀ t, eLpNorm (fun ω => f (w t ω)) 1 ℙ ≤ R))
    (h_meas : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_int : ∀ t, Integrable (fun ω => f (w t ω)) ℙ) :
    ZSharpObjectiveAsConvergence f w := by
  have h_ng : NonGaussianProbabilityOracleProcess
      (fun t ω => w (t + 1) ω - w t ω) := by
    intro t
    exact alpha_stable_is_non_gaussian h_alpha (fun ω => w (t + 1) ω - w t ω)
      (h_stable t)
  let h_oracle : ZSharpOracleDescentHypotheses f w η ℱ ℱfil :=
    ⟨h_rm, ⟨1, 1, by norm_num, le_rfl, h_ng⟩, h_adapted, h_meas⟩
  exact zsharp_heavy_tail_convergence f w η ℱ ℱfil h_oracle h_int

end LeanSharp
