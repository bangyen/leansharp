/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Stochastic.Convergence.HeavyTail
import LeanSharp.Stochastic.Foundations.Oracles

/-!
# Heavy-Tail Convergence Tests

This module verifies the wiring of almost-sure convergence under non-Gaussian,
heavy-tailed noise.

## Examples

* `cauchy_process_convergence_test`.
* `alpha_stable_convergence_test`.

## Theorems

* `alpha_stable_constant_noise`: A constant noise satisfies the α-stable oracle.
-/

namespace LeanSharp.Tests

open ProbabilityTheory MeasureTheory NNReal

variable {ι : Type*} [Fintype ι]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- **Cauchy Noise Test Witness**:
A simulated process that satisfies the `NonGaussianProbabilityOracle`.
This test verifies the wiring of almost-sure convergence. -/
example (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ)
    (ℱ : ℕ → MeasurableSpace Ω)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_oracle : ZSharpOracleDescentHypotheses f w η ℱ ℱfil)
    (h_int : ∀ t, Integrable (fun ω => f (w t ω)) ℙ) :
    ZSharpObjectiveAsConvergence f w := by
  apply zsharp_heavy_tail_convergence f w η ℱ ℱfil h_oracle h_int

/-- **Alpha-stable Noise Test Witness**: an α-stable oracle (α ≥ 1) is a valid
non-Gaussian oracle, so almost-sure convergence holds under α-stable increments. -/
example (f : W ι → ℝ)
    (w : ℕ → Ω → W ι) (η : ℕ → ℝ)
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
  exact zsharp_heavy_tail_convergence_of_alpha_stable f w η ℱ ℱfil α h_alpha
    h_rm h_stable h_adapted h_meas h_int

/-- A concrete (constant) noise satisfies the α-stable oracle with α = 1: the
polynomial-tail bound holds trivially for bounded noise. -/
lemma alpha_stable_constant_noise {Ω : Type*} [MeasureSpace Ω]
    [IsProbabilityMeasure (volume : Measure Ω)] (c : W ι) :
    AlphaStableProbabilityOracle (fun _ : Ω => c) 1 := by
  unfold AlphaStableProbabilityOracle
  refine ⟨by norm_num, by norm_num, ‖c‖ + 1, by positivity, ?_⟩
  intro r hr
  by_cases h_le : r ≤ ‖c‖
  · have h_event : normTailEvent (fun _ : Ω => c) r = Set.univ := by
      ext ω
      simp only [normTailEvent, Set.mem_setOf_eq, Set.mem_univ]
      exact Iff.intro (fun _ => trivial) (fun _ => h_le)
    rw [h_event]
    have hμ : (volume : Measure Ω) Set.univ = (1 : ENNReal) :=
      (inferInstance : IsProbabilityMeasure (volume : Measure Ω)).measure_univ
    rw [hμ]
    norm_num
    have h_r_le : r ≤ ‖c‖ + 1 := by nlinarith [h_le, norm_nonneg c]
    exact (one_le_div₀ hr).2 h_r_le
  · have h_event : normTailEvent (fun _ : Ω => c) r = ∅ := by
      ext ω
      simp only [normTailEvent, Set.mem_setOf_eq, Set.mem_empty_iff_false]
      exact Iff.intro (fun hc => h_le hc) (fun hf => False.elim hf)
    rw [h_event, measure_empty, ENNReal.toReal_zero]
    positivity

/-- The α-stable convergence theorem fires with a concrete bounded noise: the
increments are constant `c`, which satisfies the α-stable oracle, so the almost-sure
convergence claim is instantiated end-to-end. -/
example {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    (f : W ι → ℝ) (w : ℕ → Ω → W ι) (η : ℕ → ℝ)
    (ℱ : ℕ → MeasurableSpace Ω)
    (ℱfil : Filtration ℕ ‹MeasureSpace Ω›.toMeasurableSpace)
    (c : W ι)
    (h_inc : ∀ t, ∀ ω : Ω, w (t + 1) ω - w t ω = c)
    (h_rm : RobbinsMonroStepsize η)
    (h_adapted : ∃ R : NNReal,
      StronglyAdapted ℱfil (fun t ω => f (w t ω))
        ∧ (∀ t, ℙ[fun ω => f (w (t + 1) ω) | ℱfil t] ≤ᵐ[ℙ] (fun ω => f (w t ω)))
        ∧ (∀ t, eLpNorm (fun ω => f (w t ω)) 1 ℙ ≤ R))
    (h_meas : ∀ t, ℱ t ≤ ‹MeasureSpace Ω›.toMeasurableSpace)
    (h_int : ∀ t, Integrable (fun ω => f (w t ω)) ℙ) :
    ZSharpObjectiveAsConvergence f w := by
  have h_stable : AlphaStableProbabilityOracleProcess
      (fun t ω => w (t + 1) ω - w t ω) 1 := by
    intro t
    have h_fun : (fun ω : Ω => w (t + 1) ω - w t ω) = (fun _ : Ω => c) := by
      funext ω
      exact h_inc t ω
    change AlphaStableProbabilityOracle (fun ω : Ω => w (t + 1) ω - w t ω) 1
    rw [h_fun]
    exact alpha_stable_constant_noise c
  exact zsharp_heavy_tail_convergence_of_alpha_stable f w η ℱ ℱfil 1 (by norm_num)
    h_rm h_stable h_adapted h_meas h_int

end LeanSharp.Tests
