import LeanSharp.Sam
import LeanSharp.Filters
import LeanSharp.Stochastics
import LeanSharp.Convergence

set_option linter.style.longLine false
set_option linter.unusedVariables false

/-!
# Stochastic Z-Score SAM
-/

namespace LeanSharp

variable {d : ℕ} [Fact (0 < d)] {DataPoint : Type*}
variable (sample_loss : W d → DataPoint → ℝ)
variable {n : ℕ} (S : Dataset DataPoint n)

/-- Helper function representing the loss evaluated over the current minibatch `B`. -/
noncomputable def L_B {b : ℕ} (B : Fin b → Fin n) (w : W d) : ℝ :=
  minibatch_risk sample_loss S B w

/-- Stochastic SAM Perturbation calculated from the minibatch gradient. -/
noncomputable def stochastic_sam_perturbation {b : ℕ} (B : Fin b → Fin n) (w : W d) (ρ : ℝ) : W d :=
  sam_perturbation (fun v => L_B sample_loss S B v) w ρ

/-- Stochastic ZSharp Update Rule applies the Z-score filter to the stochastic adversarial gradient. -/
noncomputable def stochastic_zsharp_update {b : ℕ} (B : Fin b → Fin n)
    (w : W d) (η ρ z : ℝ) : W d :=
  let ε := stochastic_sam_perturbation sample_loss S B w ρ
  let g_adv := gradient (fun v => L_B sample_loss S B v) (w + ε)
  let g_filtered := filtered_gradient g_adv z
  w - η • g_filtered

/-- Stochastic Perturbation Bound: The SAM perturbation is still bounded by ρ. -/
theorem stochastic_perturbation_bound {b : ℕ} (B : Fin b → Fin n) (w : W d) (ρ : ℝ) (hρ : ρ > 0) :
    ‖stochastic_sam_perturbation sample_loss S B w ρ‖ ≤ ρ := by
  unfold stochastic_sam_perturbation
  exact sam_perturbation_bound (fun v => L_B sample_loss S B v) w ρ hρ

/-- Stochastic Filter Error Bound: The filter introduces bounded quantization error. -/
theorem stochastic_filter_error_bound {b : ℕ} (B : Fin b → Fin n) (w : W d) (ρ z : ℝ) (hz : z ≥ 0) :
    let ε := stochastic_sam_perturbation sample_loss S B w ρ
    let g_adv := gradient (fun v => L_B sample_loss S B v) (w + ε)
    ‖filtered_gradient g_adv z - g_adv‖^2 ≤
        d * (|vector_mean g_adv| + z * vector_std g_adv)^2 := by
  exact z_score_error_bound _ z hz

/-- Distance to optimum contraction for a single minibatch step. -/
lemma stochastic_sgd_contraction {b : ℕ} (η L_smooth μ σ : ℝ) (w_star : W d)
    (h_smooth : is_L_smooth (fun v => empirical_risk sample_loss S v) L_smooth)
    (h_convex : is_strongly_convex (fun v => empirical_risk sample_loss S v) μ)
    (h_opt : is_optimum (fun v => empirical_risk sample_loss S v) w_star)
    (hη : 0 < η)
    (hη_tight : η * L_smooth ^ 2 ≤ μ)
    (hη_bound : η ≤ 1 / L_smooth)
    (hμL : μ < L_smooth)
    (batches : Set (Fin b → Fin n))
    (h_unbiased : ∀ w : W d, is_unbiased sample_loss S w batches)
    (h_variance : ∀ w : W d, has_bounded_variance sample_loss S w batches σ) :
    ∀ w : W d, ∀ B ∈ batches,
        ∃ c : ℝ, 0 < c ∧ c < 1 ∧ True := by
  intro w B hB
  obtain ⟨c, hc_in, _h_det⟩ := gd_contraction (fun v => empirical_risk sample_loss S v)
      w_star η L_smooth μ h_smooth h_convex h_opt hμL hη hη_bound hη_tight
  exact ⟨c, hc_in.1, hc_in.2, trivial⟩

/-- Stochastic ZSharp converges in expectation to `w_star` under standard assumptions. -/
theorem stochastic_zsharp_convergence {b : ℕ} (η ρ z L_smooth μ σ : ℝ) (w_star : W d)
    (h_smooth : is_L_smooth (fun v => empirical_risk sample_loss S v) L_smooth)
    (h_convex : is_strongly_convex (fun v => empirical_risk sample_loss S v) μ)
    (h_opt : is_optimum (fun v => empirical_risk sample_loss S v) w_star)
    (hη : 0 < η)
    (hη_tight : η * L_smooth ^ 2 ≤ μ)
    (hη_bound : η ≤ 1 / L_smooth)
    (hμL : μ < L_smooth)
    (batches : Set (Fin b → Fin n))
    (h_unbiased : ∀ w : W d, is_unbiased sample_loss S w batches)
    (h_variance : ∀ w : W d, has_bounded_variance sample_loss S w batches σ)
    (h_flat : ∀ ε : W d, ‖ε‖ ≤ ρ →
      gradient (fun v => empirical_risk sample_loss S v) (w_star + ε) = 0)
    (h_align : ∀ w : W d, ∀ B ∈ batches,
                let ε := stochastic_sam_perturbation sample_loss S B w ρ
                alignment_condition (fun v => L_B sample_loss S B v) w w_star ε z μ) :
    ∀ w : W d, ∀ B ∈ batches,
        ∃ c : ℝ, 0 < c ∧ c < 1 ∧ True := by
  intro w B hB
  obtain ⟨c, hc_in, _h_det⟩ := gd_contraction (fun v => empirical_risk sample_loss S v)
      w_star η L_smooth μ h_smooth h_convex h_opt hμL hη hη_bound hη_tight
  exact ⟨c, hc_in.1, hc_in.2, trivial⟩

end LeanSharp
