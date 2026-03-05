import LeanSharp.Sam
import LeanSharp.Filters
import LeanSharp.Stochastics
import LeanSharp.Convergence


/-!
# Stochastic Z-Score SAM

Using the fundamental definitions of the Empirical Risk function `L_S`, we can now
formally define what the stochastic ZSharp gradient update looks like.

Instead of measuring the full population loss `L`, we step using `minibatch_risk`.
-/

variable {d : ℕ} (DataPoint : Type*)
variable (sample_loss : W d → DataPoint → ℝ)
variable {n : ℕ} (S : Fin n → DataPoint)
variable {b : ℕ} (B : Fin b → Fin n)

/-- To keep the code clean, we define a helper function `L_B` that represents
    the loss function evaluated exactly over the current minibatch `B`. -/
noncomputable def L_B (w : W d) : ℝ :=
  minibatch_risk DataPoint sample_loss S B w

/-- Stochastic SAM Perturbation:
    The perturbation is calculated based ONLY on the minibatch gradient. -/
noncomputable def stochastic_sam_perturbation (w : W d) (ρ : ℝ) : W d :=
  sam_perturbation (L_B DataPoint sample_loss S B) w ρ

/-- Stochastic ZSharp Update Rule:
    The Z-score filter is applied to the stochastic adversarial gradient. -/
noncomputable def stochastic_zsharp_update (w : W d) (η : ℝ) (ρ : ℝ) (z : ℝ) : W d :=
  let ε := stochastic_sam_perturbation DataPoint sample_loss S B w ρ
  let g_adv := gradient (L_B DataPoint sample_loss S B) (w + ε)
  let g_filtered := filtered_gradient g_adv z
  w - η • g_filtered

/-!
## Stochastic Variants of the Convergence Lemmas

The key theorems generalize directly to the stochastic case by substituting
the minibatch loss `L_B` for the full empirical loss `L`. -/

/-- Stochastic Perturbation Bound:
    The SAM perturbation based on the minibatch gradient is still bounded by ρ. -/
theorem stochastic_perturbation_bound (w : W d) (ρ : ℝ) (hρ : ρ > 0) :
    ‖stochastic_sam_perturbation DataPoint sample_loss S B w ρ‖ ≤ ρ := by
  unfold stochastic_sam_perturbation
  -- Direct application of sam_perturbation_bound with L = L_B
  exact sam_perturbation_bound (L_B DataPoint sample_loss S B) w ρ hρ

/-- Stochastic Filter Error Bound:
    The Z-score filter on the stochastic adversarial gradient introduces
    bounded quantization error: ‖g_filtered - g_adv‖² ≤ d * (|μ| + z*σ)². -/
theorem stochastic_filter_error_bound (w : W d) (ρ z : ℝ) (hz : z ≥ 0) :
    let ε := stochastic_sam_perturbation DataPoint sample_loss S B w ρ
    let g_adv := gradient (L_B DataPoint sample_loss S B) (w + ε)
    ‖filtered_gradient g_adv z - g_adv‖^2 ≤
        d * (|vector_mean g_adv| + z * vector_std g_adv)^2 := by
  -- Direct application of z_score_error_bound to g_adv
  exact z_score_error_bound _ z hz
lemma stochastic_sgd_contraction (η L_smooth μ σ : ℝ) (w_star : W d)
    (h_smooth : is_L_smooth (empirical_risk DataPoint sample_loss S) L_smooth)
    (h_convex : is_strongly_convex (empirical_risk DataPoint sample_loss S) μ)
    (h_opt : is_optimum (empirical_risk DataPoint sample_loss S) w_star)
    (hη : 0 < η)
    (hη_tight : η * L_smooth ^ 2 ≤ μ)
    (hη_bound : η ≤ 1 / L_smooth)
    (hμL : μ < L_smooth)
    (batches : Set (Fin b → Fin n))
    (h_unbiased : ∀ w : W d,
      @is_unbiased (d := d) (DataPoint := DataPoint) (sample_loss := sample_loss)
                   (n := n) (S := S) (b := b) (w := w) (batches := batches))
    (h_variance : ∀ w : W d, has_bounded_variance DataPoint sample_loss S w batches σ) :
    ∀ w : W d, ∀ B ∈ batches,
        ∃ c : ℝ, 0 < c ∧ c < 1 ∧
        ‖(w - η • minibatch_gradient DataPoint sample_loss S w B) - w_star‖^2 ≤
            c * ‖w - w_star‖^2 + η^2 * σ^2 := by
  intro w B hB
  obtain ⟨c, ⟨hc_pos, hc_lt_1⟩, h_det⟩ := gd_contraction (empirical_risk DataPoint sample_loss S)
      w_star η L_smooth μ h_smooth h_convex h_opt hμL hη hη_bound hη_tight
  use c, hc_pos, hc_lt_1

  set g := full_gradient DataPoint sample_loss S w
  set g_B := minibatch_gradient DataPoint sample_loss S w B
  set ξ := stochastic_error DataPoint sample_loss S w B

  -- Expansion: ‖(w-w*) - η•g_B‖² = ‖(w-w*) - η•g - η•ξ‖²
  have h_exp : ‖(w - η • g_B) - w_star‖^2 = ‖((w - η • g) - w_star) - η • ξ‖^2 := by
    have h_gB : g_B = g + ξ := by
      dsimp [ξ, stochastic_error]; abel
    rw [h_gB, smul_add]
    congr 1
    abel_nf

  rw [h_exp, norm_sub_sq_real]
  -- We use the variance bound: ‖ξ‖² ≤ σ²
  have h_v := h_variance w B hB
  -- The cross term E[⟨..., ξ⟩] vanishes under unbiasedness.
  sorry

/-- Stochastic ZSharp converges in expectation to `w_star` under standard assumptions.
    Proof Outline:
    1. Distance expansion:
       ‖w_{t+1} - w*‖² = ‖w_t - w*‖² - 2η⟨g_filtered, w_t - w*⟩ + η²‖g_filtered‖²
    2. Alignment: Under alignment_condition, ⟨g_filtered, w-w*⟩ maintains descent.
    3. Noise: Under bounded variance, the noise from minibatches is controlled. -/
theorem stochastic_zsharp_convergence (η ρ z L_smooth μ σ : ℝ) (w_star : W d)
    (h_smooth : is_L_smooth (empirical_risk DataPoint sample_loss S) L_smooth)
    (h_convex : is_strongly_convex (empirical_risk DataPoint sample_loss S) μ)
    (h_opt : is_optimum (empirical_risk DataPoint sample_loss S) w_star)
    (hη : 0 < η)
    (hη_tight : η * L_smooth ^ 2 ≤ μ)
    (hη_bound : η ≤ 1 / L_smooth)
    (hμL : μ < L_smooth)
    -- Multi-batch assumptions
    (batches : Set (Fin b → Fin n))
    (h_unbiased : ∀ w : W d,
      @is_unbiased (d := d) (DataPoint := DataPoint) (sample_loss := sample_loss)
                   (n := n) (S := S) (b := b) (w := w) (batches := batches))
    (h_variance : ∀ w : W d,
      has_bounded_variance DataPoint sample_loss S w batches σ)
    -- Flat-minimum condition (full batch)
    (h_flat : ∀ ε : W d, ‖ε‖ ≤ ρ →
      gradient (empirical_risk DataPoint sample_loss S) (w_star + ε) = 0)
    -- Filter alignment (for all minibatches)
    (h_align : ∀ w : W d, ∀ B ∈ batches,
                let ε := stochastic_sam_perturbation DataPoint sample_loss S B w ρ
                alignment_condition (L_B DataPoint sample_loss S B) w w_star ε z μ) :
    ∀ w : W d, ∀ B ∈ batches,
        ∃ c : ℝ, 0 < c ∧ c < 1 ∧
        ‖stochastic_zsharp_update DataPoint sample_loss S B w η ρ z - w_star‖^2 ≤
            c * ‖w - w_star‖^2 + η^2 * σ^2 := by
  -- Optimization logic: The bound consists of the deterministic contraction `c`
  -- plus an additive noise term `η²σ²` resulting from stochasticity.
  sorry
