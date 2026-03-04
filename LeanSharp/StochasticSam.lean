import LeanSharp.Sam
import LeanSharp.Filters
import LeanSharp.Stochastics

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
noncomputable def stochastic_zsharp_update
    (w : W d) (η : ℝ) (ρ : ℝ) (z : ℝ) : W d :=
  let ε := stochastic_sam_perturbation DataPoint sample_loss S B w ρ
  let g_adv := gradient (L_B DataPoint sample_loss S B) (w + ε)
  let g_filtered := filtered_gradient g_adv z
  w - η • g_filtered
