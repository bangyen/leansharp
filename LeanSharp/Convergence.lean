import LeanSharp.Landscape
import LeanSharp.Sam
import LeanSharp.Filters
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Phase 4: ZSharp Convergence Bound

One of the open research questions for SAM variants is how modifying the
adversarial gradient affects the theoretical convergence rate under standard
optimization assumptions.

Here, we mathematically formalize the conditions required to prove that
ZSharp converges on a well-behaved (convex, smooth) landscape.
-/

variable {d : ℕ}

-- The loss function we are optimizing.
variable (L : W d → ℝ)

-- The unique global minimum of the strongly convex function.
variable (w_star : W d)

/-- We assume the loss function is L-smooth.
    This means the gradient is Lipschitz continuous with constant `L_smooth`.
    ‖∇L(w) - ∇L(v)‖ ≤ L_smooth * ‖w - v‖ -/
def is_L_smooth (L_smooth : ℝ) : Prop :=
  L_smooth > 0 ∧ ∀ w v : W d,
    ‖gradient L w - gradient L v‖ ≤ L_smooth * ‖w - v‖

/-- We assume the loss function is μ-strongly convex.
    This provides a strong lower bound on the function's curvature.
    L(v) ≥ L(w) + ⟨∇L(w), v - w⟩ + (μ/2)‖v - w‖² -/
def is_strongly_convex (μ : ℝ) : Prop :=
  μ > 0 ∧ ∀ w v : W d,
    L v ≥ L w + @inner ℝ (W d) _ (gradient L w) (v - w) + (μ / 2) * ‖v - w‖^2

/-!
## ZSharp Optimization Step

We define a single step of the non-stochastic ZSharp optimizer.
-/

/-- The parameter update for a single step of ZSharp.
    w_{t+1} = w_t - η * filtered_gradient(∇L(w_t + ε), z) -/
noncomputable def zsharp_step (w : W d) (η ρ z : ℝ) : W d :=
  let ε := sam_perturbation L w ρ
  let g_adv := gradient L (w + ε)
  let g_filtered := filtered_gradient g_adv z
  w - η • g_filtered

/-!
## Convergence Theorem Statement

If we were to write a full machine learning theory paper, the ultimate goal
would be to prove the following theorem bounding the distance to the minimum
at step `t+1` based on the parameters at step `t`.

Since ZSharp introduces a non-linear thresholding operator (the Z-score filter),
this proof requires bounding the quantization error introduced by `filtered_gradient`.
-/

/-- The formal statement of ZSharp convergence under standard assumptions.
    It posits that there exists a contraction factor `c ∈ (0, 1)` such that
    the distance to the optimal parameters decreases geometrically. -/
def zsharp_convergence_holds (η ρ z L_smooth μ : ℝ) : Prop :=
  is_L_smooth L L_smooth →
  is_strongly_convex L μ →
  -- Assumptions on learning rate and SAM radius
  η > 0 ∧ ρ > 0 →
  -- The bound statement:
  ∃ c : ℝ, 0 < c ∧ c < 1 ∧
    ∀ w : W d, ‖zsharp_step L w η ρ z - w_star‖^2 ≤ c * ‖w - w_star‖^2
