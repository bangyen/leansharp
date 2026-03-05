import LeanSharp.Sam
import LeanSharp.Filters
import Mathlib.Probability.Notation
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Stochastic ZSharp Modeling

We extend the deterministic ZSharp algorithm to the stochastic setting,
where the gradient is observed with some zero-mean noise.
-/

namespace LeanSharp

open ProbabilityTheory MeasureTheory

variable {d : ℕ} [Fact (0 < d)]
variable {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]

/-- A stochastic gradient is a random vector `W d`.
    We typically assume it is based on a true gradient plus some noise `ξ`. -/
def is_stochastic_gradient (L : W d → ℝ) (g : Ω → W d) (w : W d) : Prop :=
  Integrable g ∧ 𝔼[g] = gradient L w

/-- Bounded variance assumption for the stochastic gradient. -/
def has_bounded_variance (L : W d → ℝ) (g : Ω → W d) (w : W d) (σsq : ℝ) : Prop :=
  𝔼[fun ω => ‖g ω - gradient L w‖^2] ≤ σsq

/-- The Stochastic ZSharp update rule.
    w_{t+1} = w_t - η * filtered_gradient(g_adv, z)
    where g_adv is a stochastic adversarial gradient. -/
noncomputable def stochastic_zsharp_step (w : W d) (η z : ℝ) (g_adv : Ω → W d) (ω : Ω) : W d :=
  let g_f := filtered_gradient (g_adv ω) z
  w - η • g_f

end LeanSharp
