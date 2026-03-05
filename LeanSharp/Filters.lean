import LeanSharp.Sam
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Sum

/-!
# Z-Score Gradient Filtering

The core of ZSharp is the statistical filtering of gradient tensors.
Given a gradient vector `g ∈ ℝ^d`, we compute its mean `μ` and standard
deviation `σ`.

We then apply a binary mask `M` parameterized by the z-score threshold `z`:
M_i = 1 if |g_i - μ| ≥ z * σ
M_i = 0 if |g_i - μ| < z * σ

Finally, the filtered gradient is `g ⊙ M` (element-wise multiplication).
-/

namespace LeanSharp

open BigOperators

variable {d : ℕ} [Fact (0 < d)]

/-- The mean of a vector in `W = ℝ^d`. -/
noncomputable def vector_mean (g : W d) : ℝ :=
  (∑ i : Fin d, g i) / (d : ℝ)

/-- The variance of a vector in `W = ℝ^d`. -/
noncomputable def vector_variance (g : W d) : ℝ :=
  let μ := vector_mean g
  (∑ i : Fin d, (g i - μ)^2) / (d : ℝ)

/-- The standard deviation `σ` is the square root of the variance. -/
noncomputable def vector_std (g : W d) : ℝ :=
  Real.sqrt (vector_variance g)

/-- The Z-score Mask operator. Returns a new vector in `W` where each component
    is 1 if the condition $|g_i - μ| ≥ z * σ$ is met, and 0 otherwise. -/
noncomputable def z_score_mask (g : W d) (z : ℝ) : W d :=
  let μ := vector_mean g
  let σ := vector_std g
  WithLp.equiv 2 (Fin d → ℝ) |>.symm (fun i => if |g i - μ| ≥ z * σ then 1 else 0)

/-- Element-wise multiplication (Hadamard product) of vectors in $W$. -/
noncomputable def hadamard (a b : W d) : W d :=
  WithLp.equiv 2 (Fin d → ℝ) |>.symm (fun i => a i * b i)

/-- The fully filtered gradient used in the parameter update. -/
noncomputable def filtered_gradient (g : W d) (z : ℝ) : W d :=
  hadamard g (z_score_mask g z)

end LeanSharp
