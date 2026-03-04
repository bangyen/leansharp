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

variable {d : ℕ}

/-- To compute statistics, we need `d` as a real number. -/
noncomputable def d_real (d : ℕ) : ℝ := (d : ℝ)

/-- The mean of a vector in `W = ℝ^d`. -/
noncomputable def vector_mean (g : W d) : ℝ :=
  (∑ i : Fin d, g i) / d_real d

/-- The variance of a vector in `W = ℝ^d`. -/
noncomputable def vector_variance (g : W d) : ℝ :=
  let μ := vector_mean g
  (∑ i : Fin d, (g i - μ)^2) / d_real d

/-- The standard deviation `σ` is the square root of the variance. -/
noncomputable def vector_std (g : W d) : ℝ :=
  Real.sqrt (vector_variance g)

/-- The Z-score Mask operator. Returns a new vector in `W` where each component
    is 1 if the condition is met, and 0 otherwise. -/
noncomputable def z_score_mask (g : W d) (z : ℝ) : W d :=
  let μ := vector_mean g
  let σ := vector_std g
  WithLp.equiv 2 (Fin d → ℝ) |>.symm (fun i => if |g i - μ| ≥ z * σ then 1 else 0)

/-- Element-wise multiplication (Hadamard product) of vectors in `W`. -/
noncomputable def hadamard (a b : W d) : W d :=
  WithLp.equiv 2 (Fin d → ℝ) |>.symm (fun i => a i * b i)

/-- The fully filtered gradient used in the parameter update. -/
noncomputable def filtered_gradient (g : W d) (z : ℝ) : W d :=
  hadamard g (z_score_mask g z)

/-!
## ZSharp SAM Update Rule

We can now define the full formulation for Z-Score SAM.
The standard update `w_{t+1} = w_t - η ∇L(w_t + ε*(w_t))`
becomes `w_{t+1} = w_t - η * filtered_gradient(∇L(w_t + ε*(w_t)), z)`
-/

/-- The full parameter update given learning rate `η`. -/
noncomputable def zsharp_sam_update (L : W d → ℝ) (w : W d) (η : ℝ) (ρ : ℝ) (z : ℝ) : W d :=
  let ε := sam_perturbation L w ρ
  let g_adv := gradient L (w + ε)
  let g_filtered := filtered_gradient g_adv z
  w - η • g_filtered
