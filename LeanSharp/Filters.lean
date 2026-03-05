import LeanSharp.Sam
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Sum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Z-Score Gradient Filtering

The core of ZSharp is the statistical filtering of gradient tensors.
Given a gradient vector `g ∈ ℝ^d`, we compute its mean `μ` and standard
deviation `σ`.
-/

namespace LeanSharp

open BigOperators

variable {d : ℕ} [Fact (0 < d)]

/-- The mean of a vector in `W = ℝ^d`. -/
noncomputable def vector_mean (g : W d) : ℝ :=
  (∑ i : Fin d, (WithLp.equiv 2 (Fin d → ℝ) g) i) / (d : ℝ)

/-- The variance of a vector in $W = ℝ^d$. -/
noncomputable def vector_variance (g : W d) : ℝ :=
  let μ := vector_mean g
  (∑ i : Fin d, ((WithLp.equiv 2 (Fin d → ℝ) g) i - μ)^2) / (d : ℝ)

/-- The standard deviation `σ` is the square root of the variance. -/
noncomputable def vector_std (g : W d) : ℝ :=
  Real.sqrt (vector_variance g)

/-- The Z-score Mask operator. Returns a new vector in `W`. -/
noncomputable def z_score_mask (g : W d) (z : ℝ) : W d :=
  let μ := vector_mean g
  let σ := vector_std g
  WithLp.equiv 2 (Fin d → ℝ) |>.symm fun i =>
    if |(WithLp.equiv 2 (Fin d → ℝ) g) i - μ| ≥ z * σ then 1 else 0

/-- Element-wise multiplication (Hadamard product) of vectors in $W$. -/
noncomputable def hadamard (a b : W d) : W d :=
  WithLp.equiv 2 (Fin d → ℝ) |>.symm fun i =>
    (WithLp.equiv 2 (Fin d → ℝ) a) i * (WithLp.equiv 2 (Fin d → ℝ) b) i

/-- The fully filtered gradient used in the parameter update. -/
noncomputable def filtered_gradient (g : W d) (z : ℝ) : W d :=
  hadamard g (z_score_mask g z)

/-- **Filter Sparsity (Non-emptiness)**: For z ≤ 1, the filter always preserves at least
    one component of the gradient. -/
theorem z_score_nonempty (g : W d) {z : ℝ} (hz_le : z ≤ 1) (hz_pos : 0 < z) :
    ∃ i : Fin d, (WithLp.equiv 2 (Fin d → ℝ) (z_score_mask g z)) i = 1 := by
  let μ := vector_mean g
  let σ := vector_std g
  haveI : 0 < d := Fact.out
  by_cases hσ : σ = 0
  · -- Case σ = 0: All are kept.
    use ⟨0, ‹0 < d›⟩
    simp [z_score_mask, σ, hσ, hz_pos]
  · -- Case σ > 0: Contradiction if all are zeroed.
    by_contra h
    push_neg at h
    -- If (mask g z) i ≠ 1, then it must be 0.
    have h_abs : ∀ i : Fin d, |(WithLp.equiv 2 (Fin d → ℝ) g) i - μ| < z * σ := by
      intro i
      have hi := h i
      unfold z_score_mask at hi
      simp only [WithLp.equiv_apply, Equiv.apply_symm_apply] at hi
      split_ifs at hi with h_cond
      · contradiction
      · push_neg at h_cond; exact h_cond
    -- Since z ≤ 1, |g i - μ| < σ.
    have h_sq : ∀ i : Fin d, ((WithLp.equiv 2 (Fin d → ℝ) g) i - μ)^2 < σ^2 := by
      intro i
      have hlt := h_abs i
      have h_nonneg : 0 ≤ σ := Real.sqrt_nonneg _
      have hsz : z * σ ≤ σ := mul_le_of_le_one_left h_nonneg hz_le
      have h_lt : |(WithLp.equiv 2 (Fin d → ℝ) g) i - μ| < σ := hlt.trans_le hsz
      rw [sq_lt_sq, abs_of_nonneg h_nonneg]
      exact h_lt
    -- Summing gives Σ (g_i - μ)² < d * σ².
    have h_sum : (∑ i : Fin d, ((WithLp.equiv 2 (Fin d → ℝ) g) i - μ)^2) < d * σ^2 := by
      haveI : Nonempty (Fin d) := ⟨⟨0, ‹0 < d›⟩⟩
      calc (∑ i : Fin d, ((WithLp.equiv 2 (Fin d → ℝ) g) i - μ)^2)
          < (∑ i : Fin d, σ^2) :=
            Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun i _ => h_sq i)
        _ = d * σ^2 := by simp
    -- But Σ |g i - μ|² = d * σ² by definition.
    have h_def : (∑ i : Fin d, ((WithLp.equiv 2 (Fin d → ℝ) g) i - μ)^2) = d * σ^2 := by
      have h_var_pos : 0 ≤ vector_variance g := by unfold vector_variance; positivity
      have h_sq_std : (Real.sqrt (vector_variance g))^2 = vector_variance g := Real.sq_sqrt h_var_pos
      unfold σ at hσ h_sq_std ⊢
      rw [vector_std, h_sq_std]
      unfold vector_variance
      dsimp
      have : (d : ℝ) ≠ 0 := by positivity
      rw [mul_div_cancel₀ _ ‹_›]
    linarith

end LeanSharp
