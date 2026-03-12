import LeanSharp.Theory.Convergence
import LeanSharp.Theory.Schedulers
import LeanSharp.Examples.ToyApplication

namespace LeanSharp

/-- **Schedule Convergence Verification**: A toy example demonstrating that
the generalized convergence theorem can be applied to `cosine_decay_schedule`. -/
theorem toy_cosine_convergence (T : ℕ) (hT : T > 0) (η0 ρ z μ L_smooth : ℝ)
    (h_bounds : 0 ≤ η0 ∧ η0 * L_smooth ^ 2 ≤ μ ∧ η0 ≤ 1 / L_smooth ∧ μ < L_smooth)
    (h_align : ∀ w : W (Fin 2), alignment_condition Toy.L_toy w 0 
                (sam_perturbation Toy.L_toy w ρ) z μ L_smooth) :
    zsharp_convergence_holds Toy.L_toy 0 
      (cosine_decay_schedule η0 0 T) ρ z L_smooth μ := by
  apply zsharp_convergence
  · intro t; dsimp [cosine_decay_schedule]
    -- Proof that η_t * L_smooth^2 ≤ μ
    -- η_t ≤ η0 since cosine decay is antitone
    have h_mono : cosine_decay_schedule η0 0 T t ≤ cosine_decay_schedule η0 0 T 0 :=
      cosine_decay_antitone η0 0 T (by linarith) (Nat.zero_le t)
    have h_eta0 : η0 = cosine_decay_schedule η0 0 T 0 := by 
      rw [cosine_decay_zero η0 0 T hT]
    rw [← h_eta0] at h_mono
    calc cosine_decay_schedule η0 0 T t * L_smooth ^ 2
      _ ≤ η0 * L_smooth ^ 2 := mul_le_mul_of_nonneg_right h_mono (sq_nonneg _)
      _ ≤ μ := h_bounds.2.1
  · intro t; dsimp [cosine_decay_schedule]
    -- Proof that η_t ≤ 1 / L_smooth
    have h_mono : cosine_decay_schedule η0 0 T t ≤ cosine_decay_schedule η0 0 T 0 :=
      cosine_decay_antitone η0 0 T (by linarith) (Nat.zero_le t)
    have h_eta0 : η0 = cosine_decay_schedule η0 0 T 0 := by 
      rw [cosine_decay_zero η0 0 T hT]
    rw [← h_eta0] at h_mono
    exact h_mono.trans h_bounds.2.2.1
  · exact h_bounds.2.2.2
  · exact h_align

end LeanSharp
