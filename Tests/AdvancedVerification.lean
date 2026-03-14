import LeanSharp.Theory.Dynamics.Convergence
import LeanSharp.Theory.Dynamics.Schedulers
import LeanSharp.Examples.IllConditioned

namespace LeanSharp

/-- **Advanced Verification**: Proves that the generalized convergence theorem
holds for the ill-conditioned landscape with a cosine decay schedule. -/
theorem advanced_schedule_convergence (T : ℕ) (hT : T > 0) (η0 ρ z : ℝ)
    (h_bounds : 0 ≤ η0 ∧ η0 * 20 ^ 2 ≤ 2 ∧ η0 ≤ 1 / 20)
    (h_align : ∀ w : W (Fin 2), alignment_condition IllConditioned.L_advanced w 0
                (sam_perturbation IllConditioned.L_advanced w ρ) z 2 20) :
    zsharp_convergence_holds IllConditioned.L_advanced 0
      (cosine_decay_schedule η0 0 T) ρ z 20 2 := by
  apply zsharp_convergence
  · intro t; rw [cosine_decay_schedule]
    have h_mono : cosine_decay_schedule η0 0 T t ≤ cosine_decay_schedule η0 0 T 0 :=
      cosine_decay_antitone η0 0 T (by linarith) (Nat.zero_le t)
    have h_eta0 : η0 = cosine_decay_schedule η0 0 T 0 := by
      rw [cosine_decay_zero η0 0 T hT]
    rw [← h_eta0] at h_mono
    calc cosine_decay_schedule η0 0 T t * 20 ^ 2
      _ ≤ η0 * 20 ^ 2 := mul_le_mul_of_nonneg_right h_mono (by norm_num)
      _ ≤ 2 := h_bounds.2.1
  · intro t; rw [cosine_decay_schedule]
    have h_mono : cosine_decay_schedule η0 0 T t ≤ cosine_decay_schedule η0 0 T 0 :=
      cosine_decay_antitone η0 0 T (by linarith) (Nat.zero_le t)
    have h_eta0 : η0 = cosine_decay_schedule η0 0 T 0 := by
      rw [cosine_decay_zero η0 0 T hT]
    rw [← h_eta0] at h_mono
    exact h_mono.trans h_bounds.2.2
  · norm_num
  · exact h_align

end LeanSharp
