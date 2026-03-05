import LeanSharp.Landscape
import LeanSharp.Sam
import LeanSharp.Filters
import LeanSharp.Theorems
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.Order.Ring.Defs

set_option linter.unusedSectionVars false

/-!
# Phase 4: ZSharp Convergence Bound

One of the open research questions for SAM variants is how modifying the
adversarial gradient affects the theoretical convergence rate under standard
optimization assumptions.

Here, we mathematically formalize the conditions required to prove that
ZSharp converges on a well-behaved (convex, smooth) landscape.
-/

namespace LeanSharp

variable {d : ℕ} [Fact (0 < d)]

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

/-- The parameter update for a single step of ZSharp.
    w_{t+1} = w_t - η * filtered_gradient(∇L(w_t + ε), z) -/
noncomputable def zsharp_step (w : W d) (η ρ z : ℝ) : W d :=
  let ε := sam_perturbation L w ρ
  let g_adv := gradient L (w + ε)
  let g_filtered := filtered_gradient g_adv z
  w - η • g_filtered

/-- Lipschitz Gradient Bound: under L-smoothness and optimality of w_star,
    the gradient magnitude at any w is bounded by L_smooth * ‖w - w_star‖. -/
lemma gradient_bound (L_smooth : ℝ) (h_smooth : is_L_smooth L L_smooth)
    (h_opt : gradient L w_star = 0) (w : W d) :
    ‖gradient L w‖ ≤ L_smooth * ‖w - w_star‖ := by
  obtain ⟨hL, h_lip⟩ := h_smooth
  have hb := h_lip w w_star
  rw [h_opt, sub_zero] at hb
  exact hb

/-- Lemma 1: Gradient Descent Contraction.
    Under μ-strong convexity and L-smoothness, a GD step contracts the squared
    distance to w* by factor (1 - η*μ) < 1. -/
lemma gd_contraction (η L_smooth μ : ℝ)
    (h_smooth : is_L_smooth L L_smooth)
    (h_convex : is_strongly_convex L μ)
    (h_opt : gradient L w_star = 0)
    (hμL : μ < L_smooth)
    (hη : 0 < η)
    (hη_bound : η ≤ 1 / L_smooth)
    (hη_tight : η * L_smooth ^ 2 ≤ μ) :
    ∃ c ∈ Set.Ioo 0 1, ∀ w : W d,
        ‖(w - η • gradient L w) - w_star‖^2 ≤ c * ‖w - w_star‖^2 := by
  obtain ⟨hL, h_lip⟩ := h_smooth
  obtain ⟨hμ, h_sc⟩ := h_convex
  use 1 - η * μ
  have hημ_pos : 0 < η * μ := mul_pos hη hμ
  have hημ_lt_1 : η * μ < 1 := by
    have hL_inv : η * L_smooth ≤ 1 := calc
      η * L_smooth ≤ (1 / L_smooth) * L_smooth := mul_le_mul_of_nonneg_right hη_bound (le_of_lt hL)
      _             = 1                         := by field_simp
    calc η * μ < η * L_smooth := mul_lt_mul_of_pos_left hμL hη
         _     ≤ 1            := hL_inv
  constructor
  · constructor <;> linarith
  · intro w
    have h_expand : ‖(w - η • gradient L w) - w_star‖^2 =
        ‖w - w_star‖^2 - 2 * η * @inner ℝ _ _ (gradient L w) (w - w_star) +
        η^2 * ‖gradient L w‖^2 := by
      have hrw : (w - η • gradient L w) - w_star = (w - w_star) - η • gradient L w := by abel
      rw [hrw, norm_sub_sq_real, inner_smul_right, real_inner_comm,
          norm_smul, Real.norm_eq_abs, abs_of_pos hη]
      ring
    have h_sc_bound : μ * ‖w - w_star‖^2 ≤ @inner ℝ _ _ (gradient L w) (w - w_star) := by
      have h_sc2 := h_sc w_star w
      simp only [h_opt, inner_zero_left] at h_sc2
      have h_sc1 := h_sc w w_star
      have h_inner_flip : @inner ℝ _ _ (gradient L w) (w_star - w) =
          -@inner ℝ _ _ (gradient L w) (w - w_star) := by
        rw [show w_star - w = -(w - w_star) from (neg_sub w w_star).symm, inner_neg_right]
      have h_norm_eq : ‖w_star - w‖ = ‖w - w_star‖ := by rw [norm_sub_rev]
      rw [h_inner_flip, h_norm_eq] at h_sc1
      linarith
    have h_smooth_bound : ‖gradient L w‖^2 ≤ L_smooth^2 * ‖w - w_star‖^2 := by
      have hb := h_lip w w_star
      rw [h_opt, sub_zero] at hb
      nlinarith [sq_nonneg (‖gradient L w‖ - L_smooth * ‖w - w_star‖),
                 norm_nonneg (gradient L w), norm_nonneg (w - w_star)]
    rw [h_expand]
    have h_sq_eta : η^2 ≥ 0 := sq_nonneg η
    have hkey : η^2 * L_smooth^2 ≤ η * μ := by nlinarith [h_sq_eta, hη_tight]
    nlinarith [h_sc_bound, h_smooth_bound, sq_nonneg ‖w - w_star‖,
               mul_nonneg (le_of_lt hη) (mul_nonneg (le_of_lt hμ) (sq_nonneg ‖w - w_star‖))]

/-- Lemma 2: SAM Perturbation Bound.
    The error introduced by the SAM perturbation `ε` is bounded by `ρ`. -/
lemma sam_perturbation_bound (w : W d) (ρ : ℝ) (hρ : ρ > 0) :
    ‖sam_perturbation L w ρ‖ ≤ ρ := by
  unfold sam_perturbation
  by_cases h : ‖gradient L w‖ = 0
  · simp only [h, if_true, norm_zero]; linarith
  · simp only [h, if_false, norm_smul]
    have hg_pos : 0 < ‖gradient L w‖ := by
      exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm h)
    rw [Real.norm_of_nonneg (div_nonneg (le_of_lt hρ) (le_of_lt hg_pos))]
    field_simp; exact le_refl _

/-- Lemma 3: Z-Score Quantization Error.
    The total squared $L_2$ error introduced by the filter is bounded by
    $d \cdot (|μ| + z \cdot σ)^2$. -/
lemma z_score_error_bound (g : W d) (z : ℝ) (hz : z ≥ 0) :
    ‖filtered_gradient g z - g‖^2 ≤ d * (|vector_mean g| + z * vector_std g)^2 := by
  have h_norm_sq :
      ‖filtered_gradient g z - g‖^2 = ∑ i : Fin d, (filtered_gradient g z i - g i)^2 := by
    rw [EuclideanSpace.norm_sq_eq]; simp [Real.norm_eq_abs, sq_abs]
  rw [h_norm_sq]
  have h_comp_sq : ∀ i : Fin d,
      (filtered_gradient g z i - g i)^2 ≤ (|vector_mean g| + z * vector_std g)^2 := by
    intro i
    have h_abs := filtered_component_bound g z hz i
    let b := |vector_mean g| + z * vector_std g
    have h_b_nonneg : 0 ≤ b := by
      have h1 : 0 ≤ |vector_mean g| := abs_nonneg _
      have h2 : 0 ≤ z * vector_std g := by
        apply mul_nonneg hz
        unfold vector_std; exact Real.sqrt_nonneg _
      linarith
    have h_abs_le_abs : |filtered_gradient g z i - g i| ≤ |b| := by
      rw [abs_of_nonneg h_b_nonneg]; exact h_abs
    exact sq_le_sq.mpr h_abs_le_abs
  calc (∑ i : Fin d, (filtered_gradient g z i - g i)^2)
      ≤ ∑ i : Fin d, (|vector_mean g| + z * vector_std g)^2 :=
          Finset.sum_le_sum fun i _ => h_comp_sq i
    _ = d * (|vector_mean g| + z * vector_std g)^2 := by
           simp [Finset.sum_const, nsmul_eq_mul]

/-- The formal statement of ZSharp convergence holds.
    It posits that there exists a contraction factor `c ∈ (0, 1)`. -/
def zsharp_convergence_holds (η ρ z L_smooth μ : ℝ) : Prop :=
  is_L_smooth L L_smooth →
  is_strongly_convex L μ →
  η > 0 ∧ ρ > 0 →
  ∃ c : ℝ, 0 < c ∧ c < 1 ∧
    ∀ w : W d, ‖zsharp_step L w η ρ z - w_star‖^2 ≤ c * ‖w - w_star‖^2

/-- The Alignment Condition:
    A statistical assumption that the filtered gradient maintains sufficient
    alignment with the true descent direction, and its norm is bounded by the
    landscape smoothness. -/
def alignment_condition (L : W d → ℝ) (w w_star : W d) (ε : W d) (z μ L_smooth : ℝ) : Prop :=
  let g_adv := gradient L (w + ε)
  let g_f := filtered_gradient g_adv z
  μ * ‖w - w_star‖^2 ≤ @inner ℝ _ _ g_f (w - w_star) ∧
  ‖g_f‖ ≤ L_smooth * ‖w - w_star‖

/-- Main Theorem: ZSharp converges geometrically to `w_star` under standard assumptions. -/
theorem zsharp_convergence (η ρ z L_smooth μ : ℝ)
    (hη_tight : η * L_smooth ^ 2 ≤ μ)
    (hη_bound : η ≤ 1 / L_smooth)
    (hμL : μ < L_smooth)
    (h_align : ∀ w : W d, let ε := sam_perturbation L w ρ
                          alignment_condition L w w_star ε z μ L_smooth) :
    zsharp_convergence_holds L w_star η ρ z L_smooth μ := by
  intro h_smooth h_convex ⟨hη, hρ⟩
  set c := 1 - η * μ with hc_def
  have hμ := h_convex.1
  have hL := h_smooth.1
  have h_c_pos : 0 < c := by
    rw [hc_def]
    have hημ_lt_1 : η * μ < 1 := by
      have : η * μ < η * L_smooth := mul_lt_mul_of_pos_left hμL hη
      have hη_L_le_1 : η * L_smooth ≤ 1 := by
        have h1 := mul_le_mul_of_nonneg_right hη_bound (le_of_lt hL)
        field_simp at h1; exact h1
      linarith
    linarith
  have h_c_lt_1 : c < 1 := by rw [hc_def]; linarith [mul_pos hη hμ]
  refine ⟨c, h_c_pos, h_c_lt_1, fun w => ?_⟩
  simp only [zsharp_step]
  let ε := sam_perturbation L w ρ
  let g_f := filtered_gradient (gradient L (w + ε)) z
  obtain ⟨h_inner_bound, h_gf_bound⟩ := h_align w
  have h_gf_sq : ‖g_f‖^2 ≤ (L_smooth * ‖w - w_star‖)^2 := by
    apply sq_le_sq.mpr
    rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (mul_nonneg (le_of_lt hL) (norm_nonneg _))]
    exact h_gf_bound
  have hrw : (w - η • g_f) - w_star = (w - w_star) - η • g_f := by abel
  rw [hrw, norm_sub_sq_real, inner_smul_right, real_inner_comm]
  simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hη]
  have hkey : η^2 * L_smooth^2 ≤ η * μ := by nlinarith [sq_nonneg η, hη_tight]
  nlinarith [sq_nonneg ‖w - w_star‖, h_inner_bound, h_gf_sq, hkey,
             mul_nonneg (le_of_lt hη) (mul_nonneg (le_of_lt hμ) (sq_nonneg ‖w - w_star‖))]

end LeanSharp
