import LeanSharp.Core.Stats
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.Order.Field.Basic

namespace LeanSharp

variable {ι : Type*} [Fintype ι]
variable {α : Type*}

open BigOperators

/-- A constant unit vector in $W$. -/
noncomputable def unit_vector (ι : Type*) [Fintype ι] : W ι :=
  WithLp.equiv 2 (ι → ℝ) |>.symm fun _ => 1 / Real.sqrt (Fintype.card ι)

lemma norm_unit_vector (ι : Type*) [Fintype ι] [Nonempty ι] : ‖unit_vector ι‖ = 1 := by
  unfold unit_vector
  rw [EuclideanSpace.norm_eq]
  simp only [WithLp.equiv_symm_apply, Real.norm_eq_abs, sq_abs]
  have card_pos : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h_sq : (1 / Real.sqrt (Fintype.card ι))^2 = 1 / (Fintype.card ι : ℝ) := by
    rw [one_div, inv_pow, Real.sq_sqrt card_pos]; field_simp
  simp only [h_sq]
  have card_ne_zero : (Fintype.card ι : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := ι))
  rw [mul_one_div_cancel card_ne_zero, Real.sqrt_one]

/-- The empirical mean of a collection of vectors. -/
noncomputable def empirical_mean (s : Finset α) (g : α → W ι) : W ι :=
  (1 / (s.card : ℝ)) • ∑ i ∈ s, g i

/-- **Mean Non-Robustness**: A single large outlier can move the mean arbitrarily far. -/
lemma mean_unbounded [Nonempty ι] (s : Finset α) (g : α → W ι) (i0 : α) (hi0 : i0 ∈ s) (C : ℝ)
    (hC : -1 ≤ C) :
    ∃ g' : α → W ι, (∀ i ≠ i0, g' i = g i) ∧ ‖empirical_mean s g'‖ > C := by
  classical
  let other_sum := ∑ i ∈ s.erase i0, g i
  let n := (s.card : ℝ)
  -- Choose v such that ‖(1/n) * (v + other_sum)‖ > C
  let v := (n * (C + 1) + ‖other_sum‖) • unit_vector ι
  use fun i => if i = i0 then v else g i
  have h_norm_v : ‖v‖ = n * (C + 1) + ‖other_sum‖ := by
    rw [
      norm_smul,
      norm_unit_vector,
      mul_one,
      Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (mul_nonneg (by positivity) (by linarith)) (norm_nonneg _))
    ]
  constructor
  · intro i hi; simp only [if_neg hi]
  · unfold empirical_mean
    rw [
      ← Finset.insert_erase hi0,
      Finset.sum_insert (fun h => absurd rfl (Finset.mem_erase.mp h).left),
      Finset.sum_congr rfl (fun i hi => if_neg (Finset.mem_erase.1 hi).1),
      Finset.insert_erase hi0
    ]
    simp only [↓reduceIte]
    rw [show (s.erase i0).sum g = other_sum from rfl, show (s.card : ℝ) = n from rfl]
    have hn_pos : 0 < n := by have : s.Nonempty := ⟨i0, hi0⟩; positivity
    rw [norm_smul, Real.norm_eq_abs (1 / n), abs_of_pos (one_div_pos.mpr hn_pos)]
    have heq : (1 / n) * (‖v‖ - ‖other_sum‖) = (1 / n)
      * (n * (C + 1) + ‖other_sum‖ - ‖other_sum‖) := by rw [h_norm_v]
    have hring : (1 / n) * (n * (C + 1) + ‖other_sum‖ - ‖other_sum‖)
      = (1 / n) * (n * (C + 1)) := by ring
    have hlast : (1 / n) * (n * (C + 1)) = C + 1 := by field_simp [hn_pos.ne.symm]
    have hineq : ‖v + other_sum‖ ≥ ‖v‖ - ‖other_sum‖ := by
      have H := (norm_sub_norm_le v (-other_sum)).trans_eq (by rw [sub_neg_eq_add])
      have hneg : ‖v‖ - ‖-other_sum‖ = ‖v‖ - ‖other_sum‖ := by rw [norm_neg other_sum]
      exact (ge_of_eq hneg).trans H
    have hchain := heq.trans (hring.trans hlast)
    have hge := ge_trans (mul_le_mul_of_nonneg_left hineq (one_div_pos.mpr hn_pos).le)
      (ge_of_eq hchain)
    exact lt_of_lt_of_le (by linarith) hge

/-- **Median Robustness (Boundedness)**: The geometric median remains bounded even if
some points are moved, as long as a majority stay fixed.
This is a precursor to the 50% breakdown point. -/
theorem median_bounded_subset (s : Finset α) (g : α → W ι) (s_fixed : Finset α)
    (h_sub : s_fixed ⊆ s) (h_maj : 2 * s_fixed.card > s.card) :
    ∃ R_med : ℝ, ∀ g' : α → W ι, (∀ i ∈ s_fixed, g' i = g i) →
      ‖geometric_median s g'‖ ≤ R_med := by
  classical
  have hs_nonempty : s.Nonempty := by
    by_contra h
    have heq : s = ∅ := (Finset.not_nonempty_iff_eq_empty (α := α)).1 h
    rw [heq, Finset.card_empty] at h_maj
    rw [heq] at h_sub
    rw [Finset.subset_empty.1 h_sub, Finset.card_empty, mul_zero] at h_maj
    exact Nat.not_lt_zero _ h_maj
  have h_fixed_nonempty : s_fixed.Nonempty := by
    by_contra h
    have heq : s_fixed = ∅ := (Finset.not_nonempty_iff_eq_empty (α := α)).1 h
    rw [heq, Finset.card_empty, mul_zero] at h_maj
    exact Nat.not_lt_zero _ h_maj
  let i0 := h_fixed_nonempty.choose
  have hi0 : i0 ∈ s_fixed := h_fixed_nonempty.choose_spec
  let C_fixed := 2 * ∑ i ∈ s_fixed, ‖g i - g i0‖
  let n := (s.card : ℝ)
  let nf := (s_fixed.card : ℝ)
  let K := 2 * nf - n
  have hK_pos : 0 < K := by
    have H : (2 : ℝ) * (s_fixed.card : ℝ) > (s.card : ℝ) := mod_cast h_maj
    exact sub_pos.mpr H
  use ‖g i0‖ + C_fixed / K
  intro g' hg'
  let m := geometric_median s g'
  have h_min : (fun x => ∑ i ∈ s, ‖g' i - x‖) m ≤ (∑ i ∈ s, ‖g' i - g i0‖) := by
    rw [show m = geometric_median s g' from rfl]
    have H : ∀ x ∈ Set.univ, (fun m => ∑ i ∈ s, ‖g' i - m‖)
        (geometric_median s g') ≤ (fun m => ∑ i ∈ s, ‖g' i - m‖) x := by
      unfold geometric_median; rw [dif_pos hs_nonempty]
      exact Classical.choose_spec (exists_isMin_on_finite_sum_norm s g' hs_nonempty)
    exact H (g i0) (Set.mem_univ (g i0))
  let s_out := s \ s_fixed
  have h_split (x : W ι) : ∑ i ∈ s, ‖g' i - x‖
      = (∑ i ∈ s_fixed, ‖g i - x‖) + (∑ i ∈ s_out, ‖g' i - x‖) := by
    rw [← Finset.sdiff_union_of_subset h_sub]
    rw [Finset.sum_union (Finset.disjoint_iff_inter_eq_empty.2 (Finset.sdiff_inter_self s_fixed s))]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl (fun i hi => congr_arg (fun w => ‖w - x‖) (hg' i hi))
  rw [show (fun x => ∑ i ∈ s, ‖g' i - x‖) m = ∑ i ∈ s, ‖g' i - m‖ from rfl] at h_min
  rw [h_split m, h_split (g i0)] at h_min
  -- From h_min, bound ‖m - g i0‖
  have h_dist_bound : K * ‖m - g i0‖ ≤ C_fixed := by
    -- ‖g i - m‖ ≥ ‖m - g i0‖ - ‖g i - g i0‖
    have h1 : ∑ i ∈ s_fixed, ‖g i - m‖ ≥ nf * ‖m - g i0‖ - (∑ i ∈ s_fixed, ‖g i - g i0‖) := by
      calc (∑ i ∈ s_fixed, ‖g i - m‖) ≥ ∑ i ∈ s_fixed, (‖m - g i0‖ - ‖g i - g i0‖) :=
            Finset.sum_le_sum (fun i _ => by
              have H := norm_sub_norm_le (m - g i0) (g i - g i0)
              rw [show (m - g i0) - (g i - g i0) = m - g i from by abel] at H
              rw [norm_sub_rev m (g i)] at H
              exact H)
        _ = nf * ‖m - g i0‖ - ∑ i ∈ s_fixed, ‖g i - g i0‖ := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    -- ∑_{i ∈ s_out} (‖g' i - i0‖ - ‖g' i - m‖) ≤ n_out * ‖m - i0‖
    have h2 : (∑ i ∈ s_out, ‖g' i - g i0‖) - (∑ i ∈ s_out, ‖g' i - m‖)
        ≤ (s_out.card : ℝ) * ‖m - g i0‖ := by
      calc (∑ i ∈ s_out, ‖g' i - g i0‖) - (∑ i ∈ s_out, ‖g' i - m‖)
          = ∑ i ∈ s_out, (‖g' i - g i0‖ - ‖g' i - m‖) := by rw [Finset.sum_sub_distrib]
        _ ≤ ∑ i ∈ s_out, ‖m - g i0‖ := by
          apply Finset.sum_le_sum; intro i _
          have H := norm_sub_norm_le (g' i - g i0) (g' i - m)
          rw [show (g' i - g i0) - (g' i - m) = m - g i0 from by abel] at H; exact H
        _ = (s_out.card : ℝ) * ‖m - g i0‖ := by rw [Finset.sum_const, nsmul_eq_mul]
    have h_out_card : (s_out.card : ℝ) = n - nf := by
      rw [Finset.card_sdiff, Finset.inter_comm, Finset.inter_eq_right.2 h_sub,
          Nat.cast_sub (Finset.card_le_card h_sub)]
    rw [h_out_card] at h2
    linarith
  calc ‖geometric_median s g'‖ = ‖m‖ := by rw [show m = geometric_median s g' from rfl]
    _ ≤ ‖m - g i0‖ + ‖g i0‖ := by rw [add_comm]; apply norm_le_insert'
    _ ≤ C_fixed / K + ‖g i0‖ := by
      have hdiv : ‖m - g i0‖ ≤ C_fixed / K := by
        have H := mul_le_mul (α := ℝ) (le_refl K⁻¹) h_dist_bound
          (mul_nonneg (le_of_lt hK_pos) (norm_nonneg _)) (inv_pos.mpr hK_pos).le
        have H2 : K⁻¹ * K = (1 : ℝ) := by field_simp [ne_of_gt hK_pos]
        rw [← mul_assoc, H2, one_mul, mul_comm] at H
        rwa [div_eq_inv_mul C_fixed K, mul_comm]
      rw [add_comm (‖m - g i0‖), add_comm (C_fixed / K)]
      exact add_le_add_right hdiv ‖g i0‖
    _ = ‖g i0‖ + C_fixed / K := add_comm _ _

/-- **50% breakdown point (unbounded side)**: When strictly fewer than half the points
are fixed, an adversary can move the remaining points so that the geometric median
has arbitrarily large norm. Together with `median_bounded_subset` this characterizes
the 50% breakdown point: the median stays bounded iff more than half the points are fixed. -/
theorem median_breakdown [Nonempty ι] (s : Finset α) (g : α → W ι) (s_fixed : Finset α)
    (h_sub : s_fixed ⊆ s) (h_break : 2 * s_fixed.card < s.card) (C : ℝ) (hC : -1 ≤ C) :
    ∃ g' : α → W ι, (∀ i ∈ s_fixed, g' i = g i) ∧ ‖geometric_median s g'‖ > C := by
  classical
  have hs_nonempty : s.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h, Finset.card_empty] at h_break
    exact Nat.not_lt_zero _ h_break
  let s_out := s \ s_fixed
  have h_out_card : s_out.card = s.card - s_fixed.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.2 h_sub]
  have h_nout_gt_nfixed : (s_fixed.card : ℝ) < (s_out.card : ℝ) := by
    rw [h_out_card, Nat.cast_sub (Finset.card_le_card h_sub)]
    have H : (2 : ℝ) * (s_fixed.card : ℝ) < (s.card : ℝ) := mod_cast h_break
    linarith
  have h_denom_pos : 0 < (s_out.card : ℝ) - (s_fixed.card : ℝ) := sub_pos.mpr h_nout_gt_nfixed
  set B := ∑ i ∈ s_fixed, ‖g i‖
  set n_out := (s_out.card : ℝ)
  set n_fixed := (s_fixed.card : ℝ)
  set R := max (C + 2) ((n_out * C + B) / (n_out - n_fixed) + 1)
  have hR_ge : R ≥ 0 := by unfold R; apply le_max_iff.mpr; left; linarith
  have hR_gt_C : C < R := by unfold R; exact lt_max_of_lt_left (by linarith)
  have hR_large : (n_out * C + B) / (n_out - n_fixed) < R := by
    unfold R; have h1 := le_max_right (C + 2) ((n_out * C + B) / (n_out - n_fixed) + 1)
    linarith
  use fun i => if i ∈ s_out then R • unit_vector ι else g i
  constructor
  · intro i hi
    split_ifs with h
    · exact absurd hi (Finset.mem_sdiff.1 h).2
    · rfl
  · set g' := fun i => if i ∈ s_out then R • unit_vector ι else g i
    set m := geometric_median s g'
    have hg'_fixed : ∀ i ∈ s_fixed, g' i = g i := by
      intro i hi; simp only [g']; split_ifs with h
      · exact absurd hi (Finset.mem_sdiff.1 h).2
      · rfl
    have hg'_out : ∀ i ∈ s_out, g' i = R • unit_vector ι := by
      intro i hi; simp only [g']; rw [if_pos hi]
    have hm_min : ∀ x : W ι, ∑ i ∈ s, ‖g' i - m‖ ≤ ∑ i ∈ s, ‖g' i - x‖ := by
      intro x
      have h_m_choice : m = Classical.choose (exists_isMin_on_finite_sum_norm s g' hs_nonempty) :=
        geometric_median_eq_choose s g' hs_nonempty
      rw [h_m_choice]
      exact Classical.choose_spec
        (exists_isMin_on_finite_sum_norm s g' hs_nonempty) (Set.mem_univ x)
    by_contra h_norm_le
    push_neg at h_norm_le
    set v := R • unit_vector ι
    have h_sum_at_m : ∑ i ∈ s, ‖g' i - m‖ =
        (∑ i ∈ s_fixed, ‖g i - m‖) + ∑ i ∈ s_out, ‖v - m‖ := by
      rw [← Finset.sdiff_union_of_subset h_sub,
        Finset.sum_union (Finset.disjoint_iff_inter_eq_empty.2 (Finset.sdiff_inter_self s_fixed s)),
        add_comm]
      congr 1
      · refine Finset.sum_congr rfl (fun i hi => congr_arg (‖· - m‖) (hg'_fixed i hi))
      · refine Finset.sum_congr rfl (fun i hi => congr_arg (‖· - m‖) (hg'_out i hi))
    have h_norm_v : ‖v‖ = R := by
      rw [norm_smul, norm_unit_vector, mul_one, Real.norm_eq_abs, abs_of_nonneg hR_ge]
    have h_lower : ∑ i ∈ s_fixed, ‖g i - m‖ + ∑ i ∈ s_out, ‖v - m‖ ≥ (n_out : ℝ) * (R - C) := by
      have h1 : ∑ i ∈ s_out, ‖v - m‖ ≥ (n_out : ℝ) * (R - C) := by
        have h1' : ∑ i ∈ s_out, ‖v - m‖ ≥ ∑ i ∈ s_out, (R - C) := by
          apply Finset.sum_le_sum; intro i _
          have H := norm_sub_norm_le v m
          rw [h_norm_v] at H
          have hR_C : R - C ≤ R - ‖m‖ := sub_le_sub_left h_norm_le R
          exact hR_C.trans H
        rw [Finset.sum_const, nsmul_eq_mul, Finset.sum_const, nsmul_eq_mul] at h1'
        rw [Finset.sum_const, nsmul_eq_mul, show (s_out.card : ℝ) = n_out from rfl]
        exact h1'
      have h2 : 0 ≤ ∑ i ∈ s_fixed, ‖g i - m‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
      exact (zero_add (n_out * (R - C))).symm.le.trans (add_le_add h2 h1)
    have h_upper : ∑ i ∈ s, ‖g' i - v‖ ≤ B + n_fixed * R := by
      rw [← Finset.sdiff_union_of_subset h_sub,
        Finset.sum_union (Finset.disjoint_iff_inter_eq_empty.2 (Finset.sdiff_inter_self s_fixed s))]
      have h_fixed : ∑ i ∈ s_fixed, ‖g' i - v‖ = ∑ i ∈ s_fixed, ‖g i - v‖ := by
        refine Finset.sum_congr rfl (fun i hi => congr_arg (‖· - v‖) (hg'_fixed i hi))
      rw [h_fixed]
      have h_out : ∑ i ∈ s_out, ‖g' i - v‖ = 0 := by
        rw [Finset.sum_eq_zero]; intro i hi; rw [hg'_out i hi, sub_self, norm_zero]
      rw [h_out, zero_add]
      trans ∑ i ∈ s_fixed, (‖g i‖ + ‖v‖)
      · exact Finset.sum_le_sum (fun i _ => norm_sub_le (g i) v)
      · rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, h_norm_v]
    have h_eq : ∑ i ∈ s, ‖g' i - m‖ = (∑ i ∈ s_fixed, ‖g i - m‖) + ∑ i ∈ s_out, ‖v - m‖ :=
      h_sum_at_m
    have h_m_le_v := hm_min v
    have h_sum_at_v : ∑ i ∈ s, ‖g' i - v‖ = ∑ i ∈ s_fixed, ‖g i - v‖ + 0 := by
      rw [← Finset.sdiff_union_of_subset h_sub,
        Finset.sum_union (Finset.disjoint_iff_inter_eq_empty.2 (Finset.sdiff_inter_self s_fixed s)),
        add_comm]
      congr 1
      · refine Finset.sum_congr rfl (fun i hi => congr_arg (‖· - v‖) (hg'_fixed i hi))
      · rw [Finset.sum_eq_zero]; intro i hi; rw [hg'_out i hi, sub_self, norm_zero]
    rw [h_eq] at hm_min
    rw [h_sum_at_v] at h_m_le_v
    have h_v_ub : ∑ i ∈ s_fixed, ‖g i - v‖ ≤ B + n_fixed * R := by
      trans ∑ i ∈ s_fixed, (‖g i‖ + ‖v‖)
      · exact Finset.sum_le_sum (fun i _ => norm_sub_le (g i) v)
      · rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, h_norm_v]
    have key : R * (n_out - n_fixed) ≤ n_out * C + B := by
      rw [h_eq, add_zero] at h_m_le_v
      have := h_lower.trans (h_m_le_v.trans h_v_ub)
      nlinarith
    have hR_large' : (n_out * C + B) < R * (n_out - n_fixed) := by
      have := mul_lt_mul_of_pos_right hR_large h_denom_pos
      have H : (n_out * C + B) / (n_out - n_fixed) * (n_out - n_fixed) = n_out * C + B := by
        field_simp [ne_of_gt h_denom_pos]
      rwa [H] at this
    nlinarith [key, hR_large']

end LeanSharp
