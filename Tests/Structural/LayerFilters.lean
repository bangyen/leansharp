/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Core.LayerFilters

/-!
# Layer-Wise Filtering Separation

This module exists to verify that layer-wise Z-score filtering is not merely a
generalization of the global filter on paper but genuinely differs from it on a
concrete gradient, so that the per-layer statistics of arXiv:2505.02369 have real
content.

The witness is `g = ![0, 0, 0, 1]` over `Fin 4`, split into the two layers
`{0, 1}` and `{2, 3}`, at threshold `z = 1`. Coordinate `3` is an outlier against
the pooled statistics — the global mean is `1/4` and the global standard deviation
is `√(3/16) < 3/4` — so the global filter keeps it. Within its own layer `{2, 3}`
the mean is `1/2` and the standard deviation is `1/2`, so `|1 - 1/2| = 1/2` sits
exactly on the threshold and the layer-wise filter discards it.

## Definitions

* `sepGrad`: the separating gradient `![0, 0, 0, 1]`.
* `sepPart`: the two-layer partition `{0, 1} ⊔ {2, 3}`.

## Theorems

* `sep_blockMean`: the mean of coordinate `3`'s own layer.
* `sep_blockStd`: the standard deviation of that layer.
* `sep_vectorMean`: the pooled mean.
* `sep_vectorVariance`: the pooled variance.
* `sep_vectorStd_lt`: the pooled standard deviation is below `3/4`.
* `sep_layer_ne_global`: the layer-wise and global filters differ on `sepGrad`.
-/

namespace LeanSharp.Tests

open Finset

/-- The separating gradient: three zeros and a single one. -/
noncomputable def sepGrad : W (Fin 4) :=
  (WithLp.equiv 2 (Fin 4 → ℝ)).symm ![0, 0, 0, 1]

/-- The two-layer partition `{0, 1} ⊔ {2, 3}`. -/
def sepPart : Fin 4 → Fin 2 := ![0, 0, 1, 1]

private lemma sep_fiber : fiber sepPart (sepPart 3) = {2, 3} := by decide +kernel

private lemma sep_card : (({2, 3} : Finset (Fin 4))).card = 2 := by decide +kernel

/-- The layer containing coordinate `3` has mean `1/2`. -/
lemma sep_blockMean : blockMean sepGrad sepPart (sepPart 3) = 1 / 2 := by
  unfold blockMean
  rw [sep_fiber, Finset.sum_pair (by decide : (2 : Fin 4) ≠ 3), sep_card]
  simp only [sepGrad, WithLp.equiv_symm_apply, Fin.isValue, WithLp.equiv_apply,
    Matrix.cons_val, zero_add, Nat.cast_ofNat, one_div]

/-- The layer containing coordinate `3` has standard deviation `1/2`. -/
lemma sep_blockStd : blockStd sepGrad sepPart (sepPart 3) = 1 / 2 := by
  unfold blockStd blockVariance
  rw [sep_fiber, sep_blockMean, Finset.sum_pair (by decide : (2 : Fin 4) ≠ 3),
    sep_card]
  simp only [sepGrad, WithLp.equiv_symm_apply, Fin.isValue, WithLp.equiv_apply,
    Matrix.cons_val, one_div, zero_sub, even_two, Even.neg_pow, inv_pow, Nat.cast_ofNat,
    Nat.ofNat_nonneg, Real.sqrt_div']
  rw [show ((2 : ℝ) ^ 2)⁻¹ + (1 - 2⁻¹) ^ 2 = 2⁻¹ by norm_num, Real.sqrt_inv]
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
  field_simp
  linarith [hs]

/-- Pooled over all four coordinates the mean is `1/4`. -/
lemma sep_vectorMean : vectorMean sepGrad = 1 / 4 := by
  unfold vectorMean
  simp only [sepGrad, WithLp.equiv_symm_apply, WithLp.equiv_apply, Fin.sum_univ_four,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, add_zero, Matrix.cons_val,
    zero_add, Fintype.card_fin, Nat.cast_ofNat, one_div]

/-- Pooled over all four coordinates the variance is `3/16`. -/
lemma sep_vectorVariance : vectorVariance sepGrad = 3 / 16 := by
  unfold vectorVariance
  rw [sep_vectorMean]
  simp only [sepGrad, WithLp.equiv_symm_apply, WithLp.equiv_apply, one_div,
    Fin.sum_univ_four, Fin.isValue, Matrix.cons_val_zero, zero_sub, even_two,
    Even.neg_pow, inv_pow, Matrix.cons_val_one, Matrix.cons_val, Fintype.card_fin,
    Nat.cast_ofNat]
  norm_num

/-- The pooled standard deviation is below `3/4`, so coordinate `3` is a global
outlier at `z = 1`. -/
lemma sep_vectorStd_lt : vectorStd sepGrad < 3 / 4 := by
  unfold vectorStd
  rw [sep_vectorVariance,
    show (3 : ℝ) / 4 = Real.sqrt ((3 / 4) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  apply Real.sqrt_lt_sqrt (by norm_num)
  norm_num

/-- **Separation**: the layer-wise filter is genuinely different from the global one.
Coordinate `3` stands out against the pooled statistics but not within its own layer,
so the paper's per-layer normalization is not a restatement of the global filter. -/
theorem sep_layer_ne_global :
    layerTailFilteredGradient sepGrad sepPart 1 ≠ tailFilteredGradient sepGrad 1 := by
  intro h
  have h3 := congrArg (fun v => (WithLp.equiv 2 (Fin 4 → ℝ)) v 3) h
  unfold layerTailFilteredGradient tailFilteredGradient hadamard
    layerZScoreTailMask zScoreTailMask at h3
  simp only [WithLp.equiv_apply, Equiv.apply_symm_apply] at h3
  rw [sep_blockMean, sep_blockStd, sep_vectorMean] at h3
  have hval : sepGrad.ofLp 3 = 1 := by
    simp only [Fin.isValue, sepGrad, WithLp.equiv_symm_apply, Matrix.cons_val]
  split_ifs at h3 with hL hR hR
  · -- both discard: but coordinate 3 IS a global outlier
    rw [hval, show |(1:ℝ) - 1 / 4| = 3 / 4 by rw [abs_of_nonneg] <;> norm_num] at hR
    exact absurd hR (by simpa only [one_mul, not_le] using not_le.mpr sep_vectorStd_lt)
  · rw [hval] at h3; norm_num at h3
  · rw [hval, show |(1:ℝ) - 1 / 2| = 1 / 2 by rw [abs_of_nonneg] <;> norm_num] at hL
    exact absurd (by norm_num : (1:ℝ)/2 ≤ 1 * (1/2)) hL
  · rw [hval, show |(1:ℝ) - 1 / 2| = 1 / 2 by rw [abs_of_nonneg] <;> norm_num] at hL
    exact absurd (by norm_num : (1:ℝ)/2 ≤ 1 * (1/2)) hL

end LeanSharp.Tests
