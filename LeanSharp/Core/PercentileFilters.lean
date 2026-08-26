/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.LayerFilters

/-!
# Percentile Z-Score Filtering

The paper *Sharpness-Aware Minimization with Z-Score Gradient Filtering*
(arXiv:2505.02369) thresholds by a **percentile** rather than by a fixed multiple
of the standard deviation: it keeps coordinate `j` exactly when

$$|\Omega(\nabla L(w))_j| > q_{Q_p},$$

with `q_{Q_p}` the `Q_p`-th percentile of the layer's absolute Z-scores. A fixed
`z * σ` threshold retains a count that varies with the gradient's distribution,
whereas the percentile fixes the *fraction* — which is the guarantee
`percentile_mask_sparsity` records below.

## Conventions

The paper does not state which percentile convention it uses, so this module fixes
the **nearest-rank** one and encodes it by *rank counting*: coordinate `i` is kept
when at least `⌈Q_p * n⌉` coordinates of its own layer have a strictly smaller
absolute deviation. For `Q_p > 0` this agrees with taking the nearest-rank
percentile of the absolute Z-scores and comparing strictly, and it avoids
formalizing sorted lists entirely.

Because the layer's `σ` is a common positive factor, comparing absolute Z-scores
is the same as comparing absolute deviations from the layer mean, so no division
appears and the `σ = 0` case needs no special handling. `percentile_mask_eq_zscore_rank`
records that bridge back to the paper's `Ω` form.

Ties are kept together: when every coordinate of a layer shares one absolute
deviation, no coordinate has a strictly smaller one, so for `Q_p > 0` the mask is
identically zero — matching the paper's strict `>` against a threshold that all
coordinates tie with.

## Main definitions

* `absDev`: a coordinate's absolute deviation from its own layer's mean.
* `strictlyBelow`: the coordinates of a layer with strictly smaller absolute deviation.
* `keptCoords`: the coordinates of a layer that survive the mask.
* `absZScore`: a coordinate's absolute Z-score within its own layer.
* `percentileTailMask`: the paper's percentile mask.
* `percentileFilteredGradient`: the gradient filtered by that mask.

## Main theorems

* `norm_sq_percentile_filtered_gradient_le`: the filter is an $L_2$ contraction.
* `norm_percentile_filtered_gradient_le`: norm-level form of the contraction.
* `percentile_mask_sparsity`: at most `n - ⌈Q_p * n⌉` coordinates of a layer survive.
* `percentile_mask_eq_zero_of_constant_fiber`: a constant layer keeps nothing.
* `absZScore_lt_iff_absDev_lt`: within a layer the absolute-Z-score ranking is the
  absolute-deviation ranking, whenever the standard deviation is positive.
-/

namespace LeanSharp

open BigOperators

variable {ι : Type*} [Fintype ι] {Λ : Type*} [DecidableEq Λ]

/-- The absolute deviation of coordinate `i` from the mean of its own layer. -/
noncomputable def absDev (g : W ι) (π : ι → Λ) (i : ι) : ℝ :=
  |(WithLp.equiv 2 (ι → ℝ) g) i - blockMean g π (π i)|

/-- The coordinates of `i`'s layer whose absolute deviation is strictly smaller
than `i`'s. Its cardinality is `i`'s rank within the layer. -/
noncomputable def strictlyBelow (g : W ι) (π : ι → Λ) (i : ι) : Finset ι :=
  (fiber π (π i)).filter fun k => absDev g π k < absDev g π i

/-- The paper's percentile mask, in rank-counting form: keep `i` exactly when at
least `⌈Q_p * n⌉` coordinates of its layer lie strictly below it, `n` being the
layer's size. -/
noncomputable def percentileTailMask (g : W ι) (π : ι → Λ) (Qp : ℝ) : W ι :=
  WithLp.equiv 2 (ι → ℝ) |>.symm fun i =>
    if ⌈Qp * ((fiber π (π i)).card : ℝ)⌉₊ ≤ (strictlyBelow g π i).card then 1 else 0

/-- The gradient filtered by the percentile mask: the paper's `∇L(w)_Ω`. -/
noncomputable def percentileFilteredGradient (g : W ι) (π : ι → Λ) (Qp : ℝ) : W ι :=
  hadamard g (percentileTailMask g π Qp)

/-- **Percentile Contraction**: the filter never increases the squared norm. -/
theorem norm_sq_percentile_filtered_gradient_le (g : W ι) (π : ι → Λ) (Qp : ℝ) :
    ‖percentileFilteredGradient g π Qp‖^2 ≤ ‖g‖^2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  apply Finset.sum_le_sum
  intro i _
  unfold percentileFilteredGradient hadamard percentileTailMask
  rw [WithLp.equiv_apply, Equiv.apply_symm_apply]
  dsimp only [ge_iff_le, WithLp.equiv_symm_apply, Real.norm_eq_abs]
  split_ifs
  · rw [mul_one, sq_abs]
  · simp only [
      mul_zero,
      ne_eq,
      OfNat.ofNat_ne_zero,
      not_false_eq_true,
      zero_pow,
      sq_abs
    ]
    positivity

/-- **Percentile Filtered Norm Bound**: norm-level form of the contraction. -/
theorem norm_percentile_filtered_gradient_le (g : W ι) (π : ι → Λ) (Qp : ℝ) :
    ‖percentileFilteredGradient g π Qp‖ ≤ ‖g‖ := by
  have h_sq := norm_sq_percentile_filtered_gradient_le g π Qp
  have h_sqrt := Real.sqrt_le_sqrt h_sq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h_sqrt
  exact h_sqrt

/-- The coordinates of layer `l` that the percentile mask keeps. -/
noncomputable def keptCoords (g : W ι) (π : ι → Λ) (Qp : ℝ) (l : Λ) : Finset ι :=
  (fiber π l).filter fun i =>
    ⌈Qp * ((fiber π (π i)).card : ℝ)⌉₊ ≤ (strictlyBelow g π i).card

/-- **Percentile Sparsity**: at most `n - ⌈Q_p * n⌉` of a layer's `n` coordinates
survive. This is the guarantee a fixed `z * σ` threshold cannot provide: the retained
*fraction* is pinned by `Q_p` alone, independent of how the gradient is distributed.

The proof takes the surviving coordinate of least absolute deviation. Everything
strictly below it is, by minimality, discarded, and there are at least `⌈Q_p * n⌉ `
such coordinates because that coordinate itself passed the mask. -/
theorem percentile_mask_sparsity (g : W ι) (π : ι → Λ) {Qp : ℝ} (hQ1 : Qp ≤ 1)
    (l : Λ) :
    (keptCoords g π Qp l).card + ⌈Qp * ((fiber π l).card : ℝ)⌉₊
      ≤ (fiber π l).card := by
  classical
  rcases (keptCoords g π Qp l).eq_empty_or_nonempty with hE | hNE
  · rw [hE]
    simp only [Finset.card_empty, zero_add, Nat.ceil_le]
    calc Qp * ((fiber π l).card : ℝ) ≤ 1 * ((fiber π l).card : ℝ) :=
          mul_le_mul_of_nonneg_right hQ1 (Nat.cast_nonneg _)
      _ = ((fiber π l).card : ℝ) := one_mul _
  · obtain ⟨i₀, hi₀mem, hi₀min⟩ :=
      (keptCoords g π Qp l).exists_min_image (absDev g π) hNE
    have hfib : π i₀ = l := by
      have := Finset.mem_filter.mp hi₀mem |>.1
      simpa only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] using this
    have hcard : ⌈Qp * ((fiber π l).card : ℝ)⌉₊ ≤ (strictlyBelow g π i₀).card := by
      have := (Finset.mem_filter.mp hi₀mem).2
      rwa [hfib] at this
    have hdisj : Disjoint (keptCoords g π Qp l) (strictlyBelow g π i₀) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      have h1 : absDev g π i₀ ≤ absDev g π a := hi₀min a ha
      have h2 : absDev g π a < absDev g π i₀ := (Finset.mem_filter.mp hb).2
      linarith
    have hsub : (keptCoords g π Qp l) ∪ (strictlyBelow g π i₀) ⊆ fiber π l := by
      intro a ha
      rcases Finset.mem_union.mp ha with h | h
      · exact (Finset.mem_filter.mp h).1
      · have := (Finset.mem_filter.mp h).1
        rwa [hfib] at this
    calc (keptCoords g π Qp l).card + ⌈Qp * ((fiber π l).card : ℝ)⌉₊
        ≤ (keptCoords g π Qp l).card + (strictlyBelow g π i₀).card := by omega
      _ = ((keptCoords g π Qp l) ∪ (strictlyBelow g π i₀)).card :=
          (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ (fiber π l).card := Finset.card_le_card hsub

/-- **Constant Layer Annihilation**: if every coordinate of a layer shares one absolute
deviation then none lies strictly below another, so for `Q_p > 0` the mask keeps
nothing. This mirrors `tail_filtered_gradient_eq_zero_of_std_zero` and is what makes the
`zsharpPerturbation` fallback reachable under a percentile threshold. -/
theorem percentile_mask_eq_zero_of_constant_fiber (g : W ι) (π : ι → Λ) {Qp : ℝ}
    (hQ : 0 < Qp) (i : ι) (hconst : ∀ k ∈ fiber π (π i), absDev g π k = absDev g π i)
    (hne : (fiber π (π i)).Nonempty) :
    (WithLp.equiv 2 (ι → ℝ) (percentileTailMask g π Qp)) i = 0 := by
  classical
  unfold percentileTailMask
  rw [Equiv.apply_symm_apply]
  have hsb : strictlyBelow g π i = ∅ := by
    unfold strictlyBelow
    rw [Finset.filter_eq_empty_iff]
    intro k hk
    rw [hconst k hk]
    exact lt_irrefl _
  rw [hsb, Finset.card_empty]
  have hpos : 0 < ⌈Qp * ((fiber π (π i)).card : ℝ)⌉₊ := by
    rw [Nat.lt_ceil]
    push_cast
    have : (0 : ℝ) < ((fiber π (π i)).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr hne
    positivity
  rw [if_neg (by omega)]

/-- A coordinate's absolute Z-score, normalized within its own layer: the `|Ω|` of
the paper. -/
noncomputable def absZScore (g : W ι) (π : ι → Λ) (i : ι) : ℝ :=
  absDev g π i / blockStd g π (π i)

/-- **Z-Score Ranking Bridge**: within one layer the standard deviation is a common
positive factor, so ranking by absolute Z-score — the paper's `|Ω(∇L(w))|` — is the
same as ranking by absolute deviation. This is why `percentileTailMask` can avoid
dividing, and with it the `σ = 0` case, without departing from the paper. -/
theorem absZScore_lt_iff_absDev_lt (g : W ι) (π : ι → Λ) (i k : ι) (hsame : π k = π i)
    (hpos : 0 < blockStd g π (π i)) :
    absZScore g π k < absZScore g π i ↔ absDev g π k < absDev g π i := by
  unfold absZScore
  rw [hsame]
  exact div_lt_div_iff_of_pos_right hpos

end LeanSharp
