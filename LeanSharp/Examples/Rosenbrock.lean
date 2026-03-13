/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Landscape
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Dual

set_option linter.unusedSimpArgs false

namespace LeanSharp.Rosenbrock

open BigOperators

local notation "W2" => W (Fin 2)

/-- The 2D Rosenbrock function: $L(x, y) = (1 - x)^2 + 100(y - x^2)^2$. -/
noncomputable def L_rosenbrock (w : W2) : ℝ :=
  (1 - w 0)^2 + 100 * (w 1 - (w 0)^2)^2

/-- The analytical gradient of $L_{rosenbrock}$. -/
noncomputable def exact_gradient_rosenbrock (w : W2) : W2 :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm fun i =>
    if i = 0 then
      -2 * (1 - w 0) - 400 * w 0 * (w 1 - (w 0)^2)
    else
      200 * (w 1 - (w 0)^2)

/-- Derivative of the first term $(1 - x)^2$. -/
lemma hasFDerivAt_rosenbrock_term1 (w : W2) :
    HasFDerivAt (fun x : W2 => (1 - x 0)^2) ((-2 * (1 - w 0)) • EuclideanSpace.proj (ι := Fin 2) (𝕜 := ℝ) 0) w := by
  let p0 : W2 →L[ℝ] ℝ := EuclideanSpace.proj (ι := Fin 2) (𝕜 := ℝ) 0
  have h0 : HasFDerivAt (fun x : W2 => x 0) p0 w := p0.hasFDerivAt
  have h_sub : HasFDerivAt (fun x => 1 - x 0) (-p0) w := by
    have h_c := hasFDerivAt_const (1 : ℝ) w
    convert h_c.sub h0 using 1
    ext; simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.zero_apply,
      Pi.sub_apply, zero_sub, ContinuousLinearMap.neg_apply]
  convert h_sub.pow 2 using 1
  ext; simp only [Pi.pow_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply,
    smul_eq_mul]; ring

/-- Derivative of the second term $100(y - x^2)^2$. -/
lemma hasFDerivAt_rosenbrock_term2 (w : W2) :
    HasFDerivAt (fun x : W2 => 100 * (x 1 - (x 0)^2)^2)
      ((-400 * w 0 * (w 1 - (w 0)^2)) • EuclideanSpace.proj (ι := Fin 2) (𝕜 := ℝ) 0 +
       (200 * (w 1 - (w 0)^2)) • EuclideanSpace.proj (ι := Fin 2) (𝕜 := ℝ) 1) w := by
  let p0 : W2 →L[ℝ] ℝ := EuclideanSpace.proj (ι := Fin 2) (𝕜 := ℝ) 0
  let p1 : W2 →L[ℝ] ℝ := EuclideanSpace.proj (ι := Fin 2) (𝕜 := ℝ) 1
  have h0 : HasFDerivAt (fun x : W2 => x 0) p0 w := p0.hasFDerivAt
  have h1 : HasFDerivAt (fun x : W2 => x 1) p1 w := p1.hasFDerivAt
  have h_xsq : HasFDerivAt (fun x => (x 0)^2) ((2 * w 0) • p0) w := by
    convert h0.pow 2 using 1
    ext; simp only [Pi.pow_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring
  have h_inner : HasFDerivAt (fun x => x 1 - (x 0)^2) (p1 - (2 * w 0) • p0) w := h1.sub h_xsq
  have h_sq : HasFDerivAt (fun x => (x 1 - (x 0)^2)^2)
      ((2 * (w 1 - (w 0)^2)) • (p1 - (2 * w 0) • p0)) w := by
    convert h_inner.pow 2 using 1
    ext; simp only [Pi.pow_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring
  convert h_sq.const_smul 100 using 1
  · ext x
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, Pi.smul_apply, smul_eq_mul, smul_smul]
    ring
  · ext x; simp only [Pi.smul_apply, smul_eq_mul, Pi.pow_apply]; ring

/-- The analytical Fréchet derivative of $L_{rosenbrock}$. -/
lemma hasFDerivAt_rosenbrock (w : W2) :
    HasFDerivAt L_rosenbrock ((-2 * (1 - w 0) - 400 * w 0 * (w 1 - (w 0)^2)) •
      EuclideanSpace.proj (ι := Fin 2) (𝕜 := ℝ) 0 +
      (200 * (w 1 - (w 0)^2)) • EuclideanSpace.proj (ι := Fin 2) (𝕜 := ℝ) 1) w := by
  convert (hasFDerivAt_rosenbrock_term1 w).add (hasFDerivAt_rosenbrock_term2 w) using 1
  ext x; simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sub_apply, smul_eq_mul]; ring

/-- Helper for coordinate-wise evaluation of the Riesz representative. -/
lemma coordinate_dual_apply (g : W2 →L[ℝ] ℝ) (i : Fin 2) :
    ((InnerProductSpace.toDual ℝ W2).symm g) i = g (EuclideanSpace.single i (1 : ℝ)) := by
  let v := (InnerProductSpace.toDual ℝ W2).symm g
  have hv : @inner ℝ W2 _ v (EuclideanSpace.single i (1 : ℝ)) = v i := by
    simp only [EuclideanSpace.inner_single_right, starRingEnd_apply, star_trivial, one_mul]
  rw [← hv, InnerProductSpace.toDual_symm_apply]

/-- **Gradient Identity**: The analytical gradient matches the Fréchet gradient. -/
theorem gradient_rosenbrock_eq (w : W2) :
    gradient L_rosenbrock w = exact_gradient_rosenbrock w := by
  let g_0 : W2 →L[ℝ] ℝ := (-2 * (1 - w 0) - 400 * w 0 * (w 1 - (w 0)^2)) •
    EuclideanSpace.proj (ι := Fin 2) (𝕜 := ℝ) 0
  let g_1 : W2 →L[ℝ] ℝ := (200 * (w 1 - (w 0)^2)) • EuclideanSpace.proj (ι := Fin 2) (𝕜 := ℝ) 1
  let g_a := g_0 + g_1
  have hL : HasFDerivAt L_rosenbrock g_a w := hasFDerivAt_rosenbrock w
  unfold gradient
  rw [hL.fderiv]
  ext i
  unfold exact_gradient_rosenbrock
  fin_cases i
  · rw [coordinate_dual_apply]
    simp only [exact_gradient_rosenbrock, g_a, g_0, g_1, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, PiLp.proj_apply,
      EuclideanSpace.single, Pi.single_apply, WithLp.equiv_symm_apply]
    split_ifs <;> try contradiction
    try simp only [one_mul, zero_mul, add_zero, sub_zero, zero_sub]
    ring
  · rw [coordinate_dual_apply]
    simp only [exact_gradient_rosenbrock, g_a, g_0, g_1, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, PiLp.proj_apply,
      EuclideanSpace.single, Pi.single_apply, WithLp.equiv_symm_apply]
    split_ifs <;> try contradiction
    try simp only [one_mul, zero_mul, add_zero, sub_zero, zero_sub]
    ring

/-- **L-Smoothness**: The Rosenbrock function is $L$-smooth on any compact set.
    For simplicity, we show it is locally $L$-smooth at any point. -/
lemma rosenbrock_locally_L_smooth (w : W2) :
    ∃ L > 0, ∀ v ∈ Metric.ball w 1, ∀ u ∈ Metric.ball w 1,
      ‖gradient L_rosenbrock u - gradient L_rosenbrock v‖ ≤ L * ‖u - v‖ := by
  sorry

end LeanSharp.Rosenbrock
