/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Theory.Dynamics.Convergence
import LeanSharp.Theory.Structural.ChainStability

/-!
# Chain Convergence Sharpness

This module tightens the geometric convergence rate of ZSharp by explicitly
connecting it to the recursive Lipschitz constants (stability certificates)
of multilayer chains.

## Definitions

* `ChainZSharpModel`: A ZSharp model specialized for neural network chains.

## Theorems

* `zsharp_chain_convergence`: Tightened convergence bound for chains using
  explicit Lipschitz constants.
-/

namespace LeanSharp

variable {In Out : Type} [NormedAddCommGroup In] [NormedSpace ℝ In]
  [NormedAddCommGroup Out] [NormedSpace ℝ Out]

/-- A ZSharp model explicitly instantiated for a neural network chain,
    where the objective smoothness is bounded by the chain's certified
    Lipschitz constant. -/
structure ChainZSharpModel (c : Chain In Out) extends ZSharpModel c.ParamDim where
  /-- The certified chain property, ensuring each layer is stable. -/
  cc : CertifiedChain c
  /-- A certificate generator that provides stability proof for each constituent layer. -/
  cert : ∀ {M1 M2 : Type} [NormedAddCommGroup M1] [NormedSpace ℝ M1]
         [NormedAddCommGroup M2] [NormedSpace ℝ M2] (L : Layer M1 M2) (_w : W L.ParamDim),
         StabilityCertificate M1 M2
  /-- The operational data for the chain, containing the weights for each layer. -/
  data : ChainData c
  /-- The overall smoothness is bounded by the chain's Lipschitz constant K. -/
  h_smooth_bound : (L.smoothness : ℝ) ≤ (chainStabilityCertificate cc cert data).K

/-- **Tightened Chain Convergence**: Specializes the abstract `zsharp_convergence`
    to chains, utilizing the explicit Lipschitz bounds from `StabilityCertificate`
    to tighten the required local learning rate bound. -/
theorem zsharp_chain_convergence {c : Chain In Out} (M : ChainZSharpModel c) (η : ℕ → ℝ)
    (hη_pos : ∀ t, 0 ≤ η t)
    (hη_tight : ∀ t, η t * ((chainStabilityCertificate M.cc M.cert M.data).K : ℝ) ^ 2 ≤
      M.L.μ)
    (hμL : M.L.μ < (M.L.smoothness : ℝ)) :
    ZSharpConvergenceHolds M.L.toFun M.w_star η M.ρ M.z (M.L.smoothness : ℝ) M.L.μ := by
  have hk_nonneg : 0 ≤ ((chainStabilityCertificate M.cc M.cert M.data).K : ℝ) := NNReal.coe_nonneg _
  have hs_nonneg : 0 ≤ (M.L.smoothness : ℝ) := NNReal.coe_nonneg _
  apply zsharp_convergence M.toZSharpModel η
  · intro t
    have h_smooth_sq : (M.L.smoothness : ℝ) ^ 2 ≤
        ((chainStabilityCertificate M.cc M.cert M.data).K : ℝ) ^ 2 := by
      nlinarith [M.h_smooth_bound, hs_nonneg, hk_nonneg]
    have h1 : η t * (M.L.smoothness : ℝ) ^ 2 ≤
        η t * ((chainStabilityCertificate M.cc M.cert M.data).K : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left h_smooth_sq (hη_pos t)
    linarith [hη_tight t]
  · exact hμL

end LeanSharp
