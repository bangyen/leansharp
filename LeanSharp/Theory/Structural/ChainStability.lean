/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Models
import LeanSharp.Theory.Alignment
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Linarith

/-!
# Deep Model Stability Theorems

This module formalizes the collective stability of Z-score filtered gradients
across multi-layer neural network chains.

## Main definitions

* `CertifiedChain`: A dependently typed structure tracking stability property
  requirements for a `Chain`.
* `chainStabilityCertificate`: Recursively builds a stability certificate for
  a certified chain.

## Main theorems

* `zsharp_chain_stability`: Proves that layer-wise Z-score filtering ensures
  that the total norm of the filtered parameter updates is bounded by the total
  norm of the raw gradients.
-/

namespace LeanSharp

/-- A `CertifiedChain` is a dependent type over `Chain` that carries the
    necessary `NormedSpace` instances for stability certification. This avoids
    coupling the core `Chain` type with heavy analytical requirements. -/
inductive CertifiedChain : {In Out : Type} → Chain In Out → Type 1 where
  | single {In Out : Type} [NormedAddCommGroup In] [NormedSpace ℝ In]
      [NormedAddCommGroup Out] [NormedSpace ℝ Out] (L : Layer In Out) :
      CertifiedChain (.single L)
  | append {In Mid Out : Type} [NormedAddCommGroup In] [NormedSpace ℝ In]
      [NormedAddCommGroup Mid] [NormedSpace ℝ Mid]
      [NormedAddCommGroup Out] [NormedSpace ℝ Out] {c : Chain In Mid} :
      CertifiedChain c → (L : Layer Mid Out) → CertifiedChain (c.append L)

/-- Auxiliary function for `chainStabilityCertificate` using explicit index matching. -/
noncomputable def chainStabilityCertificate_aux :
  ∀ {In Out : Type} {c : Chain In Out}
    (nI : NormedAddCommGroup In) (sI : NormedSpace ℝ In)
    (nO : NormedAddCommGroup Out) (sO : NormedSpace ℝ Out)
    (_cc : CertifiedChain c)
    (_cert : ∀ {M1 M2 : Type} [NormedAddCommGroup M1] [NormedSpace ℝ M1]
       [NormedAddCommGroup M2] [NormedSpace ℝ M2] (L : Layer M1 M2) (_w : W L.ParamDim),
       StabilityCertificate M1 M2),
    (ChainData c) → @StabilityCertificate In Out nI sI nO sO
  | In, Out, _, nI, sI, nO, sO, @CertifiedChain.single _ _ _ _ _ _ L, cert, .single _ _w =>
      @cert In Out nI sI nO sO L _w
  | In, Out, _, nI, sI, nO, sO,
    @CertifiedChain.append _ Mid _ _ _ nM sM _ _ c_prev cc_prev L, cert, .append d_prev _w =>
      let cert_L := @cert Mid Out nM sM nO sO L _w
      let cert_prev :=
        @chainStabilityCertificate_aux In Mid c_prev nI sI nM sM cc_prev cert d_prev
      @StabilityCertificate.comp In Mid Out nI sI nM sM nO sO cert_L cert_prev

/-- **Chain Stability Certificate**: Recursively builds a stability certificate
    for a chain of layers. Using a simultaneous dependent match via an auxiliary
    function to strictly ensure typeclass index alignment. -/
noncomputable def chainStabilityCertificate {In Out : Type} {c : Chain In Out}
    [NormedAddCommGroup In] [NormedSpace ℝ In]
    [NormedAddCommGroup Out] [NormedSpace ℝ Out]
    (cc : CertifiedChain c)
    (cert : ∀ {M1 M2 : Type} [NormedAddCommGroup M1] [NormedSpace ℝ M1]
       [NormedAddCommGroup M2] [NormedSpace ℝ M2] (L : Layer M1 M2) (_w : W L.ParamDim),
       StabilityCertificate M1 M2) (d : ChainData c) : StabilityCertificate In Out :=
  chainStabilityCertificate_aux _ _ _ _ cc cert d

/-- **Chain-wise Stability**: For any network chain, applying Z-score
filtering layer-wise results in a total parameter update whose norm is bounded
by the norm of the raw (unfiltered) backpropagation gradients. -/
theorem zsharp_chain_stability {In Out : Type} {c : Chain In Out}
    (z : ℝ) (p : ChainData c) (x : In) (g_out : Out) :
    chainDataNormSq (backpropChain z p x g_out).1 ≤
    chainDataNormSq (rawBackpropChain p x g_out).1 := by
  induction c generalizing x with
  | single L =>
      cases p
      unfold backpropChain rawBackpropChain chainDataNormSq
      simp only [norm_sq_filtered_gradient_le]
  | append prev L ih =>
      cases p with | append p_prev w =>
      unfold backpropChain rawBackpropChain chainDataNormSq
      apply add_le_add (ih p_prev _ _) (norm_sq_filtered_gradient_le _ _)

end LeanSharp
