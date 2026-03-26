/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters
import LeanSharp.Core.Landscape
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Deep Model Foundations

This module formalizes multi-layer neural network architectures and the
backpropagation algorithm, integrated with Z-score gradient filtering.

## Main definitions

* `Layer`: An abstract structure for a neural network layer.
* `Chain`: A recursive structure for composing multiple `Layer`s.
* `ChainData`: A type-indexed structure for storing parameters/gradients.
* `backpropChain`: Recursive computation of filtered gradients through a chain.
* `rawBackpropChain`: Standard backpropagation without Z-score filtering (for theory).
-/

namespace LeanSharp

/-- A Neural Network Layer is characterized by its input/output spaces,
    its parameter space, and its forward/backward maps. -/
structure Layer (Input : Type) (Output : Type) where
  /-- The index type for the parameter space. -/
  ParamDim : Type
  /-- The Fintype instance for the parameter index type. -/
  fintypeParamDim : Fintype ParamDim
  /-- Forward pass: maps parameters and input to an output. -/
  forward : W ParamDim → Input → Output
  /-- Backward pass: takes params, input, and gradient w.r.t output.
      Returns (gradient w.r.t params, gradient w.r.t input). -/
  backward : W ParamDim → Input → Output → W ParamDim × Input

/-- Expose the Fintype instance for type class resolution. -/
instance {In Out : Type} (L : Layer In Out) : Fintype L.ParamDim := L.fintypeParamDim

/-- A Chain of layers composing Input -> ... -> Output. -/
inductive Chain : Type → Type → Type 1 where
  | single {In Out : Type} : Layer In Out → Chain In Out
  | append {In Mid Out : Type} : Chain In Mid → Layer Mid Out → Chain In Out

/-- The number of layers in a chain. -/
def Chain.length {In Out : Type} : Chain In Out → ℕ
  | .single _ => 1
  | .append prev _ => prev.length + 1

/-- Concatenate two chains. -/
def Chain.concat {In Mid Out : Type} (c1 : Chain In Mid) : Chain Mid Out → Chain In Out
  | .single L => Chain.append c1 L
  | .append prev L => Chain.append (Chain.concat c1 prev) L

/-- Data (parameters or gradients) for a specific chain. -/
inductive ChainData : {In Out : Type} → Chain In Out → Type 1 where
  | single {In Out : Type} (L : Layer In Out) :
      W L.ParamDim → ChainData (.single L)
  | append {In Mid Out : Type} {prev : Chain In Mid} {L : Layer Mid Out} :
      ChainData prev → W L.ParamDim → ChainData (.append prev L)

/-- The squared Frobenius/Euclidean norm of all elements in a ChainData. -/
noncomputable def chainDataNormSq {In Out : Type} {c : Chain In Out} :
    ChainData c → ℝ :=
  match c with
  | .single _ => fun d =>
      match d with
      | .single _ w => ‖w‖^2
  | .append _ _ => fun d =>
      match d with
      | .append d_prev w => chainDataNormSq d_prev + ‖w‖^2

/-- Forward pass through a chain of layers. -/
def forwardChain {In Out : Type} {c : Chain In Out} :
    ChainData c → In → Out :=
  match c with
  | .single L => fun p x =>
      match p with
      | .single _ w => L.forward w x
  | .append _prev L => fun p x =>
      match p with
      | .append p_prev w => L.forward w (forwardChain p_prev x)

/-- Forward pass through a chain of layers. Alias for `forwardChain`. -/
abbrev Chain.forward {In Out : Type} {c : Chain In Out}
    (p : ChainData c) (x : In) : Out :=
  forwardChain p x

/-- Recursive backpropagation through a chain.
    Applies Z-score filtering at each layer. -/
noncomputable def backpropChain {In Out : Type} {c : Chain In Out}
    (z : ℝ) (p : ChainData c) (x : In) (g_out : Out) :
    ChainData c × In :=
  match c with
  | .single L =>
      match p with
      | .single _ w =>
          let (g_w, g_in) := L.backward w x g_out
          (.single L (filteredGradient g_w z), g_in)
  | .append _prev L =>
      match p with
      | .append p_prev w =>
          let mid_in := forwardChain p_prev x
          let (g_w_L, g_mid) := L.backward w mid_in g_out
          let (g_prevs, g_in) := backpropChain z p_prev x g_mid
          (.append g_prevs (filteredGradient g_w_L z), g_in)

/-- Recursive backpropagation through a chain without filtering. -/
noncomputable def rawBackpropChain {In Out : Type} {c : Chain In Out}
    (p : ChainData c) (x : In) (g_out : Out) :
    ChainData c × In :=
  match c with
  | .single L =>
      match p with
      | .single _ w =>
          let (g_w, g_in) := L.backward w x g_out
          (.single L g_w, g_in)
  | .append _prev L =>
      match p with
      | .append p_prev w =>
          let mid_in := forwardChain p_prev x
          let (g_w_L, g_mid) := L.backward w mid_in g_out
          let (g_prevs, g_in) := rawBackpropChain p_prev x g_mid
          (.append g_prevs g_w_L, g_in)

end LeanSharp
