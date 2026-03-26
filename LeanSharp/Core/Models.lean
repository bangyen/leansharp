/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters
import LeanSharp.Core.Landscape
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fintype.Basic

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

/-- **Broadcast Layer**: Lifts a layer $f: W \iota_{in} \to W \iota_{out}$ to operate on a
    higher-dimensional space $W (\kappa \times \iota_{in}) \to W (\kappa \times \iota_{out})$
    by applying it independently to each slice $\kappa$. -/
noncomputable def broadcastLayer (κ : Type) [Fintype κ] {ι_in ι_out : Type}
    (L : Layer (W ι_in) (W ι_out)) : Layer (W (κ × ι_in)) (W (κ × ι_out)) where
  ParamDim := L.ParamDim
  fintypeParamDim := L.fintypeParamDim
  forward w x :=
    WithLp.equiv 2 _ |>.symm fun (k, i) =>
      let slice := WithLp.equiv 2 _ |>.symm fun i' => (WithLp.equiv 2 _ x) (k, i')
      (WithLp.equiv 2 _ (L.forward w slice)) i
  backward w x g_out :=
    let x_f := WithLp.equiv 2 _ x
    let g_out_f := WithLp.equiv 2 _ g_out
    let g_step (k : κ) :=
      let slice := WithLp.equiv 2 _ |>.symm fun i' => x_f (k, i')
      let g_out_slice := WithLp.equiv 2 _ |>.symm fun i' => g_out_f (k, i')
      L.backward w slice g_out_slice
    let g_w := ∑ k, (g_step k).1
    let g_x := WithLp.equiv 2 _ |>.symm fun (k, i) =>
      (WithLp.equiv 2 _ (g_step k).2) i
    (g_w, g_x)

/-- **Map Layer**: Lifts a layer $f: \mathbb{R} \to \mathbb{R}$ to operate on a
    vector space $W \iota$ by applying it element-wise. -/
noncomputable def mapLayer (ι : Type) [Fintype ι]
    (f : Layer ℝ ℝ) : Layer (W ι) (W ι) where
  ParamDim := f.ParamDim
  fintypeParamDim := f.fintypeParamDim
  forward w x :=
    WithLp.equiv 2 _ |>.symm fun i => f.forward w ((WithLp.equiv 2 _ x) i)
  backward w x g_out :=
    let x_f := WithLp.equiv 2 _ x
    let g_out_f := WithLp.equiv 2 _ g_out
    let g_step (i : ι) := f.backward w (x_f i) (g_out_f i)
    let g_w := ∑ i, (g_step i).1
    let g_x := WithLp.equiv 2 _ |>.symm fun i => (g_step i).2
    (g_w, g_x)

/-- The parameter index type for a chain. -/
def Chain.ParamDim {In Out : Type} : Chain In Out → Type
  | .single L => L.ParamDim
  | .append prev L => prev.ParamDim ⊕ L.ParamDim

/-- Instance for Fintype on Chain.ParamDim. -/
def Chain.ParamDimFintype {In Out : Type} (c : Chain In Out) : Fintype c.ParamDim :=
  match c with
  | .single L => L.fintypeParamDim
  | .append prev L =>
      let _ := Chain.ParamDimFintype prev
      let _ := L.fintypeParamDim
      (inferInstance : Fintype (prev.ParamDim ⊕ L.ParamDim))

attribute [instance] Chain.ParamDimFintype

/-- Flatten a `ChainData` recursive structure into a single parameter vector. -/
noncomputable def ChainData.toVector {In Out : Type} {c : Chain In Out} :
    ChainData c → W c.ParamDim :=
  match c with
  | .single _ => fun d =>
      match d with
      | .single _ w => w
  | .append prev L => fun d =>
      match d with
      | .append d_prev w =>
          have := Chain.ParamDimFintype prev
          have := L.fintypeParamDim
          WithLp.equiv 2 _ |>.symm fun
            | Sum.inl i => (WithLp.equiv 2 _ (ChainData.toVector d_prev)) i
            | Sum.inr i => (WithLp.equiv 2 _ w) i

/-- Convert a vector in W (Chain.ParamDim) back to ChainData. -/
noncomputable def Chain.toData {In Out : Type} (c : Chain In Out) :
    W c.ParamDim → ChainData c :=
  match c with
  | .single L => fun w => .single L w
  | .append prev L => fun w =>
      let _ := Chain.ParamDimFintype prev
      let _ := L.fintypeParamDim
      let w_f := WithLp.equiv 2 _ w
      let d_prev := Chain.toData prev (WithLp.equiv 2 _ |>.symm (fun i => w_f (Sum.inl i)))
      let w_L := WithLp.equiv 2 _ |>.symm (fun i => w_f (Sum.inr i))
      ChainData.append d_prev w_L

/-- **Chain-to-Layer Bridge**: Converts a `Chain` into a single `Layer` by
    bundling its recursive parameter structure. This allows chains to be
    wrapped in `residualLayer` or further composed as units. -/
noncomputable def Chain.toLayer {In Out : Type} (c : Chain In Out) :
    Layer In Out where
  ParamDim := c.ParamDim
  fintypeParamDim := inferInstance
  forward w x := forwardChain (c.toData w) x
  backward w x g_out :=
    let (g_data, g_in) := rawBackpropChain (c.toData w) x g_out
    (g_data.toVector, g_in)

end LeanSharp
