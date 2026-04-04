# LeanSharp API Design & Documentation

This document describes the design philosophy, architectural structure, and formal theorem registry of the `LeanSharp` project. It serves as the primary reference for understanding how the library's components interact and the mathematical justifications for its design.

---

## 1. Design Philosophy

The `LeanSharp` API is built on three core pillars:

### A. Compositional Formalism
Neural networks are not modeled as monolithic functions but as a **Chain of Layers**. By defining a recursive `Chain` structure, we allow formal proofs to proceed by induction over the network's depth. This compositionality ensures that properties proven for a single `Layer` (like Z-score stability) automatically lift to the entire architecture.

### B. The Statistical-Geometric Bridge
The primary innovation of this project is the integration of **Z-score gradient filtering** into the Sharpness-Aware Minimization (SAM) framework. The API is designed to bridge:
- **Geometry**: The curvature of the loss landscape (Hessian).
- **Statistics**: The distribution of gradient components (Mean, Variance, Z-scores).

The documentation of theorems focuses on how statistical operations (like filtering) preserve geometric properties (like descent alignment).

### C. Proof-Oriented Regularization
Every definition in the API is chosen to facilitate formal verification. For example, using `EuclideanSpace ℝ ι` for weights allows us to leverage Mathlib's extensive inner product space and calculus libraries directly.

---

## 2. Overarching Design Goals

To achieve the pillars above, the library adheres to four abstract design mandates:

### Goal 1: Universal Stability Certification
Every component (Layer, Filter, Objective) MUST expose a formal `StabilityCertificate`. We have moved from "implicit stability" (assuming a layer is well-behaved) to "explicit certification" (providing a term that bundles Lipschitz and differentiability proofs).

### Goal 2: Inductive Property Propagation
The API is designed for **Recursive Verification**. Model-level guarantees should never be proven from scratch; they must be derived via generic induction over the `Chain` structure using propagation theorems like `chainStabilityCertificate`.

### Goal 3: Geometric-Statistical Alignment
Statistical normalization (BatchNorm, LayerNorm) and filtering (Z-score) must be mathematically "aligned" with the descent direction. The API enforces this through unified `AlignmentCondition` contracts, ensuring that data-driven transformations do not destroy the first-order optimization signal.

### Goal 4: Deterministic Projections of Stochasticity
To verify inherently non-deterministic layers (like Dropout), the API utilizes a **Fixed-Mask Projection**. This allows us to treat a stochastic layer as a parameterized family of deterministic functions, resolving the paradox between randomness and formal differentiability.

---

## 3. Architectural Justification

The project is organized into four main functional areas:

### `LeanSharp/Core`
- **Purpose**: Foundations and primitives.
- **Justification**: Contains the "ground truth" definitions (Landscape, Stats, Filters, Models). By keeping these narrow and dependency-free (other than Mathlib), we ensure that the core logic is stable and easier to audit.

### `LeanSharp/Theory`
- **Purpose**: Mathematical guarantees.
- **Justification**: Separated into `Robustness`, `Dynamics`, and `Structural`.
    - `Robustness`: High-level guarantees against data/gradient contamination.
    - `Dynamics`: Proofs about the training process (convergence).
    - `Structural`: Invariance and regularity properties of the model architecture.

### `LeanSharp/Layers`
- **Purpose**: A library of verified components.
- **Justification**: Modularized into `Basic`, `Normalization`, and `Specialized` folders to allow developers to find and verify specific layer types (e.g., `BatchNorm` vs `ReLU`) without cluttering the core theory modules.

### `LeanSharp/Tactic`
- **Purpose**: Developer ergonomics.
- **Justification**: Contains `zsharp_solve`, a custom tactic that automates the idiosyncratic steps of Z-score proofs (unfolding filters, handling `if-then-else` splits).

---

## 3. Theorem Registry

This section lists each significant theorem, its role, and the rationale for its visibility.

### `LeanSharp.Core.Filters`

| Theorem | Visibility | Justification |
| :--- | :--- | :--- |
| `norm_sq_filteredGradient_le` | **Public** | Essential for proving the filter is an $L_2$ contraction. High-level stability proofs depend on this. |
| `norm_filteredGradient_le` | **Public** | API convenience; a non-squared version of the contraction lemma for simpler norm bounds. |
| `zScoreMask_nonempty` | **Public** | Guarantees the filter doesn't zero out the gradient for reasonable thresholds ($z \le 1$). Vital for progress guarantees. |
| `zScoreMask_nonempty_contradiction`| **Private** | An internal proof by contradiction used solely by `zScoreMask_nonempty`. |
| `filteredGradient_eq_self_of_std_zero`| **Public** | Proves stability for constant gradients (zero variance). Justifies filter behavior in low-noise regimes. |
| `zScoreMask_idempotent` | **Public** | Structural property of the mask; used in algebraic simplifications of filtered updates. |

### `LeanSharp.Core.Landscape`

| Theorem | Visibility | Justification |
| :--- | :--- | :--- |
| `hessian_symmetric` | **Public** | Established via Schwarz's Theorem for $C^2$ functions. Fundamental for all second-order optimization analysis. |
| `hessian_def_riesz_comp` | **Private** | Technical lemma relating the Hessian to the Riesz representation. Implementation detail. |
| `hessian_symmetry_reduction` | **Private** | Internal reduction step for the symmetry proof. |
| `norm_sub_smul_sq` | **Public** | Geometric identity for descent steps. Used widely in convergence proofs. |

### `LeanSharp.Core.Objective`

| Theorem | Visibility | Justification |
| :--- | :--- | :--- |
| `samObjective_ge_self` | **Public** | Baseline property of SAM: the perturbed loss is always at least the original loss. |
| `differentiableAt_samPerturbation` | **Public** | Justifies the use of calculus on the SAM update vector itself. |

### `LeanSharp.Theory.Robustness.Alignment`

| Theorem | Visibility | Justification |
| :--- | :--- | :--- |
| `alignment_filtered_gradient` | **Public** | **Key Result**: Proves that filtering preserves the descent direction if "bad" components are removed. |
| `inner_hadamard_comm` | **Private** | Lemma for converting Hadamard products into sums for inner product analysis. |

### `LeanSharp.Theory.Robustness.PacBayes`

| Theorem | Visibility | Justification |
| :--- | :--- | :--- |
| `zsharp_gap_benefit` | **Public** | Formal proof that filtering strictly reduces the generalization gap in the Taylor regime. |
| `standard_bound_of_zsharp` | **Public** | Establishes `ZSharp` as a tighter/stricter generalization basis than standard SAM. |
| `filtered_rademacher_le` | **Public** | Proves that the complexity of the hypothesis class is reduced by the filter. |

### `LeanSharp.Theory.Dynamics.Convergence`

| Theorem | Visibility | Justification |
| :--- | :--- | :--- |
| `zsharp_convergence` | **Public** | **Main Result**: Proof of geometric convergence to the optimum under alignment assumptions. |

### `LeanSharp.Theory.Structural.HessianContraction`

| Theorem | Visibility | Justification |
| :--- | :--- | :--- |
| `zsharp_curvature_bound` | **Public** | Relates filter contraction to Hessian sharpness. The "bridge" between stats and landscape geometry. |
| `generalized_filter_condition...` | **Public** | Abstract template for proving new filters satisfy curvature contracts. |

### `LeanSharp.Theory.Alignment`

| Theorem | Visibility | Justification |
| :--- | :--- | :--- |
| `alignment_condition_of_signal_noise` | **Public** | Bridge theorem proving that Z-score filtering preserves alignment in stochastic signal-noise models. |
| `inner_hadamard_comm` | **Private** | Technical lemma for resolving inner products over element-wise masks. |

### `LeanSharp.Theory.Structural.ChainStability`

| Theorem | Visibility | Justification |
| :--- | :--- | :--- |
| `chainStabilityCertificate` | **Public** | Recursive constructor for model-level stability certificates via induction over the `Chain` structure. |
| `zsharp_chain_stability` | **Public** | Global stability proof for multi-layer architectures using layer-wise filtering. |

### `LeanSharp.Layers.Basic`

| Theorem | Visibility | Justification |
| :--- | :--- | :--- |
| `dropout_contDiff` | **Public** | Establishes $C^2$ regularity for Dropout under the Fixed-Mask Projection. |
| `contDiff_softmax` | **Public** | Formal proof of $C^2$ smoothness for the Softmax activation. |
| `contDiff_smoothRelu` | **Public** | Justifies use of Softplus as a formally verifiable alternative to ReLU for Hessian analysis. |

---

## 4. The Certification System

LeanSharp uses a formal **Certification Framework** to ensure that mathematical properties are not just claimed, but carried as terms in the library's logic.

### `StabilityCertificate`
A certificate bundles the forward pass `f` with:
- A Lipschitz constant `K`.
- A proof that `f` is `LipschitzWith K`.
- A proof that `f` is `ContDiff ℝ 2`.

### Recursive Propagation
Stability is never verified for a large model as a single block. Instead:
1. Individual **Layers** provide certificates (e.g., `linearCertificate`, `batchnormCertificate`).
2. The **Chain Stability** module provides `chainStabilityCertificate`, which uses `StabilityCertificate.comp` to recursively fold these properties through the network.

---

## 5. Regularity Hierarchy

To support second-order (Hessian-based) sharpness analysis, LeanSharp enforces a strict regularity hierarchy:

- **$C^0$ (Continuous)**: Standard ReLU and basic piecewise functions. Suitable for basic convergence but NOT for sharpness analysis.
- **$C^1$ (Differentiable)**: Basic linear layers and primitives.
- **$C^2$ (Twice-Differentiable)**: Required for curvature theorems. The API promotes `smoothReluLayer` (Softplus) and `softmaxLayer` as the certified standard for robust architectures.

---

## 6. Stochasticity & Projections

A recurring challenge in formal verification is the non-differentiable nature of stochastic operations. LeanSharp resolves this through **Stochastic Projection**.

### The Fixed-Mask Paradox
In `Dropout.lean`, we acknowledge that while dropout is stochastic at runtime, its formal properties are analyzed through a **Fixed-Mask Projection**. We treat the dropout layer as a deterministic linear operator for a given mask. This allows us to prove $C^2$ regularity and Lipschitz bounds that hold *for any mask*, which then lifts to the stochastic expectation in the `StochasticAlignmentCondition`.
