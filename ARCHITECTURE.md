# LeanSharp Architecture

This document provides a technical overview of the `LeanSharp` project's design patterns and core abstractions. It is intended for developers who wish to contribute to the formal verification of Sharpness-Aware Minimization (SAM).

## Core Abstractions

### Parameter Space (`W`)
The project uses `W ι` (equivalent to `EuclideanSpace ℝ ι`) as the primary representation for parameter tensors. This allows for a unified treatment of weights, gradients, and perturbations as vectors in an inner product space.

### Layer and Chain
The project models neural networks as a composition of abstract layers.

- **`Layer In Out`**: A structure containing the parameter dimension (`ParamDim`), a forward pass, and a backward pass.
- **`Chain In Out`**: An inductive type representing a sequence of layers.
- **`ChainData c`**: A type-indexed structure that stores the actual parameters (of type `W`) for each layer in a `Chain`.

> [!TIP]
> When implementing a new layer, ensure you define a corresponding `ParamDim` and provide a `Fintype` instance for it. This allows the `Layer` structure to automatically manage the parameter space.

## Statistical Filtering Framework

Z-Score filtering is implemented via three core operators in `LeanSharp.Core.Filters`:

1.  **`zScoreMask g z`**: Generates a boolean-valued vector in $\{0, 1\}^d$. It marks components that deviate from the vector mean by more than `z` standard deviations.
2.  **`hadamard a b`**: Performs element-wise multiplication, used to apply masks to gradient tensors.
3.  **`filteredGradient g z`**: Returns the product of the gradient and its Z-score mask.

The framework provides proofs for **Mask Contraction** ($\|g_{filt}\| \le \|g\|$) and **Non-emptiness** (the filter preserves at least one component for $z \le 1$).

## The Alignment Bridge

The `AlignmentCondition` links the deterministic geometry of the loss landscape to the stochastic behavior of the gradient filter.

- **`AlignmentCondition`**: Defines when a descent direction is "well-aligned" with the global minimum.
- **`StochasticAlignmentCondition`**: Generalizes alignment for stochastic processes, ensuring that the *expected* progress remains positive after filtering and noise.
- **`alignment_filtered_gradient`**: A core theorem proving that Z-score filtering preserves alignment under specific signal-noise conditions.

## Stability Certificates

To support Hessian-based analysis, LeanSharp enforces regularity constraints through `StabilityCertificate`.

- **`StabilityCertificate α β`**: Bundles a mapping `f: α → β` with a Lipschitz constant `K` and a proof of $C^2$ smoothness (`ContDiff ℝ 2`).
- **Composition**: Certificates are composable; the composition of two $C^2$ layers is guaranteed to be $C^2$ with a product Lipschitz constant.

## Proof Automation

### `zsharp_solve`
To simplify proofs involving Z-score filtering and Hadamard products, use the `zsharp_solve` tactic. It automates:
1. Unfolding of core filtering definitions (`filteredGradient`, `zScoreMask`).
2. Simplification of `WithLp` and `EuclideanSpace` projections.
3. Case splitting on `if-then-else` blocks (common in filtering logic).
4. Terminal calls to `linarith`, `positivity`, and `aesop`.

## Project Structure

- `LeanSharp/Core`: Foundations (Landscape, Models, Stats, Filters).
- `LeanSharp/Theory`: Mathematical proofs.
    - `Alignment.lean`: The core bridge theory and certificates.
    - `Robustness/`: Generalization bounds (PAC-Bayes) and breakdown analysis.
    - `Structural/`: Layer-specific regularity and invariance properties.
    - `Dynamics.lean`: Convergence and stability over time.
- `LeanSharp/Layers`: Specific neural network components (Linear, ReLU, Normalization).
- `LeanSharp/Tactic`: Custom proof automation.
- `Tests/`: Structural and functional verification.
