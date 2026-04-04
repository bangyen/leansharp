# LeanSharp Architecture

This document provides a technical overview of the `LeanSharp` project's design patterns and core abstractions. It is intended for developers who wish to contribute to the formal verification of Sharpness-Aware Minimization (SAM).

## Core Abstractions

### Layer and Chain
The project models neural networks as a composition of abstract layers.

- **`Layer In Out`**: A structure containing the parameter dimension (`ParamDim`), a forward pass, and a backward pass.
- **`Chain In Out`**: An inductive type representing a sequence of layers.
- **`ChainData c`**: A type-indexed structure that stores the actual parameters (of type `W`) for each layer in a `Chain`.

> [!TIP]
> When implementing a new layer, ensure you define a corresponding `ParamDim` and provide a `Fintype` instance for it. This allows the `Layer` structure to automatically manage the parameter space.

## Proof Automation

### `zsharp_solve`
To simplify proofs involving Z-score filtering and Hadamard products, use the `zsharp_solve` tactic. It automates:
1. Unfolding of core filtering definitions (`filteredGradient`, `zScoreMask`).
2. Simplification of `WithLp` and `EuclideanSpace` projections.
3. Case splitting on `if-then-else` blocks (common in filtering logic).
4. Terminal calls to `linarith`, `positivity`, and `aesop`.

## Project Structure
- `LeanSharp/Core`: Foundations (Landscape, Models, Stats).
- `LeanSharp/Theory`: Mathematical proofs (Robustness, Dynamics).
- `LeanSharp/Layers`: Specific neural network components (Linear, ReLU).
- `LeanSharp/Tactic`: Custom proof automation.
- `Tests/`: Structural and functional verification.
