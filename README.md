# LeanSharp 🛡️

**Formal Verification of Sharpness-Aware Minimization with Z-Score Gradient Filtering in Lean 4.**

[![Lean 4 Version](https://img.shields.io/badge/Lean-4.28.0-blue.svg)](https://leanprover.github.io/)
[![Mathlib4](https://img.shields.io/badge/Mathlib-4-brightgreen.svg)](https://github.com/leanprover-community/mathlib4)

LeanSharp is the formal, mathematical sister-project to [ZSharp](https://github.com/bangyen/zsharp). While ZSharp provides an empirical PyTorch implementation of Z-Score filtered SAM (achieving +5.26% accuracy over SGD), this repository constructs a completely rigorous foundation for the algorithm using the [Lean 4](https://leanprover.github.io/) interactive theorem prover.

## Motivation

Machine Learning optimization algorithms are notoriously difficult to analyze theoretically. Proofs of convergence for Deep Learning optimizers often rely on informal heuristics or hidden assumptions about the loss landscape.

By formally verifying Z-Score SAM in Lean 4, every mathematical step—from the Fréchet derivative of the loss function to the final contraction properties of the gradient filter—is rigorously checked by a verified kernel. **Critically, every theorem is formally proved with zero `axiom` declarations in the source; all mathematical claims are derived directly from Mathlib.**

## Verification Status

The Z-Score SAM formalization is divided into four logical layers, from foundational linear algebra to advanced generalization theory.

### 1. Mathematical Foundations (`Landscape.lean`, `Filters.lean`)
- ✅ **Parameter Space**: Formal definition of $\mathbb{R}^d$ and Euclidean norm properties.
- ✅ **Hessian Symmetry**: Proved from Mathlib's `second_derivative_symmetric` (Schwarz's Theorem) — **no axioms**.
- ✅ **Z-Score Filter**: Statistical mean, variance, and standard deviation operators for gradient tensors.

### 2. Deterministic Optimization (`Sam.lean`, `Convergence.lean`)
- ✅ **SAM Objective**: Formalized the $L_\infty$-perturbation and dual-norm derivation.
- ✅ **Alignment Condition**: Proved the geometric alignment required for filtered gradient updates, strictly bounding the filter norm against the landscape smoothness.
- ✅ **Convergence**: Geometric convergence theorem for deterministic Z-score SAM.

### 3. Stochastic Optimization (`StochasticSam.lean`, `StochasticConvergence.lean`)
- ✅ **Stochastic Gradient Model**: Formalization of empirical gradients with bounded variance.
- ✅ **Stochastic ZSharp Convergence**: Proof that the Z-score filtered gradient descent converges in expectation even under stochastic noise.

### 4. Generalization & Sharpness (`Generalization.lean`, `HessianContraction.lean`)
- ✅ **Sharpness (λ_max)**: Sharpness defined via the maximum eigenvalue of the Hessian.
- 🚧 **Hessian Contraction Bound**: Formal connection bounding the Z-score filtered gradient's curvature descent by the native Maximum Eigenvalue of the Hessian.
- ✅ **PAC-Bayes Bound**: Formal link between population risk, empirical risk, and flatness.
- ✅ **Uniform Stability**: Stability bounds for the Z-score filtered update rule.

### 5. Toy Application (`ToyApplication.lean`)
- ✅ **Explicit Computability**: Explicit evaluation matching the theoretical exact gradient of the algorithm on a simple 2D quadratic landscape.

### 6. Absolute Mathematical Purity
- ✅ **Zero `axiom` declarations**: Every theorem is formally derived. CI enforces this automatically.
- ✅ **Zero `sorry` placeholders**: All proofs are complete.
- ✅ **Zero `set_option linter` suppressions**: All linter warnings resolved at their source.

## Installation & Building

Make sure you have [elan](https://github.com/leanprover/elan) installed for Lean 4 version management.

```bash
git clone https://github.com/bangyen/leansharp.git
cd leansharp
lake exe cache get  # Downloads the pre-compiled Mathlib libraries
lake build
```

## Contributing
This repo uses standard Mathlib naming conventions. If you're a Lean 4 wizard interested in ML optimization theory, feel free to submit PRs targeting the Roadmap!
