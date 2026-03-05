# LeanSharp 🛡️

**Formal Verification of Sharpness-Aware Minimization with Z-Score Gradient Filtering in Lean 4.**

[![Lean 4 Version](https://img.shields.io/badge/Lean-4.28.0-blue.svg)](https://leanprover.github.io/)
[![Mathlib4](https://img.shields.io/badge/Mathlib-4-brightgreen.svg)](https://github.com/leanprover-community/mathlib4)

LeanSharp is the formal, mathematical sister-project to [ZSharp](https://github.com/bangyen/zsharp). While ZSharp provides an empirical PyTorch implementation of Z-Score filtered SAM (achieving +5.26% accuracy over SGD), this repository aims to construct a completely rigorous foundation for the algorithm using the [Lean 4](https://leanprover.github.io/) interactive theorem prover.

## Motivation
Machine Learning optimization algorithms are notoriously difficult to analyze theoretically. Proofs of convergence for Deep Learning optimizers often rely on informal heuristics or hidden assumptions about the loss landscape.

By formally verifying Z-Score SAM in Lean 4, we ensure that every mathematical step—from the Fréchet derivative of the loss function to the final contraction properties of the gradient filter—is rigorously checked by a verified kernel.

## Verification Status

The Z-Score SAM formalization is divided into four logical layers, from foundational linear algebra to advanced generalization theory.

### 1. Mathematical Foundations (`Landscape.lean`, `Filters.lean`)
- ✅ **Parameter Space**: Formal definition of $\mathbb{R}^d$ and Euclidean norm properties.
- ✅ **Z-Score Filter**: Statistical mean and variance operators for gradient tensors.
- ✅ **L₂ Contraction**: Proved that the Z-score filter is a non-expansive mapping in the parameter space.

### 2. Deterministic Optimization (`Sam.lean`, `Theorems.lean`, `Convergence.lean`)
- ✅ **SAM Objective**: Formalized the $L_\infty$-perturbation and dual-norm derivation.
- ✅ **Alignment Condition**: Proved the geometric alignment required for filtered gradient updates.
- ✅ **Convergence**: Geometric convergence theorem for deterministic Z-score SAM under flat-minimum assumptions.

### 3. Stochastic & Non-Convex Analysis (`Stochastics.lean`, `StochasticSam.lean`, `NonConvex.lean`)
- ✅ **Noise Modeling**: Bounded variance and unbiasedness foundations for minibatch gradients.
- ✅ **Stochastic Convergence**: Initial scaffolding for the Robbins-Monro style convergence proof.
- ✅ **Curvature Linkage**: Formalized the link between the Hessian spectrum and stationary point optimization.

### 4. Generalization & Sharpness (`Generalization.lean`)
- ✅ **Sharpness (λ_max)**: Sharpness defined via the maximum eigenvalue of the Hessian matrix.
- ✅ **PAC-Bayes Bound**: Formal link between population risk, empirical risk, and flatness.
- ✅ **Uniform Stability**: Stability bounds for the Z-score filtered update rule.

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
