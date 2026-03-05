# LeanSharp 🛡️

**Formal Verification of Sharpness-Aware Minimization with Z-Score Gradient Filtering in Lean 4.**

[![Lean 4 Version](https://img.shields.io/badge/Lean-4.28.0-blue.svg)](https://leanprover.github.io/)
[![Mathlib4](https://img.shields.io/badge/Mathlib-4-brightgreen.svg)](https://github.com/leanprover-community/mathlib4)

LeanSharp is the formal, mathematical sister-project to [ZSharp](https://github.com/bangyen/zsharp). While ZSharp provides an empirical PyTorch implementation of Z-Score filtered SAM (achieving +5.26% accuracy over SGD), this repository constructs a completely rigorous foundation for the algorithm using the [Lean 4](https://leanprover.github.io/) interactive theorem prover.

## Motivation

Machine Learning optimization algorithms are notoriously difficult to analyze theoretically. Proofs of convergence for Deep Learning optimizers often rely on informal heuristics or hidden assumptions about the loss landscape.

By formally verifying Z-Score SAM in Lean 4, every mathematical step—from the Fréchet derivative of the loss function to the final contraction properties of the gradient filter—is rigorously checked by a verified kernel. **Critically, every theorem is formally proved with zero `axiom` declarations in the source; all mathematical claims are derived directly from Mathlib.**

## Verification Status

All theorems in LeanSharp are formally verified with **zero axioms** and **zero sorry placeholders**.

- ✅ **Core Foundations** (`Core/`): Hessian symmetry, L-smoothness, and Z-score hadamard filtering.
- ✅ **Theory & Convergence** (`Theory/`): Geometric convergence for ZSharp, generalization bounds (PAC-Bayes), and Z-score uniform stability.
- ✅ **Curvature & Sharpness** (`Theory/`): Spectral bounds relating maximum Hessian eigenvalues to Z-score gradient contraction.
- ✅ **Stochastic Stability** (`Stochastic/`): Probabilistic convergence and variance contraction bounds.
- ✅ **Mathematical Purity**: Verified by CI to have no axioms and no linter warnings.
- ✅ **Toy Application** (`Examples/`): Computable verification on 2D quadratic landscapes.

## Roadmap & Future Work

While the core theory is now verified, the following research directions are planned:
- **ZSharp Universality**: Formally prove that the empirical distribution of Z-scores converges to the standard Gaussian as $d \to \infty$.
- **Explicit Convergence Rates**: Formalize specific $O(1/T)$ or $O(1/\sqrt{T})$ rates for specific classes of functions (e.g., PŁ functions).
- **Deep Models**: Extend formalization to structured multi-layer neural network architectures and backpropagation.
- **Heavy-Tailed Noise**: Rigorously prove ZSharp's superiority over standard SGD under non-Gaussian (e.g., Cauchy) noise.
- **Third-Order Analysis**: Define third-derivative tensors to analyze Z-score filtering against higher-order geometry.
- **Sobolev Space Foundations**: Transition to Sobolev spaces for advanced regularity and functional analysis.
- **Automated Tactics**: Develop a `zsharp_solve` tactic using `aesop` or `linarith` extensions to automate filter contraction bounds.

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
