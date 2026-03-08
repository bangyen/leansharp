# LeanSharp

**Formal Verification of Sharpness-Aware Minimization with Z-Score Gradient Filtering in Lean 4.**

[![Lean 4 Version](https://img.shields.io/badge/Lean-4.28.0-blue.svg)](https://leanprover.github.io/)
[![Mathlib4](https://img.shields.io/badge/Mathlib-4-brightgreen.svg)](https://github.com/leanprover-community/mathlib4)
[![License: MIT](https://img.shields.io/badge/License-MIT-yellow.svg)](LICENSE)

LeanSharp is the formal, mathematical sister-project to [ZSharp](https://github.com/bangyen/zsharp). While ZSharp provides an empirical PyTorch implementation of Z-Score filtered SAM (achieving +5.26% accuracy over SGD), this repository constructs a completely rigorous foundation for the algorithm using the [Lean 4](https://leanprover.github.io/) interactive theorem prover.

## Motivation

Machine Learning optimization algorithms are notoriously difficult to analyze theoretically. Proofs of convergence for Deep Learning optimizers often rely on informal heuristics or hidden assumptions about the loss landscape.

By formally verifying Z-Score SAM in Lean 4, every mathematical step—from the Fréchet derivative of the loss function to the final contraction properties of the gradient filter—is rigorously checked by a verified kernel. **Critically, every theorem is formally proved with zero `axiom` declarations in the source; all mathematical claims are derived directly from Mathlib.**

## Verification Status

All mathematical claims in LeanSharp are formally verified with **zero axioms** and **zero sorry placeholders**.

- ✅ **Optimizers & Curvature** (`Core/`): Established Hessian symmetry, L-smoothness, and Z-score filtering foundations. Provides the core Taylor descent lemma for optimization proofs.
- ✅ **Stability & Robustness** (`Theory/`): Verified geometric convergence and explicit $O(1/T)$ rate bounds. Formally proved Z-score outlier signal preservation for sparse gradients.
- ✅ **Stochastic Convergence** (`Stochastic/`): Derived expected squared distance bounds and variance contraction. Validates algorithm progress under noisy, non-convex stochastic gradients.
- ✅ **Tactic Support** (`Tactic/`): Implemented the `zsharp_solve` custom tactic. Automates repetitive algebraic normalization and inequality proofs for Z-score filters.

## Roadmap & Future Work

### Immediate Roadmap
These items represent the next phase of formalization, balancing theoretical impact with Lean implementation feasibility:
- **Tensor Generalization**: Transition from `Fin d` vectors to generic `Fintype` indices. Enables support for multi-dimensional weight tensors (matrices, 3D/4D weights).
- **Deterministic Stability**: Prove Lipschitz continuity and perturbation sensitivity for the Z-score filter. Bounds result variations relative to input gradient perturbations.
- **Formal Stochastic Descent**: Formally derive the expected descent lemma from local Lipschitz smoothness. Requires integrating the second-order Taylor bound over the probability measure.
- **Tactic Hardening**: Expand `zsharp_solve` to normalize `abs` and `ge_iff_le` expressions. Reduces manual proof overhead for future inequality analysis.

### Future Directions (Mathlib Under Construction)
The following "Grand Challenges" are currently limited by foundational gaps or high combinatorial complexity in Lean 4:
- **Z-Score Universality**: Formalize the Gaussian convergence of empirical Z-score distributions. Represents a specialized project in formalizing a CLT for filtering operations.
- **Heavy-Tailed Noise**: Formalize non-Gaussian probability oracles (e.g., Cauchy noise). Limited by the measure-theoretic complexity of advanced probability in Lean.
- **Sobolev Regularity**: Transition foundations from pointwise Fréchet differentiability to $H^1/H^2$ spaces. Replaces pointwise calculus with weak derivatives and $L^2$ norms.
- **Isotropic Noise Models**: Prove statistical convergence toward "true" gradients under isotropic Gaussian noise. Faces boilerplate challenges in measure-theoretic expectation handling.
- **Median-Based Robustness**: Formalize median-based filtering as a robust alternative to Z-scores. Limited by the combinatorial and order-theoretic complexity of sorting in Lean.
- **Third-Order Descent**: Implement multivariate Taylor remainder theory for multilinear maps. Requires ongoing multilinear calculus refactors in Mathlib.

## Installation & Building

Make sure you have [elan](https://github.com/leanprover/elan) installed for Lean 4 version management.

```bash
git clone https://github.com/bangyen/leansharp.git
cd leansharp
lake exe cache get  # Downloads the pre-compiled Mathlib libraries
lake build
```

## Contributing
This repo uses standard Mathlib naming conventions. If you're a Lean 4 wizard interested in ML optimization theory, feel free to submit PRs targeting the roadmap!

## Citation

If you use this work in your research, please cite:

```bibtex
@misc{pham_leansharp_2026,
  author = {Pham, Bangyen},
  title = {LeanSharp: Formal Verification of Sharpness-Aware Minimization with Z-Score Gradient Filtering in Lean 4},
  year = {2026},
  url = {https://github.com/bangyen/leansharp}
}
