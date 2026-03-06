# LeanSharp 🛡️

**Formal Verification of Sharpness-Aware Minimization with Z-Score Gradient Filtering in Lean 4.**

[![Lean 4 Version](https://img.shields.io/badge/Lean-4.28.0-blue.svg)](https://leanprover.github.io/)
[![Mathlib4](https://img.shields.io/badge/Mathlib-4-brightgreen.svg)](https://github.com/leanprover-community/mathlib4)

LeanSharp is the formal, mathematical sister-project to [ZSharp](https://github.com/bangyen/zsharp). While ZSharp provides an empirical PyTorch implementation of Z-Score filtered SAM (achieving +5.26% accuracy over SGD), this repository constructs a completely rigorous foundation for the algorithm using the [Lean 4](https://leanprover.github.io/) interactive theorem prover.

## Motivation

Machine Learning optimization algorithms are notoriously difficult to analyze theoretically. Proofs of convergence for Deep Learning optimizers often rely on informal heuristics or hidden assumptions about the loss landscape.

By formally verifying Z-Score SAM in Lean 4, every mathematical step—from the Fréchet derivative of the loss function to the final contraction properties of the gradient filter—is rigorously checked by a verified kernel. **Critically, every theorem is formally proved with zero `axiom` declarations in the source; all mathematical claims are derived directly from Mathlib.**

## Verification Status

All mathematical claims in LeanSharp are formally verified with **zero axioms** and **zero sorry placeholders**.

- ✅ **Optimizers & Curvature** (`Core/`): Hessian symmetry, L-smoothness, Z-score Hadamard filtering, and Taylor descent lemma.
- ✅ **Stability & Robustness** (`Theory/`): Geometric convergence, explicit $O(1/T)$ rates, and **Outlier Signal Preservation** (formal proof that Z-scores extract sparse signals).
- ✅ **Stochastic Convergence** (`Stochastic/`): Expected squared distance bounds and variance contraction under filtered stochastic gradients.
- ✅ **Tactic Support** (`Tactic/`): Custom `zsharp_solve` tactic for automated Z-score algebraic proofs.

## Roadmap & Future Work

### Research Moonshots (Mathlib Under Construction)
The following directions are "Grand Challenges" currently limited by foundational gaps in Mathlib:
- **ZSharp Universality**: Proving high-dimensional Gaussian convergence for Z-scores (requires Berry-Esseen / Stein's method foundations).
- **Heavy-Tailed Noise**: Formalizing non-Gaussian probability oracles (e.g., Cauchy) is currently limited by the complexity of advanced measure theory in Lean.
- **Sobolev Foundations**: Transitioning to Lebesgue spaces with AE-equivalence classes.
- **Third-Order Descent**: Multivariate Taylor remainder theory for multilinear maps (requires ongoing MUC calculus refactor).

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
