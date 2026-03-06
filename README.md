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
- ✅ **Stability & Rates** (`Theory/`): Geometric convergence, explicit $O(1/T)$ and $O(1/\sqrt{T})$ rates, and global variance contraction (validated on toy quadratic landscapes).
- ✅ **Deep Model Foundations** (`LeanSharp/Models`): Recursive layer architecture with confirmed global gradient stability for multi-layer chains.
- ✅ **Generalization Theory** (`Theory/`): PAC-Bayesian bounds and Z-score uniform stability theorems.

## Roadmap & Future Work

While the core theory is now verified, the following research directions are planned:
- **ZSharp Universality**: Formally prove that the empirical distribution of Z-scores converges to the standard Gaussian as $d \to \infty$.
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
