# LeanSharp 🛡️

**Formal Verification of Sharpness-Aware Minimization with Z-Score Gradient Filtering in Lean 4.**

[![Lean 4 Version](https://img.shields.io/badge/Lean-4.28.0-blue.svg)](https://leanprover.github.io/)
[![Mathlib4](https://img.shields.io/badge/Mathlib-4-brightgreen.svg)](https://github.com/leanprover-community/mathlib4)

LeanSharp is the formal, mathematical sister-project to [ZSharp](https://github.com/bangyen/zsharp). While ZSharp provides an empirical PyTorch implementation of Z-Score filtered SAM (achieving +5.26% accuracy over SGD), this repository aims to construct a completely rigorous foundation for the algorithm using the [Lean 4](https://leanprover.github.io/) interactive theorem prover.

## Motivation
Machine Learning optimization algorithms are notoriously difficult to analyze theoretically. Proofs of convergence for Deep Learning optimizers often rely on informal heuristics or hidden assumptions about the loss landscape.

By formally verifying Z-Score SAM in Lean 4, we ensure that every mathematical step—from the Fréchet derivative of the loss function to the final contraction properties of the gradient filter—is rigorously checked by a verified kernel.

## Current State of Verification
The foundational scaffolding is complete and compiles successfully:
- ✅ Formal definition of $\mathbb{R}^d$ parameter spaces (`Landscape.lean`).
- ✅ Formal definition of the standard SAM max-perturbation objective (`Sam.lean`).
- ✅ Formal definition of statistical Z-Score Gradient Filtering tensors (`Filters.lean`).
- ✅ Basic Boolean property proofs of the z-score mask (`LeanSharp.lean`).

## Roadmap for Formalization

Our formalization targets move from foundational linear algebra to complex optimization theory.

### Phase 1: Property Proofs of the Filter (Current)
- [ ] **Norm Contraction**: Prove that the filtered gradient norm is strictly bounded by the original gradient norm: $\forall g, z, \| \text{filtered\_gradient}(g, z) \|_2 \le \|g\|_2$.
- [ ] **Mean/Variance Invariance**: Analyze the preservation of gradient directionality under filtering.

### Phase 2: Stochastics and Empirical Risk
- [ ] **Minibatch Definitions**: Formalize a dataset $S$ and define the empirical risk $L_S(w)$.
- [ ] **Stochastic Gradient SAM**: Differentiate between the true gradient $\nabla L_\mathcal{D}(w)$ and the batch gradient $\nabla L_\mathcal{S}(w)$.

### Phase 3: The SAM Generalization Bound
- [ ] **Foret et al. Bound**: Formalize the pacing constraint: $L_\mathcal{D}(w) \le \max_{\|\epsilon\| \le \rho} L_\mathcal{S}(w + \epsilon) + h(\|w\|^2 / \rho^2)$. This is the massive core theorem of Sharpness-Aware Minimization.

### Phase 4: ZSharp Convergence (Research Goal)
- [ ] **Convergence Rate**: Prove a convergence bound for `zsharp_sam_update` assuming $\mu$-strong convexity and $L$-smoothness.

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
