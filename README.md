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
- ✅ L₂ Norm contraction and component bounds for the Z-score filter (`Theorems.lean`).

## Roadmap for Formalization

Our formalization targets move from foundational linear algebra to complex optimization theory.

### Phase 4: ZSharp Convergence Bound (Completed)
- [x] **Decomposition**: Decomposed the convergence proof into modular lemmas (`inner_g_adv_bound`, `inner_filter_error`).
- [x] **Alignment Lemma**: Established the formal `alignment_condition` required for the filtered gradient's inner product bound.
- [x] **Convergence Theorem**: Formally proved geometric convergence under the alignment and flat-minimum assumptions.

### Phase 5: Stochastic Z-Score Convergence (Future)
- [ ] **Minibatch Noise Analysis**: Analyze the interaction between Z-score filtering and stochastic noise $\xi_t$.
- [ ] **SVRG-like Bounds**: Prove 1/T convergence rates for the stochastic variant under standard variance assumptions.

### Phase 6: Extension to Non-convexity
- [ ] **L-smooth relaxations**: Relax strong convexity to general L-smoothness and prove convergence to stationary points.
- [ ] **Hessian Sharpness**: Formally link Z-score filtering to the eigenvalues of the Hessian $\nabla^2 L(w)$.

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
