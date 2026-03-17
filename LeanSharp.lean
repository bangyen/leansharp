/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

/- Core -/
import LeanSharp.Core.Filters
import LeanSharp.Core.Landscape
import LeanSharp.Core.Models
import LeanSharp.Core.Sam
import LeanSharp.Core.Stats
import LeanSharp.Core.Taylor

/- Examples -/
import LeanSharp.Examples.IllConditioned
import LeanSharp.Examples.MLP
import LeanSharp.Examples.QuadraticBowl
import LeanSharp.Examples.Rosenbrock

/- Layers -/
-- Architectures
import LeanSharp.Layers.Architectures.Attention
import LeanSharp.Layers.Architectures.Transformer
import LeanSharp.Layers.Architectures.ViT

-- Basic
import LeanSharp.Layers.Basic.Activation
import LeanSharp.Layers.Basic.Dropout
import LeanSharp.Layers.Basic.Linear
import LeanSharp.Layers.Basic.Residual

-- Normalization
import LeanSharp.Layers.Normalization.BatchNormalization
import LeanSharp.Layers.Normalization.Normalization

-- Specialized
import LeanSharp.Layers.Specialized.Convolution
import LeanSharp.Layers.Specialized.Quantization

/- Stochastic -/
import LeanSharp.Stochastic.Convergence
import LeanSharp.Stochastic.ConvergenceBridge
import LeanSharp.Stochastic.ConvergenceHypotheses
import LeanSharp.Stochastic.Descent
import LeanSharp.Stochastic.Generalization
import LeanSharp.Stochastic.Integrability
import LeanSharp.Stochastic.Rates
import LeanSharp.Stochastic.RobbinsMonro
import LeanSharp.Stochastic.Sam

/- Tactics -/
import LeanSharp.Tactic.ZSolve

/- Theory -/
-- Dynamics
import LeanSharp.Theory.Dynamics.Convergence
import LeanSharp.Theory.Dynamics.Generalization
import LeanSharp.Theory.Dynamics.SamBound
import LeanSharp.Theory.Dynamics.Schedulers

-- Structural
import LeanSharp.Theory.Structural.ChainStability
import LeanSharp.Theory.Structural.FilterAlgebra
import LeanSharp.Theory.Structural.HessianContraction
import LeanSharp.Theory.Structural.SAMDifferentiability
import LeanSharp.Theory.Structural.Stability
import LeanSharp.Theory.Structural.ViTInvariance
import LeanSharp.Stochastic.StructuralConvergence

-- Robustness
import LeanSharp.Theory.Robustness.BreakdownPoint
import LeanSharp.Theory.Robustness.ComparisonResults
import LeanSharp.Theory.Robustness.FilteredMean
import LeanSharp.Theory.Robustness.MedianComparison

-- Sensitivity
import LeanSharp.Theory.Sensitivity

/-!
# LeanSharp Aggregator

This root module exists to provide one import that pulls in the full LeanSharp
library, so downstream users can depend on a stable entrypoint instead of
managing per-submodule imports manually.
-/
