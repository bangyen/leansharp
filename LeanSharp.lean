/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

/- Core -/
import LeanSharp.Core.Filters
import LeanSharp.Core.Landscape
import LeanSharp.Core.Models
import LeanSharp.Core.Objective
import LeanSharp.Core.Stats
import LeanSharp.Core.Taylor

/- Examples -/
import LeanSharp.Examples.IllConditioned
import LeanSharp.Examples.PerceptronNetwork
import LeanSharp.Examples.QuadraticBowl
import LeanSharp.Examples.Rosenbrock

/- Layers -/
-- Architectures
import LeanSharp.Layers.Architectures.Attention
import LeanSharp.Layers.Architectures.Transformer
import LeanSharp.Layers.Architectures.VisionTransformer

-- Basic
import LeanSharp.Layers.Basic.Activation
import LeanSharp.Layers.Basic.Dropout
import LeanSharp.Layers.Basic.Linear
import LeanSharp.Layers.Basic.Residual

-- Normalization
import LeanSharp.Layers.Normalization.BatchNorm
import LeanSharp.Layers.Normalization.LayerNorm

-- Specialized
import LeanSharp.Layers.Specialized.Convolution
import LeanSharp.Layers.Specialized.Quantization

/- Stochastic -/
import LeanSharp.Stochastic.Convergence.Process
import LeanSharp.Stochastic.Convergence.Bridges
import LeanSharp.Stochastic.Convergence.Assumptions
import LeanSharp.Stochastic.Mechanics.DescentSteps
import LeanSharp.Stochastic.Mechanics.SampleErrors
import LeanSharp.Stochastic.Foundations.Integrability
import LeanSharp.Stochastic.Foundations.Martingale
import LeanSharp.Stochastic.Foundations.Oracles
import LeanSharp.Stochastic.Foundations.Schedules
import LeanSharp.Stochastic.Foundations.RobbinsMonro
import LeanSharp.Stochastic.Mechanics.SharpnessMap

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
import LeanSharp.Theory.Structural.HardThresholding
import LeanSharp.Theory.Structural.HessianContraction
import LeanSharp.Theory.Structural.SAMDifferentiability
import LeanSharp.Theory.Structural.StabilityProperties
import LeanSharp.Theory.Structural.ViTInvariance
import LeanSharp.Stochastic.Convergence.Static

-- Robustness
import LeanSharp.Theory.Robustness.BreakdownPoint
import LeanSharp.Theory.Robustness.ComparisonResults
import LeanSharp.Theory.Robustness.FilteredMeanProps
import LeanSharp.Theory.Robustness.MedianComparison

-- Sensitivity
import LeanSharp.Theory.Structural.SobolevRegularity
import LeanSharp.Theory.Robustness.SensitivityBounds

/-!
# LeanSharp Aggregator

This root module exists to provide one import that pulls in the full LeanSharp
library, so downstream users can depend on a stable entrypoint instead of
managing per-submodule imports manually.
-/
