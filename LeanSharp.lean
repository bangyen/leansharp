/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters
import LeanSharp.Core.Landscape
import LeanSharp.Core.Models
import LeanSharp.Core.Sam
import LeanSharp.Core.Stats
import LeanSharp.Core.Taylor

import LeanSharp.Examples.IllConditioned
import LeanSharp.Examples.MLP
import LeanSharp.Examples.QuadraticBowl
import LeanSharp.Examples.Rosenbrock

import LeanSharp.Layers.Activation
import LeanSharp.Layers.Convolution
import LeanSharp.Layers.Linear
import LeanSharp.Layers.Normalization

import LeanSharp.Stochastic.Convergence
import LeanSharp.Stochastic.Generalization
import LeanSharp.Stochastic.Rates
import LeanSharp.Stochastic.Sam

import LeanSharp.Tactic.ZSolve

import LeanSharp.Theory.ChainStability
import LeanSharp.Theory.Convergence
import LeanSharp.Theory.FilterAlgebra
import LeanSharp.Theory.Generalization
import LeanSharp.Theory.HessianContraction
import LeanSharp.Theory.SamBound
import LeanSharp.Theory.Schedulers

/-!
# LeanSharp

This is the main entry point for the `LeanSharp` mathematical formalization
of Sharpness-Aware Minimization with Z-Score Gradient Filtering.

Everything defined so far is fully compiled and type-checked by Lean 4's kernel!
-/
