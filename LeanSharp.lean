/-
Copyright (c) 2024 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/
import LeanSharp.Core.Filters
import LeanSharp.Core.Landscape
import LeanSharp.Core.Models
import LeanSharp.Core.Sam
import LeanSharp.Core.Taylor

import LeanSharp.Examples.ToyApplication

import LeanSharp.Stochastic.StochasticConvergence
import LeanSharp.Stochastic.StochasticGeneralization
import LeanSharp.Stochastic.StochasticSam

import LeanSharp.Tactic.ZSolve

import LeanSharp.Theory.Convergence
import LeanSharp.Theory.FilterAlgebra
import LeanSharp.Theory.Generalization
import LeanSharp.Theory.HessianContraction
import LeanSharp.Theory.ModelTheorems
import LeanSharp.Theory.Rates
import LeanSharp.Theory.SamBound

/-!
# LeanSharp

This is the main entry point for the `LeanSharp` mathematical formalization
of Sharpness-Aware Minimization with Z-Score Gradient Filtering.

Everything defined so far is fully compiled and type-checked by Lean 4's kernel!
-/
