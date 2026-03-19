/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Stochastic.Mechanics.DescentSteps.Core
import LeanSharp.Stochastic.Mechanics.DescentSteps.ZScore

/-!
# Descent Steps Aggregator

This module exists to combine baseline and Z-score-filtered one-step descent
lemmas so mechanics proofs can import a single descent namespace.
-/
