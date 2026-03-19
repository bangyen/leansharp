/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Layers.Basic.Activation
import LeanSharp.Layers.Basic.Dropout
import LeanSharp.Layers.Basic.Linear
import LeanSharp.Layers.Basic.Residual

/-!
# Basic Layers Aggregator

This module exists to collect elemental feedforward layer definitions under one
import, reducing import churn in files that reason about standard blocks.
-/
