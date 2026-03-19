/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Core.Taylor.Multilinear
import LeanSharp.Core.Taylor.SamBounds
import LeanSharp.Core.Taylor.SmoothDescent
import LeanSharp.Core.Taylor.SobolevDescent

/-!
# Taylor Aggregator

This module exists to group Taylor-expansion lemmas under one import, so proof
files can request Taylor machinery without managing per-lemma modules.
-/
