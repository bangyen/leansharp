/-
Copyright (c) 2026 Bangyen Pham. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bangyen Pham
-/

import LeanSharp.Core.Filters
import LeanSharp.Core.Landscape
import LeanSharp.Core.Models
import LeanSharp.Core.Objective
import LeanSharp.Core.Stats
import LeanSharp.Core.Taylor

/-!
# Core Aggregator

This module exists to expose all foundational `LeanSharp.Core` modules behind a
single import, so downstream theory and stochastic files can depend on one
stable entrypoint.
-/
