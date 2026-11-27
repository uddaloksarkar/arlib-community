/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArlibCommunity.Algorithms.HitAndRun.Analysis.QueryCount

/-! # Hit-and-Run with membership-query accounting

The lazy convex-body walk described in [Lov99] and [Vem05] is implemented using
a sealed membership oracle, capped chord bisection, and capped rejection.

* `Model/Program` defines the capped sampler and checks its program seal.
* `Model/Run` defines execution on a tape.
* `Analysis/QueryCount` proves that `execution_queryCount_le` bounds the
  recorded membership queries on every tape.

This module does not claim a mixing guarantee, a total-variation accuracy
bound, or a bound on arithmetic operations.
-/

#modelClosureOfType ArlibCommunity.Algorithms.HitAndRun.execution_queryCount_le
