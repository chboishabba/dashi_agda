module DASHI.Physics.SchurNSYMProductiveJoin where

import DASHI.Analysis.BlockSchurStructure
import DASHI.Analysis.BlockSchurCoercivity
import DASHI.Physics.YangMills.BalabanSchurGenericInstance
import DASHI.Physics.Closure.NSShellSchurInstance
import DASHI.Physics.Closure.NSCrossShellSchurBound

------------------------------------------------------------------------
-- Shared mathematical join:
--
--   exact finite YM block Schur structure
--                ↓
--   domain-neutral quantitative coercivity theorem
--                ↓
--   conditional NS shell frame-gap theorem
--
-- The remaining NS obligation is now exactly the independently typed
-- cross-shell correction estimate plus its budget separation from the
-- diagonal high-shell gap.
------------------------------------------------------------------------
