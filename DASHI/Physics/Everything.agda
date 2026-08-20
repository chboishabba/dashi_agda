module DASHI.Physics.Everything where

-- Physics domain spine.  Subdomains own their leaf lists; this module only
-- composes subdomain rollups so DASHI.Everything does not become a flat,
-- conflict-prone list of thousands of physics leaves.

import DASHI.Physics.Laws.Everything
import DASHI.Physics.Units.Everything
import DASHI.Physics.DarkSector.Everything
import DASHI.Physics.Unification.Everything
import DASHI.Physics.Foundations.Everything
import DASHI.Physics.StandardModel.Everything

-- Heavy Clay lanes are deliberately isolated behind their own rollups.
-- import DASHI.Physics.YangMills.Everything
-- import DASHI.Physics.Closure.Everything
