module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound17Validation where

-- Validation root for the factor-of-two Duhamel audit and genuinely coupled
-- coupling/polymer RG scalar mechanics.  It extends round sixteen with exact
-- ordered-simplex integration, gK/K^2 remainder reduction on K <= eta g^2,
-- preservation of that invariant cone, and a rational counterexample showing
-- why coupling and polymer errors cannot be silently decoupled.

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound16Validation
import DASHI.Physics.YangMills.BalabanP33DuhamelOrderedSimplexMeasureExact
import DASHI.Physics.YangMills.BalabanClayCoupledPolymerFlowRemainderExact
import DASHI.Physics.YangMills.BalabanClayCoupledRGInvariantConeExact
import DASHI.Physics.YangMills.BalabanClayCouplingPolymerDecouplingCounterexampleExact
