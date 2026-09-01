module DASHI.Physics.YangMills.BalabanTerminalBidiFrontierRound204Exact where

------------------------------------------------------------------------
-- ROUND 204
--
-- Executable cutset statement for the terminal BIDI lane.
--
-- After R200--R203, a physical positive-form producer on rooted
-- representatives automatically supplies the same-carrier GNS bridge.  Thus
-- the live mathematical work is construction of the physical state/form (and
-- subsequent completion/Hamiltonian compatibility), not another quotient.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanRootedPhysicalQuotientGNSBridgeRound200Exact as R200
import DASHI.Physics.YangMills.BalabanRootedPositiveFormPhysicalStateRound203Exact as R203

record TerminalBidiFrontier
    (Configuration Rooted Scalar : Set) : Set₁ where
  field
    physicalState : R203.RootedPhysicalState Configuration Rooted Scalar

open TerminalBidiFrontier public

sameCarrierGNS :
  ∀ {Configuration Rooted Scalar}
    (frontier : TerminalBidiFrontier Configuration Rooted Scalar) →
  R200.RootedPhysicalQuotientGNSBridge Configuration Rooted Scalar
sameCarrierGNS frontier =
  R203.physicalStateGNSBridge (physicalState frontier)
