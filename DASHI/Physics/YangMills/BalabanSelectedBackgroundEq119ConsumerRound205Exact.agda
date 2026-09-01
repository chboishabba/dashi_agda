module DASHI.Physics.YangMills.BalabanSelectedBackgroundEq119ConsumerRound205Exact where

------------------------------------------------------------------------
-- ROUND 205
--
-- Forward BIDI source-side compression.
--
-- The selected-background variational/chart bridge already proves principal
-- chart admission for every selected bond.  Therefore any Eq.(119)-style
-- consumer that only requires principal-log admissibility can consume that
-- theorem directly; it does not need a second small-field witness.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationalChartBridgeExact as Bridge
import DASHI.Physics.YangMills.BalabanClayGate4SU2PrincipalLogBallExact as Log
import DASHI.Physics.YangMills.BalabanClayGate4BackgroundFieldVariationalTheoremExact as Variational

record Eq119PrincipalLogConsumer
    (CoarseField FineField Bond Lie Group Bound Output : Set) : Set₁ where
  field
    consume :
      (bridge : Bridge.SelectedBackgroundVariationalChartBridge
        CoarseField FineField Bond Lie Group Bound) →
      (coarse : CoarseField) →
      (small : Variational.CoarseSmallField
        (Bridge.variational bridge) coarse) →
      (bond : Bond) →
      Log.InPrincipalImage (Bridge.principalChart bridge)
        (Bridge.selectedBondGroup bridge coarse small bond) →
      Output

open Eq119PrincipalLogConsumer public

consumeSelectedBackgroundDirectly :
  ∀ {CoarseField FineField Bond Lie Group Bound Output}
    (consumer : Eq119PrincipalLogConsumer
      CoarseField FineField Bond Lie Group Bound Output)
    (bridge : Bridge.SelectedBackgroundVariationalChartBridge
      CoarseField FineField Bond Lie Group Bound)
    (coarse : CoarseField)
    (small : Variational.CoarseSmallField
      (Bridge.variational bridge) coarse)
    (bond : Bond) →
  Output
consumeSelectedBackgroundDirectly consumer bridge coarse small bond =
  consume consumer bridge coarse small bond
    (Bridge.selectedBackgroundBondPrincipalAdmissible
      bridge coarse small bond)
