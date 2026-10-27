module DASHI.EverythingTOESymmetryResolved369 where

------------------------------------------------------------------------
-- Focused TOE aggregate: generic symmetry-resolved fibre calculus plus the
-- existing SSP/369 representation-reduction and physics instances.
------------------------------------------------------------------------

import DASHI.Core.SymmetryResolvedFibreExact
import DASHI.EverythingSSPRepresentationReductionRound9
import DASHI.Physics.Closure.TOESymmetryResolved369BridgeExact

-- Reuse graphene fibre obstruction and source-bounded physical non-promotion.
import DASHI.Unified.GraphenePhysicalNonPromotionTOEExact
import DASHI.Unified.GraphenePhysicalNonPromotionTOEValidation

-- Direct TOE consumers of existing non-promotion proofs.
-- These proofs remain owned by the graphene/physical validation modules.
import DASHI.Unified.GraphenePhysicalNonPromotionTOEExact as GraphenePhysicalTOE

toeSyntheticQTMIsNotMeasured :
  GraphenePhysicalTOE.syntheticQTMCountsAsMeasuredFit ≡ false
toeSyntheticQTMIsNotMeasured =
  GraphenePhysicalTOE.syntheticQTMRemainsNonPromoting

toeSyntheticEntropyIsNotMeasured :
  GraphenePhysicalTOE.syntheticMaxwellCountsAsMeasuredEntropy ≡ false
toeSyntheticEntropyIsNotMeasured =
  GraphenePhysicalTOE.syntheticMaxwellRemainsNonPromoting

toePositiveEulerianIsNotFullWEC :
  GraphenePhysicalTOE.positiveEulerianCountsAsFullWEC ≡ false
toePositiveEulerianIsNotFullWEC =
  GraphenePhysicalTOE.positiveEulerianRemainsNonPromoting
