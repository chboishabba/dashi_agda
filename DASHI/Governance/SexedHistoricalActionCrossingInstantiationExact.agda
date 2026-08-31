module DASHI.Governance.SexedHistoricalActionCrossingInstantiationExact where

------------------------------------------------------------------------
-- SEXED-HISTORICAL ACTION-CROSSING INSTANTIATION
--
-- Historical carriers persist as strands; concrete transitions/interventions
-- are crossing events.  The ordered trace is retained even when endpoint and
-- crossing count collide.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Data.List using (length)

import DASHI.Core.ActionCrossingTraceCalculusExact as Trace
import DASHI.Core.IntersectionalNonFactorability as INF

------------------------------------------------------------------------
-- 1. Persistent historical strands and actions.
------------------------------------------------------------------------

data HistoricalStrand : Set where
  femininePosition masculinePosition institution network : HistoricalStrand

data HistoricalAction : Set where
  supportAction institutionaliseAction repairAction counterformationAction : HistoricalAction

supportCrossing : Trace.CrossingEvent HistoricalStrand HistoricalAction
supportCrossing =
  Trace.crossing-event femininePosition masculinePosition supportAction

institutionCrossing : Trace.CrossingEvent HistoricalStrand HistoricalAction
institutionCrossing =
  Trace.crossing-event masculinePosition institution institutionaliseAction

repairCrossing : Trace.CrossingEvent HistoricalStrand HistoricalAction
repairCrossing =
  Trace.crossing-event femininePosition institution repairAction

counterformationCrossing : Trace.CrossingEvent HistoricalStrand HistoricalAction
counterformationCrossing =
  Trace.crossing-event masculinePosition network counterformationAction

supportThenInstitution : Trace.ActionTrace HistoricalStrand HistoricalAction
supportThenInstitution =
  Trace.singleCrossing supportCrossing Trace.++trace Trace.singleCrossing institutionCrossing

institutionThenSupport : Trace.ActionTrace HistoricalStrand HistoricalAction
institutionThenSupport =
  Trace.singleCrossing institutionCrossing Trace.++trace Trace.singleCrossing supportCrossing

repairThenCounterformation : Trace.ActionTrace HistoricalStrand HistoricalAction
repairThenCounterformation =
  Trace.singleCrossing repairCrossing Trace.++trace Trace.singleCrossing counterformationCrossing

counterformationThenRepair : Trace.ActionTrace HistoricalStrand HistoricalAction
counterformationThenRepair =
  Trace.singleCrossing counterformationCrossing Trace.++trace Trace.singleCrossing repairCrossing

------------------------------------------------------------------------
-- 2. Endpoint/count collisions do not recover order provenance.
------------------------------------------------------------------------

data TraceCode : Set where
  supportInstitutionCode institutionSupportCode
  repairCounterformationCode counterformationRepairCode : TraceCode

data CoarseEndpoint : Set where
  reciprocalPresentSurface : CoarseEndpoint

data HistoricalProvenance : Set where
  supportFirst institutionFirst repairFirst counterformationFirst : HistoricalProvenance

coarseEndpoint : TraceCode → CoarseEndpoint
coarseEndpoint _ = reciprocalPresentSurface

historicalProvenance : TraceCode → HistoricalProvenance
historicalProvenance supportInstitutionCode = supportFirst
historicalProvenance institutionSupportCode = institutionFirst
historicalProvenance repairCounterformationCode = repairFirst
historicalProvenance counterformationRepairCode = counterformationFirst

supportInstitutionSameEndpoint :
  coarseEndpoint supportInstitutionCode ≡ coarseEndpoint institutionSupportCode
supportInstitutionSameEndpoint = refl

supportInstitutionDifferentProvenance :
  historicalProvenance supportInstitutionCode
  ≡ historicalProvenance institutionSupportCode → ⊥
supportInstitutionDifferentProvenance ()

endpointCannotRecoverHistoricalProvenance :
  INF.FactorsThrough coarseEndpoint historicalProvenance → ⊥
endpointCannotRecoverHistoricalProvenance =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      supportInstitutionCode institutionSupportCode refl
      supportInstitutionDifferentProvenance)

sameCrossingCountSupportInstitution :
  length supportThenInstitution ≡ length institutionThenSupport
sameCrossingCountSupportInstitution = refl

sameCrossingCountRepairCounterformation :
  length repairThenCounterformation ≡ length counterformationThenRepair
sameCrossingCountRepairCounterformation = refl

------------------------------------------------------------------------
-- 3. Boundaries.
------------------------------------------------------------------------

data SameCrossingCountMeansSameHistory : Set where

data SameEndpointAndCountMeanSameHistory : Set where

data CrossingOrderAloneEstablishesCausalAttribution : Set where

data HistoricalActionCrossingIsLiteralPhysicalCrossing : Set where

sameCrossingCountDoesNotMeanSameHistory : SameCrossingCountMeansSameHistory → ⊥
sameCrossingCountDoesNotMeanSameHistory ()

sameEndpointAndCountDoNotMeanSameHistory : SameEndpointAndCountMeanSameHistory → ⊥
sameEndpointAndCountDoNotMeanSameHistory ()

crossingOrderAloneDoesNotEstablishCausalAttribution :
  CrossingOrderAloneEstablishesCausalAttribution → ⊥
crossingOrderAloneDoesNotEstablishCausalAttribution ()

historicalCrossingIsNotLiteralPhysicalCrossing :
  HistoricalActionCrossingIsLiteralPhysicalCrossing → ⊥
historicalCrossingIsNotLiteralPhysicalCrossing ()

record SexedHistoricalActionCrossingBoundary : Set where
  constructor sexed-historical-action-crossing-boundary
  field
    historicalActionsCompiledAsCrossings : Bool
    crossingOrderRetained : Bool
    sameEndpointCanHideOrder : Bool
    sameCrossingCountCanHideOrder : Bool
    endpointAndCountDetermineHistory : Bool
    orderAloneCreatesCausalAttribution : Bool

canonicalSexedHistoricalActionCrossingBoundary : SexedHistoricalActionCrossingBoundary
canonicalSexedHistoricalActionCrossingBoundary =
  sexed-historical-action-crossing-boundary true true true true false false
