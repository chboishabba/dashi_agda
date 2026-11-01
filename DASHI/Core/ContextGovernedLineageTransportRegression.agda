module DASHI.Core.ContextGovernedLineageTransportRegression where

------------------------------------------------------------------------
-- FINITE REGRESSION: SAFE RECONTEXTUALISATION != LINEAGE PRESERVATION.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.GovernedObservationProvenanceExact as Provenance
import DASHI.Core.ContextIndexedGovernedObservationExact as Governed
import DASHI.Core.ContextGovernedLineageTransportExact as Lineage

------------------------------------------------------------------------
-- A three-stage specimen:
--
--   source -> recharted -> downstream
--
-- keeps the value coordinate inherited throughout, erases inherited provenance
-- at the rechart, then adds a downstream provenance coordinate.  The final
-- provenance is therefore introduced, not restored.
------------------------------------------------------------------------

data Context : Set where sourceContext rechartedContext downstreamContext : Context
data Coordinate : Set where valueCoordinate provenanceCoordinate : Coordinate

data State : Set where leftState rightState : State
data Surface : Set where sameSurface : Surface
data Query : Set where readQuery : Query
data Axis : Set where valueAxis : Axis
data ValueOutcome : Set where sameValue : ValueOutcome

lineageAt : Context → Coordinate → Provenance.CoordinateLineage
lineageAt sourceContext valueCoordinate = Provenance.inheritedCoordinate
lineageAt sourceContext provenanceCoordinate = Provenance.inheritedCoordinate
lineageAt rechartedContext valueCoordinate = Provenance.inheritedCoordinate
lineageAt rechartedContext provenanceCoordinate = Provenance.absentCoordinate
lineageAt downstreamContext valueCoordinate = Provenance.inheritedCoordinate
lineageAt downstreamContext provenanceCoordinate = Provenance.introducedCoordinate

lineageFamily : Lineage.ContextCoordinateLineage Context Coordinate
lineageFamily = Lineage.context-coordinate-lineage lineageAt

firstEffect : Coordinate → Provenance.CoordinateEffect
firstEffect valueCoordinate = Provenance.preservesCoordinate
firstEffect provenanceCoordinate = Provenance.erasesCoordinate

secondEffect : Coordinate → Provenance.CoordinateEffect
secondEffect valueCoordinate = Provenance.preservesCoordinate
secondEffect provenanceCoordinate = Provenance.addsCoordinate

firstReceipt :
  Lineage.LineageTransportReceipt lineageFamily sourceContext rechartedContext
firstReceipt =
  Lineage.lineage-transport-receipt firstEffect
    (λ { valueCoordinate → refl
       ; provenanceCoordinate → refl })

secondReceipt :
  Lineage.LineageTransportReceipt lineageFamily rechartedContext downstreamContext
secondReceipt =
  Lineage.lineage-transport-receipt secondEffect
    (λ { valueCoordinate → refl
       ; provenanceCoordinate → refl })

valueLineagePreservedThroughFirstRechart :
  lineageAt rechartedContext valueCoordinate
  ≡ lineageAt sourceContext valueCoordinate
valueLineagePreservedThroughFirstRechart =
  Lineage.preservedCoordinateRetainsLineage
    firstReceipt valueCoordinate refl

provenanceErasedAtRechart :
  lineageAt rechartedContext provenanceCoordinate
  ≡ Provenance.absentCoordinate
provenanceErasedAtRechart =
  Lineage.erasedInheritedCoordinateBecomesAbsent
    firstReceipt provenanceCoordinate refl refl

downstreamProvenanceIsIntroduced :
  lineageAt downstreamContext provenanceCoordinate
  ≡ Provenance.introducedCoordinate
downstreamProvenanceIsIntroduced =
  Lineage.eraseThenAddAcrossContextsIsIntroduced
    firstReceipt secondReceipt provenanceCoordinate refl refl refl

downstreamProvenanceIsNotRestoredInherited :
  lineageAt downstreamContext provenanceCoordinate
  ≡ Provenance.inheritedCoordinate → ⊥
downstreamProvenanceIsNotRestoredInherited =
  Lineage.eraseThenAddAcrossContextsDoesNotRestoreInherited
    firstReceipt secondReceipt provenanceCoordinate refl refl refl

------------------------------------------------------------------------
-- The same three contexts can nevertheless be safe for a declared consumer
-- that only requires the preserved value axis.  This is the exact separation:
-- consumer safety does not manufacture lineage identity on inactive axes.
------------------------------------------------------------------------

observe : State → Surface
observe leftState = sameSurface
observe rightState = sameSurface

Outcome : Axis → Set
Outcome valueAxis = ValueOutcome

Active : Context → Query → Axis → Set
Active sourceContext readQuery valueAxis = ⊤
Active rechartedContext readQuery valueAxis = ⊤
Active downstreamContext readQuery valueAxis = ⊤

consume : (axis : Axis) → State → Outcome axis
consume valueAxis leftState = sameValue
consume valueAxis rightState = sameValue

governedFamily :
  Governed.ContextIndexedGovernedFamily State Context Query Surface observe
governedFamily =
  Governed.context-indexed-governed-family Axis Outcome Active consume

safeEverywhere :
  (context : Context) →
  Governed.GovernedSafeFor governedFamily context readQuery
safeEverywhere context valueAxis tt left right same = refl

record SafeRecontextualisationChangedLineage : Set₁ where
  constructor safe-recontextualisation-changed-lineage
  field
    sourceSafe : Governed.GovernedSafeFor governedFamily sourceContext readQuery
    downstreamSafe : Governed.GovernedSafeFor governedFamily downstreamContext readQuery
    finalProvenanceIntroduced :
      lineageAt downstreamContext provenanceCoordinate
      ≡ Provenance.introducedCoordinate
    finalProvenanceNotInherited :
      lineageAt downstreamContext provenanceCoordinate
      ≡ Provenance.inheritedCoordinate → ⊥

safeRecontextualisationNeedNotPreserveLineage :
  SafeRecontextualisationChangedLineage
safeRecontextualisationNeedNotPreserveLineage =
  safe-recontextualisation-changed-lineage
    (safeEverywhere sourceContext)
    (safeEverywhere downstreamContext)
    downstreamProvenanceIsIntroduced
    downstreamProvenanceIsNotRestoredInherited

record ContextGovernedLineageTransportRegressionBoundary : Set where
  field
    sameConsumerCanRemainSafeAcrossRechart : Bool
    safeRechartMustPreserveInactiveProvenanceLineage : Bool
    erasedThenAddedProvenanceIsNewLineage : Bool
    downstreamNewProvenanceCountsAsRestoredInheritedProvenance : Bool

canonicalContextGovernedLineageTransportRegressionBoundary :
  ContextGovernedLineageTransportRegressionBoundary
canonicalContextGovernedLineageTransportRegressionBoundary = record
  { sameConsumerCanRemainSafeAcrossRechart = true
  ; safeRechartMustPreserveInactiveProvenanceLineage = false
  ; erasedThenAddedProvenanceIsNewLineage = true
  ; downstreamNewProvenanceCountsAsRestoredInheritedProvenance = false
  }
