module DASHI.Governance.SexedHistoricalStratifiedMultiConsumerClosureExact where

------------------------------------------------------------------------
-- STRATIFIED MULTI-CONSUMER CLOSURE OVER TRANSPORTED SUPPORT HISTORIES
--
-- A shared measurement is useful relative to declared downstream consumers,
-- and those consumers live at different coarse strata.  Stratum is geometric
-- indexing / coverage metadata only: it does not determine semantic meaning,
-- fine history, or closure by itself.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.DiscriminatorSynthesisExact as Discriminator
import DASHI.Core.PredictionEnvelopeExact as Envelope
import DASHI.Foundations.Base369Ternary27HypervoxelStratificationExact as Strata
import DASHI.Governance.SexedHistoricalTransportedAssociatorSupportExact as Transported
import DASHI.Governance.SexedHistoricalTransportedSupportDiscriminatorExact as SupportDisc
import DASHI.Governance.SexedHistoricalTransportedSupportConsumerClosureExact as Closure

------------------------------------------------------------------------
-- 1. Four consumers distributed over centre / face / edge / corner strata.
------------------------------------------------------------------------

data HistoricalConsumer : Set where
  reopeningPriorityConsumer
  localOptionConeConsumer
  globalCompatibilityConsumer
  futureCorridorConsumer
  : HistoricalConsumer

consumerStratum : HistoricalConsumer → Strata.VoxelStratum
consumerStratum reopeningPriorityConsumer = Strata.centreStratum
consumerStratum localOptionConeConsumer = Strata.faceCentreStratum
consumerStratum globalCompatibilityConsumer = Strata.edgeCentreStratum
consumerStratum futureCorridorConsumer = Strata.cornerStratum

data ConsumerDecision : Set where
  institutionFirst distributedFirst
  localRepairCone counterformationCone
  compatibleGlobal blockedGlobal
  reciprocityCorridor pluralCorridor
  : ConsumerDecision

consumerDecision :
  HistoricalConsumer → Transported.SupportHistoryFine → ConsumerDecision
consumerDecision reopeningPriorityConsumer Transported.repairedThenCounterformed = institutionFirst
consumerDecision reopeningPriorityConsumer Transported.counterformedThenRepaired = distributedFirst
consumerDecision localOptionConeConsumer Transported.repairedThenCounterformed = localRepairCone
consumerDecision localOptionConeConsumer Transported.counterformedThenRepaired = counterformationCone
consumerDecision globalCompatibilityConsumer Transported.repairedThenCounterformed = compatibleGlobal
consumerDecision globalCompatibilityConsumer Transported.counterformedThenRepaired = blockedGlobal
consumerDecision futureCorridorConsumer Transported.repairedThenCounterformed = reciprocityCorridor
consumerDecision futureCorridorConsumer Transported.counterformedThenRepaired = pluralCorridor

------------------------------------------------------------------------
-- 2. Coverage is explicit and distinct from closure.
------------------------------------------------------------------------

data MeasurementKind : Set where
  coarseCentreProbe
  supportOrderSharedProbe
  : MeasurementKind

data CoversStratum : MeasurementKind → Strata.VoxelStratum → Set where
  coarseCoversCentre : CoversStratum coarseCentreProbe Strata.centreStratum
  sharedCoversCentre : CoversStratum supportOrderSharedProbe Strata.centreStratum
  sharedCoversFace : CoversStratum supportOrderSharedProbe Strata.faceCentreStratum
  sharedCoversEdge : CoversStratum supportOrderSharedProbe Strata.edgeCentreStratum
  sharedCoversCorner : CoversStratum supportOrderSharedProbe Strata.cornerStratum

sharedProbeCoversConsumer :
  (c : HistoricalConsumer) → CoversStratum supportOrderSharedProbe (consumerStratum c)
sharedProbeCoversConsumer reopeningPriorityConsumer = sharedCoversCentre
sharedProbeCoversConsumer localOptionConeConsumer = sharedCoversFace
sharedProbeCoversConsumer globalCompatibilityConsumer = sharedCoversEdge
sharedProbeCoversConsumer futureCorridorConsumer = sharedCoversCorner

coarseCentreProbeDoesNotCoverEdge :
  CoversStratum coarseCentreProbe Strata.edgeCentreStratum → ⊥
coarseCentreProbeDoesNotCoverEdge ()

------------------------------------------------------------------------
-- 3. One support-order measurement closes every declared consumer in this
-- finite fixture because its outcome identifies which of the two currently
-- compatible support histories remains.  This is not a universal theorem that
-- one measurement closes arbitrary multi-consumer systems.
------------------------------------------------------------------------

supportOrderProbeClosesConsumer :
  (c : HistoricalConsumer) →
  Discriminator.ProspectivelyClosesConsumer
    Closure.CompatibleSupportHistory
    (consumerDecision c)
    SupportDisc.supportOrderProbe
supportOrderProbeClosesConsumer c
    Closure.currentCoarseSupportEvidence
    Transported.repairedThenCounterformed
    Closure.repairedHistoryCompatible
    left right leftCompatible rightCompatible
  with left | right | leftCompatible | rightCompatible
... | Transported.repairedThenCounterformed
    | Transported.repairedThenCounterformed | _ | _ = refl
... | Transported.repairedThenCounterformed
    | Transported.counterformedThenRepaired | (_ , ()) | _
... | Transported.counterformedThenRepaired
    | Transported.repairedThenCounterformed | (_ , ()) | _
... | Transported.counterformedThenRepaired
    | Transported.counterformedThenRepaired | _ | _ = refl
supportOrderProbeClosesConsumer c
    Closure.currentCoarseSupportEvidence
    Transported.counterformedThenRepaired
    Closure.counterformedHistoryCompatible
    left right leftCompatible rightCompatible
  with left | right | leftCompatible | rightCompatible
... | Transported.repairedThenCounterformed
    | Transported.repairedThenCounterformed | _ | _ = refl
... | Transported.repairedThenCounterformed
    | Transported.counterformedThenRepaired | (_ , ()) | _
... | Transported.counterformedThenRepaired
    | Transported.repairedThenCounterformed | (_ , ()) | _
... | Transported.counterformedThenRepaired
    | Transported.counterformedThenRepaired | _ | _ = refl

record StratifiedConsumerClosureReceipt (c : HistoricalConsumer) : Set₁ where
  constructor stratified-consumer-closure-receipt
  field
    stratumCovered : CoversStratum supportOrderSharedProbe (consumerStratum c)
    closesConsumer :
      Discriminator.ProspectivelyClosesConsumer
        Closure.CompatibleSupportHistory
        (consumerDecision c)
        SupportDisc.supportOrderProbe

sharedClosureReceipt :
  (c : HistoricalConsumer) → StratifiedConsumerClosureReceipt c
sharedClosureReceipt c =
  stratified-consumer-closure-receipt
    (sharedProbeCoversConsumer c)
    (supportOrderProbeClosesConsumer c)

------------------------------------------------------------------------
-- 4. Coarse evidence leaves each declared consumer unresolved.
------------------------------------------------------------------------

coarseEvidenceLeavesConsumerOpen :
  (c : HistoricalConsumer) →
  Envelope.PointIdentifiable
    Closure.CompatibleSupportHistory
    (consumerDecision c)
    Closure.currentCoarseSupportEvidence → ⊥
coarseEvidenceLeavesConsumerOpen reopeningPriorityConsumer identifiable =
  distinct (identifiable
    Transported.repairedThenCounterformed
    Transported.counterformedThenRepaired
    Closure.repairedHistoryCompatible Closure.counterformedHistoryCompatible)
  where
  distinct : institutionFirst ≡ distributedFirst → ⊥
  distinct ()
coarseEvidenceLeavesConsumerOpen localOptionConeConsumer identifiable =
  distinct (identifiable
    Transported.repairedThenCounterformed
    Transported.counterformedThenRepaired
    Closure.repairedHistoryCompatible Closure.counterformedHistoryCompatible)
  where
  distinct : localRepairCone ≡ counterformationCone → ⊥
  distinct ()
coarseEvidenceLeavesConsumerOpen globalCompatibilityConsumer identifiable =
  distinct (identifiable
    Transported.repairedThenCounterformed
    Transported.counterformedThenRepaired
    Closure.repairedHistoryCompatible Closure.counterformedHistoryCompatible)
  where
  distinct : compatibleGlobal ≡ blockedGlobal → ⊥
  distinct ()
coarseEvidenceLeavesConsumerOpen futureCorridorConsumer identifiable =
  distinct (identifiable
    Transported.repairedThenCounterformed
    Transported.counterformedThenRepaired
    Closure.repairedHistoryCompatible Closure.counterformedHistoryCompatible)
  where
  distinct : reciprocityCorridor ≡ pluralCorridor → ⊥
  distinct ()

------------------------------------------------------------------------
-- 5. Explicit shared-closure bundle: one observation closes a declared family
-- of consumers across four strata in this finite comparison.
------------------------------------------------------------------------

record SharedStratifiedClosure : Set₁ where
  constructor shared-stratified-closure
  field
    centreReceipt : StratifiedConsumerClosureReceipt reopeningPriorityConsumer
    faceReceipt : StratifiedConsumerClosureReceipt localOptionConeConsumer
    edgeReceipt : StratifiedConsumerClosureReceipt globalCompatibilityConsumer
    cornerReceipt : StratifiedConsumerClosureReceipt futureCorridorConsumer

canonicalSharedStratifiedClosure : SharedStratifiedClosure
canonicalSharedStratifiedClosure =
  shared-stratified-closure
    (sharedClosureReceipt reopeningPriorityConsumer)
    (sharedClosureReceipt localOptionConeConsumer)
    (sharedClosureReceipt globalCompatibilityConsumer)
    (sharedClosureReceipt futureCorridorConsumer)

------------------------------------------------------------------------
-- 6. No-promotion boundaries.
------------------------------------------------------------------------

data SameStratumDeterminesFineHistory : Set where

data StratumLabelDeterminesConsumerMeaning : Set where

data OneSharedProbeAlwaysClosesEveryPossibleConsumer : Set where

data CrossStratumCoverageMeansStrataCollapsed : Set where

data ConsumerClosureMeansHistoricalPrediction : Set where

data CheapestCrossStratumProbeIsBestTheory : Set where

sameStratumDoesNotDetermineFineHistory : SameStratumDeterminesFineHistory → ⊥
sameStratumDoesNotDetermineFineHistory ()

stratumLabelDoesNotDetermineConsumerMeaning : StratumLabelDeterminesConsumerMeaning → ⊥
stratumLabelDoesNotDetermineConsumerMeaning ()

sharedProbeDoesNotUniversaliseClosure :
  OneSharedProbeAlwaysClosesEveryPossibleConsumer → ⊥
sharedProbeDoesNotUniversaliseClosure ()

crossStratumCoverageDoesNotCollapseStrata : CrossStratumCoverageMeansStrataCollapsed → ⊥
crossStratumCoverageDoesNotCollapseStrata ()

consumerClosureIsNotHistoricalPrediction : ConsumerClosureMeansHistoricalPrediction → ⊥
consumerClosureIsNotHistoricalPrediction ()

cheapestProbeIsNotAutomaticallyBestTheory : CheapestCrossStratumProbeIsBestTheory → ⊥
cheapestProbeIsNotAutomaticallyBestTheory ()

record StratifiedMultiConsumerClosureBoundary : Set where
  constructor stratified-multi-consumer-closure-boundary
  field
    consumersCarryDeclaredStrata : Bool
    oneSharedProbeCanCloseSeveralDeclaredConsumers : Bool
    coarseEvidenceLeavesDeclaredConsumersOpen : Bool
    measurementCoverageIsSeparateFromSemanticMeaning : Bool
    sameStratumRecoversFineHistory : Bool
    crossStratumCoverageCollapsesStrata : Bool
    sharedClosureUniversalisesToAllConsumers : Bool
    closureCreatesPredictionAuthority : Bool

canonicalStratifiedMultiConsumerClosureBoundary : StratifiedMultiConsumerClosureBoundary
canonicalStratifiedMultiConsumerClosureBoundary =
  stratified-multi-consumer-closure-boundary
    true true true true false false false false
