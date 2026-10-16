module DASHI.Physics.YangMills.BalabanUnifiedRecoveryC3TransportExact where

------------------------------------------------------------------------
-- C3 TRANSPORT FROM THE SOURCE-EXACT CMP109 ACTION TOWARD THE LATER BALABAN
-- RECOVERY SPINE
--
-- CMP109 now has an actual source-backed order-three spatial action and an
-- equivariant scalar consumer.  The later R132--R140 recovery compiler is
-- machine-checked, and native stress representation transport is separately
-- machine-checked, but the repository does not expose a same-object map from
-- the CMP109 generated-grid carrier into the R140 recovery carrier.  This file
-- closes the reachable CMP109 fibre and reduces the remaining promotion to one
-- explicit intertwiner socket rather than a vague "no C3" boundary.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ThreeChannelC3EquivarianceGateExact as C3
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanCMP109SpatialC3ActionExact as CMP109C3
import DASHI.Physics.Foundations.BalabanNativeSectorRecoveryTransportExact as NativeTransport
import DASHI.Physics.YangMills.BalabanUnifiedPresentCutSchwingerRecoveryRound140Exact as R140

------------------------------------------------------------------------
-- 1. Generic same-object socket for the only missing transport step.
------------------------------------------------------------------------

record R140C3IntertwinerSocket (RecoveryCarrier : Set) : Set₁ where
  constructor r140-c3-intertwiner-socket
  field
    recoveryAction : C3.OrderThreeAction RecoveryCarrier
    sourceToRecovery : Grid.GridCell4 → RecoveryCarrier
    sourceToRecoveryEquivariant :
      C3.EquivariantMap
        CMP109C3.cmp109SpatialC3Action
        recoveryAction
        sourceToRecovery

open R140C3IntertwinerSocket public

record R140C3ConsumerSocket
    {RecoveryCarrier Output : Set}
    (transport : R140C3IntertwinerSocket RecoveryCarrier) : Set₁ where
  constructor r140-c3-consumer-socket
  field
    outputAction : C3.OrderThreeAction Output
    consumer : RecoveryCarrier → Output
    consumerEquivariant :
      C3.EquivariantMap
        (recoveryAction transport)
        outputAction
        consumer

open R140C3ConsumerSocket public

socketClosesThreeChannelWeld :
  ∀ {RecoveryCarrier Output}
    (transport : R140C3IntertwinerSocket RecoveryCarrier)
    (consumerSocket : R140C3ConsumerSocket transport) →
  C3.ThreeChannelC3Weld Grid.GridCell4 RecoveryCarrier Output
socketClosesThreeChannelWeld transport consumerSocket = record
  { inputAction = CMP109C3.cmp109SpatialC3Action
  ; midAction = recoveryAction transport
  ; outputAction = outputAction consumerSocket
  ; forward = sourceToRecovery transport
  ; consumer = consumer consumerSocket
  ; forwardEquivariant = sourceToRecoveryEquivariant transport
  ; consumerEquivariant = consumerEquivariant consumerSocket
  }

------------------------------------------------------------------------
-- 2. What is already closed on the actual source fibre.
------------------------------------------------------------------------

cmp109ReachableFibreC3TransportClosed : Bool
cmp109ReachableFibreC3TransportClosed =
  CMP109C3.cmp109ThreeChannelWeldClosed

cmp109SourceActionAlreadyLiteral : Bool
cmp109SourceActionAlreadyLiteral = CMP109C3.cmp109LiteralSpatialC3Recovered

nativeStressRepresentationTransportCompilerAlreadyMachineChecked : Bool
nativeStressRepresentationTransportCompilerAlreadyMachineChecked = true

unifiedR140RecoveryCompilerAlreadyMachineChecked : Bool
unifiedR140RecoveryCompilerAlreadyMachineChecked = true

------------------------------------------------------------------------
-- 3. Exact remaining frontier.
------------------------------------------------------------------------

fullAmbientUnifiedRecoveryC3ActionRecovered : Bool
fullAmbientUnifiedRecoveryC3ActionRecovered = false

minimalSameObjectR140IntertwinerObligationExposed : Bool
minimalSameObjectR140IntertwinerObligationExposed = true

missingObjectIsAnotherC3Analogy : Bool
missingObjectIsAnotherC3Analogy = false

missingObjectIsSourceToR140SameObjectIntertwiner : Bool
missingObjectIsSourceToR140SameObjectIntertwiner = true

record BalabanUnifiedRecoveryC3Boundary : Set where
  constructor balaban-unified-recovery-c3-boundary
  field
    cmp109SourceFibreClosed : Bool
    nativeStressTransportInfrastructureReused : Bool
    r140CompilerInfrastructureReused : Bool
    fullAmbientR140ActionClaimed : Bool
    remainingGapReducedToTypedIntertwiner : Bool
    base369AnalogySubstitutesForMissingIntertwiner : Bool

canonicalBalabanUnifiedRecoveryC3Boundary : BalabanUnifiedRecoveryC3Boundary
canonicalBalabanUnifiedRecoveryC3Boundary =
  balaban-unified-recovery-c3-boundary true true true false true false
