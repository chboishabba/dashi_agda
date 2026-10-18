module DASHI.Physics.YangMills.BalabanUnifiedRecoveryC3TransportExact where

------------------------------------------------------------------------
-- C3 TRANSPORT FROM SOURCE-EXACT CMP109 INTO LATER BALABAN CONSUMERS
--
-- Historical note: an earlier cut treated a direct GridCell4 -> R140 carrier
-- map as the terminal missing object.  Later repository work already supplies
-- a stronger consumer-facing route: R144's actual finite-D1 stress readout is
-- covariant under the SAME concrete B4 generator family used by the CMP109
-- source symmetry theorem.  Restricting that action to the 1,2,3 spatial cycle
-- therefore removes the direct R140 carrier socket from the terminal roadmap.
--
-- The generic socket below remains useful if some future consumer genuinely
-- needs an ambient C3 action on an intermediate recovery carrier, but it is no
-- longer charged as the shortest physical source->stress route.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.ThreeChannelC3EquivarianceGateExact as C3
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanCMP109SpatialC3ActionExact as CMP109C3
import DASHI.Physics.Foundations.BalabanNativeSectorRecoveryTransportExact as NativeTransport
import DASHI.Physics.Foundations.BalabanR144SpatialC3StressRestrictionExact as R144C3
import DASHI.Physics.YangMills.BalabanUnifiedPresentCutSchwingerRecoveryRound140Exact as R140

------------------------------------------------------------------------
-- 1. Optional generic ambient-recovery socket.
------------------------------------------------------------------------

record R140C3IntertwinerSocket (RecoveryCarrier : Set) : Set₁ where
  constructor r140-c3-intertwiner-socket
  field
    recoveryAction : C3.OrderThreeAction RecoveryCarrier
    sourceToRecovery : Grid.GridCell4 → RecoveryCarrier
    sourceToRecoveryEquivariant :
      C3.EquivariantMap
        CMP109C3.cmp109SpatialXYZC3Action
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
  { inputAction = CMP109C3.cmp109SpatialXYZC3Action
  ; midAction = recoveryAction transport
  ; outputAction = outputAction consumerSocket
  ; forward = sourceToRecovery transport
  ; consumer = consumer consumerSocket
  ; forwardEquivariant = sourceToRecoveryEquivariant transport
  ; consumerEquivariant = consumerEquivariant consumerSocket
  }

------------------------------------------------------------------------
-- 2. What is already closed on the actual source/stress route.
------------------------------------------------------------------------

cmp109ReachableFibreC3TransportClosed : Bool
cmp109ReachableFibreC3TransportClosed =
  CMP109C3.cmp109SpatialXYZThreeChannelWeldClosed

cmp109SourceActionAlreadyLiteral : Bool
cmp109SourceActionAlreadyLiteral = CMP109C3.cmp109Spatial123C3Recovered

r144SpatialStressTensorActionAlreadyLiteral : Bool
r144SpatialStressTensorActionAlreadyLiteral =
  R144C3.r144SpatialC3TensorActionRecovered

r144UsesSameB4GeneratorFamilyAsCMP109 : Bool
r144UsesSameB4GeneratorFamilyAsCMP109 =
  R144C3.r144C3RestrictedFromExistingB4Action

nativeStressRepresentationTransportCompilerAlreadyMachineChecked : Bool
nativeStressRepresentationTransportCompilerAlreadyMachineChecked = true

unifiedR140RecoveryCompilerAlreadyMachineChecked : Bool
unifiedR140RecoveryCompilerAlreadyMachineChecked = true

------------------------------------------------------------------------
-- 3. Exact remaining frontier.
------------------------------------------------------------------------

fullAmbientUnifiedRecoveryC3ActionRecovered : Bool
fullAmbientUnifiedRecoveryC3ActionRecovered = false

ambientR140IntertwinerRequiredForCurrentStressConsumer : Bool
ambientR140IntertwinerRequiredForCurrentStressConsumer = false

terminalPhysicalPaymentIsExistingR144CovarianceWitness : Bool
terminalPhysicalPaymentIsExistingR144CovarianceWitness = true

minimalSameObjectR140IntertwinerObligationExposed : Bool
minimalSameObjectR140IntertwinerObligationExposed = true

missingObjectIsAnotherC3Analogy : Bool
missingObjectIsAnotherC3Analogy = false

record BalabanUnifiedRecoveryC3Boundary : Set where
  constructor balaban-unified-recovery-c3-boundary
  field
    cmp109SpatialSourceFibreClosed : Bool
    r144SpatialStressActionClosed : Bool
    sameB4GeneratorFamilyReused : Bool
    nativeStressTransportInfrastructureReused : Bool
    r140CompilerInfrastructureReused : Bool
    fullAmbientR140ActionClaimed : Bool
    ambientR140ActionRequiredByCurrentStressConsumer : Bool
    terminalGapIsExistingR144CovarianceWitness : Bool
    base369AnalogySubstitutesForMissingPhysicalWitness : Bool

canonicalBalabanUnifiedRecoveryC3Boundary : BalabanUnifiedRecoveryC3Boundary
canonicalBalabanUnifiedRecoveryC3Boundary =
  balaban-unified-recovery-c3-boundary
    true true true true true false false true false
