module DASHI.Physics.Closure.CanonicalStageCSummaryBundle where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.CanonicalStageC as CSC
open import DASHI.Physics.Closure.CanonicalStageCStatus as CSS
open import DASHI.Physics.Closure.CanonicalStageCTheoremBundle as CSTB
open import DASHI.Physics.Closure.CanonicalGaugeConstraintRealizedInstances as CGCRI
open import DASHI.Physics.Closure.KnownLimitsLocalCoherenceTheorem as KLLCT
open import DASHI.Physics.Closure.KnownLimitsExtendedLocalRecoveryTheorem as KLER
open import DASHI.Physics.Closure.KnownLimitsLocalPhysicsCoherenceTheorem as KLLPC
open import DASHI.Physics.Closure.KnownLimitsRecoveredLocalRegimeTheorem as KLRLR
open import DASHI.Physics.Closure.KnownLimitsCompleteLocalRegimeTheorem as KLCLR
open import DASHI.Physics.Closure.KnownLimitsRecoveredDynamicsTheorem as KLRDT
open import DASHI.Physics.Closure.KnownLimitsRecoveredObservablesTheorem as KLROT
open import DASHI.Physics.Closure.KnownLimitsRecoveredObservableGeometryTheorem as KLROG
open import DASHI.Physics.Closure.KnownLimitsRecoveredTransportConsistencyTheorem as KLRTC
open import DASHI.Physics.Closure.KnownLimitsRecoveredWavefrontTheorem as KLRWF
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveGeometryTheorem as KLRWG
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveRegimeTheorem as KLRWR
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveObservablesTheorem as KLRWO
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveObservableTransportTheorem as KLRWOT
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveObservableTransportGeometryTheorem as KLRWOTG
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveObservableTransportGeometryCoherenceTheorem as KLRWOTGC
open import DASHI.Physics.Closure.Recovery.WaveRegime as RWR
open import DASHI.Physics.Closure.CanonicalGeometryConsumer as CGC
open import DASHI.Physics.Closure.CanonicalObservableConsumer as COC
open import DASHI.Physics.Closure.CanonicalRegimeConsumer as CRC
open import DASHI.Physics.Closure.CanonicalRecoveryTransportConsumer as CRTC
open import DASHI.Physics.Closure.CanonicalWavefrontConsumer as CWFC
open import DASHI.Physics.Closure.CanonicalWaveGeometryConsumer as CWGC
open import DASHI.Physics.Closure.CanonicalWaveRegimeConsumer as CWRC
open import DASHI.Physics.Closure.CanonicalWaveObservableConsumer as CWOC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportConsumer as CWOTC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometryConsumer as CWOTGC
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportGeometryCoherenceConsumer as CWOTGCC
open import DASHI.Physics.Closure.Consumers.WaveRegime as CWR
open import DASHI.Physics.Closure.Validation.RealizationProfileRigidity as RPR

record CanonicalStageCSummaryBundle : Setω where
  field
    closureStatus : CSS.ClosureSurfaceStatus
    theoremBundle : CSTB.CanonicalStageCTheoremBundle
    realizedGaugeInstances : CGCRI.CanonicalGaugeConstraintRealizedInstances
    localCoherence : KLLCT.KnownLimitsLocalCoherenceTheorem
    extendedLocalRecovery : KLER.KnownLimitsExtendedLocalRecoveryTheorem
    localPhysicsCoherence : KLLPC.KnownLimitsLocalPhysicsCoherenceTheorem
    recoveredLocalRegime : KLRLR.KnownLimitsRecoveredLocalRegimeTheorem
    completeLocalRegime : KLCLR.KnownLimitsCompleteLocalRegimeTheorem
    recoveredDynamics : KLRDT.KnownLimitsRecoveredDynamicsTheorem
    recoveredObservables : KLROT.KnownLimitsRecoveredObservablesTheorem
    recoveredObservableGeometry :
      KLROG.KnownLimitsRecoveredObservableGeometryTheorem
    recoveredTransportConsistency :
      KLRTC.KnownLimitsRecoveredTransportConsistencyTheorem
    recoveredWavefront :
      KLRWF.KnownLimitsRecoveredWavefrontTheorem
    recoveredWaveGeometry :
      KLRWG.KnownLimitsRecoveredWaveGeometryTheorem
    recoveredWaveRegime :
      KLRWR.KnownLimitsRecoveredWaveRegimeTheorem
    recoveredWaveObservables :
      KLRWO.KnownLimitsRecoveredWaveObservablesTheorem
    recoveredWaveObservableTransport :
      KLRWOT.KnownLimitsRecoveredWaveObservableTransportTheorem
    recoveredWaveObservableTransportGeometry :
      KLRWOTG.KnownLimitsRecoveredWaveObservableTransportGeometryTheorem
    recoveredWaveObservableTransportGeometryCoherence :
      KLRWOTGC.KnownLimitsRecoveredWaveObservableTransportGeometryCoherenceTheorem
    recoveredWaveObservableTransportGeometryRegime :
      RWR.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeTheorem
    recoveredWaveObservableTransportGeometryRegimeCoherence :
      RWR.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeCoherenceTheorem
    recoveredWaveObservableTransportGeometryRegimeStability :
      RWR.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeStabilityTheorem
    recoveredWaveObservableTransportGeometryRegimeCompleteness :
      RWR.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeCompletenessTheorem
    recoveredWaveObservableTransportGeometryRegimeSoundness :
      RWR.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeSoundnessTheorem
    recoveredWaveObservableTransportGeometryRegimeConsistency :
      RWR.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeConsistencyTheorem
    recoveredWaveObservableTransportGeometryRegimeInvariance :
      RWR.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeInvarianceTheorem
    recoveredWaveObservableTransportGeometryRegimeRobustness :
      RWR.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeRobustnessTheorem
    recoveredWaveObservableTransportGeometryRegimeResilience :
      RWR.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeResilienceTheorem
    recoveredWaveObservableTransportGeometryRegimeIntegrity :
      RWR.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeIntegrityTheorem
    geometryConsumer : CGC.GeometryConsumerFromMinimal CSC.canonicalClosure
    observableConsumer : COC.ObservableConsumerFromMinimal CSC.canonicalClosure
    regimeConsumer : CRC.RegimeConsumerFromMinimal CSC.canonicalClosure
    recoveryTransportConsumer :
      CRTC.RecoveryTransportConsumerFromMinimal CSC.canonicalClosure
    wavefrontConsumer :
      CWFC.WavefrontConsumerFromMinimal CSC.canonicalClosure
    waveGeometryConsumer :
      CWGC.WaveGeometryConsumerFromMinimal CSC.canonicalClosure
    waveRegimeConsumer :
      CWRC.WaveRegimeConsumerFromMinimal CSC.canonicalClosure
    waveObservableConsumer :
      CWOC.WaveObservableConsumerFromMinimal CSC.canonicalClosure
    waveObservableTransportConsumerSummary :
      CWOTC.WaveObservableTransportConsumerFromMinimal CSC.canonicalClosure
    waveObservableTransportGeometryConsumerSummary :
      CWOTGC.WaveObservableTransportGeometryConsumerFromMinimal CSC.canonicalClosure
    waveObservableTransportGeometryCoherenceConsumerSummary :
      CWOTGCC.WaveObservableTransportGeometryCoherenceConsumerFromMinimal
        CSC.canonicalClosure
    waveObservableTransportGeometryRegimeConsumerSummary :
      CWR.WaveObservableTransportGeometryRegimeConsumerFromMinimal
        CSC.canonicalClosure
    waveObservableTransportGeometryRegimeCoherenceConsumerSummary :
      CWR.WaveObservableTransportGeometryRegimeCoherenceConsumerFromMinimal
        CSC.canonicalClosure
    waveObservableTransportGeometryRegimeStabilityConsumerSummary :
      CWR.WaveObservableTransportGeometryRegimeStabilityConsumerFromMinimal
        CSC.canonicalClosure
    waveObservableTransportGeometryRegimeCompletenessConsumerSummary :
      CWR.WaveObservableTransportGeometryRegimeCompletenessConsumerFromMinimal
        CSC.canonicalClosure
    waveObservableTransportGeometryRegimeSoundnessConsumerSummary :
      CWR.WaveObservableTransportGeometryRegimeSoundnessConsumerFromMinimal
        CSC.canonicalClosure
    waveObservableTransportGeometryRegimeConsistencyConsumerSummary :
      CWR.WaveObservableTransportGeometryRegimeConsistencyConsumerFromMinimal
        CSC.canonicalClosure
    waveObservableTransportGeometryRegimeInvarianceConsumerSummary :
      CWR.WaveObservableTransportGeometryRegimeInvarianceConsumerFromMinimal
        CSC.canonicalClosure
    waveObservableTransportGeometryRegimeRobustnessConsumerSummary :
      CWR.WaveObservableTransportGeometryRegimeRobustnessConsumerFromMinimal
        CSC.canonicalClosure
    waveObservableTransportGeometryRegimeResilienceConsumerSummary :
      CWR.WaveObservableTransportGeometryRegimeResilienceConsumerFromMinimal
        CSC.canonicalClosure
    waveObservableTransportGeometryRegimeIntegrityConsumerSummary :
      CWR.WaveObservableTransportGeometryRegimeIntegrityConsumerFromMinimal
        CSC.canonicalClosure
    selfVerdict : RPR.RigidityVerdict
    admissibleVerdict : RPR.RigidityVerdict
    negativeControlVerdict : RPR.RigidityVerdict

canonicalStageCSummaryBundle : CanonicalStageCSummaryBundle
canonicalStageCSummaryBundle =
  record
    { closureStatus = CSC.canonicalClosureStatus
    ; theoremBundle = CSTB.canonicalStageCTheoremBundle
    ; realizedGaugeInstances = CGCRI.canonicalGaugeConstraintRealizedInstances
    ; localCoherence = KLLCT.canonicalKnownLimitsLocalCoherenceTheorem
    ; extendedLocalRecovery = CSC.canonicalKnownLimitsExtendedLocalRecoveryTheorem
    ; localPhysicsCoherence = CSC.canonicalKnownLimitsLocalPhysicsCoherenceTheorem
    ; recoveredLocalRegime = CSC.canonicalKnownLimitsRecoveredLocalRegimeTheorem
    ; completeLocalRegime = CSC.canonicalKnownLimitsCompleteLocalRegimeTheorem
    ; recoveredDynamics = CSC.canonicalKnownLimitsRecoveredDynamicsTheorem
    ; recoveredObservables = CSC.canonicalKnownLimitsRecoveredObservablesTheorem
    ; recoveredObservableGeometry =
        CSC.canonicalKnownLimitsRecoveredObservableGeometryTheorem
    ; recoveredTransportConsistency =
        CSC.canonicalKnownLimitsRecoveredTransportConsistencyTheorem
    ; recoveredWavefront =
        CSC.canonicalKnownLimitsRecoveredWavefrontTheorem
    ; recoveredWaveGeometry =
        CSC.canonicalKnownLimitsRecoveredWaveGeometryTheorem
    ; recoveredWaveRegime =
        CSC.canonicalKnownLimitsRecoveredWaveRegimeTheorem
    ; recoveredWaveObservables =
        CSC.canonicalKnownLimitsRecoveredWaveObservablesTheorem
    ; recoveredWaveObservableTransport =
        CSC.canonicalKnownLimitsRecoveredWaveObservableTransportTheorem
    ; recoveredWaveObservableTransportGeometry =
        CSC.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryTheorem
    ; recoveredWaveObservableTransportGeometryCoherence =
        CSC.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryCoherenceTheorem
    ; recoveredWaveObservableTransportGeometryRegime =
        CSC.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeTheorem
    ; recoveredWaveObservableTransportGeometryRegimeCoherence =
        CSC.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeCoherenceTheorem
    ; recoveredWaveObservableTransportGeometryRegimeStability =
        CSC.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeStabilityTheorem
    ; recoveredWaveObservableTransportGeometryRegimeCompleteness =
        CSC.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeCompletenessTheorem
    ; recoveredWaveObservableTransportGeometryRegimeSoundness =
        CSC.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeSoundnessTheorem
    ; recoveredWaveObservableTransportGeometryRegimeConsistency =
        CSC.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeConsistencyTheorem
    ; recoveredWaveObservableTransportGeometryRegimeInvariance =
        CSC.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeInvarianceTheorem
    ; recoveredWaveObservableTransportGeometryRegimeRobustness =
        CSC.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeRobustnessTheorem
    ; recoveredWaveObservableTransportGeometryRegimeResilience =
        CSC.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeResilienceTheorem
    ; recoveredWaveObservableTransportGeometryRegimeIntegrity =
        CSC.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeIntegrityTheorem
    ; geometryConsumer = CSC.canonicalGeometryConsumer
    ; observableConsumer = CSC.canonicalObservableConsumer
    ; regimeConsumer = CSC.canonicalRegimeConsumer
    ; recoveryTransportConsumer = CSC.canonicalRecoveryTransportConsumer
    ; wavefrontConsumer = CSC.canonicalWavefrontConsumer
    ; waveGeometryConsumer = CSC.canonicalWaveGeometryConsumer
    ; waveRegimeConsumer = CSC.canonicalWaveRegimeConsumer
    ; waveObservableConsumer = CSC.canonicalWaveObservableConsumer
    ; waveObservableTransportConsumerSummary =
        CSC.canonicalWaveObservableTransportConsumer
    ; waveObservableTransportGeometryConsumerSummary =
        CSC.canonicalWaveObservableTransportGeometryConsumer
    ; waveObservableTransportGeometryCoherenceConsumerSummary =
        CSC.canonicalWaveObservableTransportGeometryCoherenceConsumer
    ; waveObservableTransportGeometryRegimeConsumerSummary =
        CSC.canonicalWaveObservableTransportGeometryRegimeConsumer
    ; waveObservableTransportGeometryRegimeCoherenceConsumerSummary =
        CSC.canonicalWaveObservableTransportGeometryRegimeCoherenceConsumer
    ; waveObservableTransportGeometryRegimeStabilityConsumerSummary =
        CSC.canonicalWaveObservableTransportGeometryRegimeStabilityConsumer
    ; waveObservableTransportGeometryRegimeCompletenessConsumerSummary =
        CSC.canonicalWaveObservableTransportGeometryRegimeCompletenessConsumer
    ; waveObservableTransportGeometryRegimeSoundnessConsumerSummary =
        CSC.canonicalWaveObservableTransportGeometryRegimeSoundnessConsumer
    ; waveObservableTransportGeometryRegimeConsistencyConsumerSummary =
        CSC.canonicalWaveObservableTransportGeometryRegimeConsistencyConsumer
    ; waveObservableTransportGeometryRegimeInvarianceConsumerSummary =
        CSC.canonicalWaveObservableTransportGeometryRegimeInvarianceConsumer
    ; waveObservableTransportGeometryRegimeRobustnessConsumerSummary =
        CSC.canonicalWaveObservableTransportGeometryRegimeRobustnessConsumer
    ; waveObservableTransportGeometryRegimeResilienceConsumerSummary =
        CSC.canonicalWaveObservableTransportGeometryRegimeResilienceConsumer
    ; waveObservableTransportGeometryRegimeIntegrityConsumerSummary =
        CSC.canonicalWaveObservableTransportGeometryRegimeIntegrityConsumer
    ; selfVerdict = CSC.canonicalSelfVerdict
    ; admissibleVerdict = CSC.canonicalAdmissibleVerdict
    ; negativeControlVerdict = CSC.canonicalNegativeControlVerdict
    }
