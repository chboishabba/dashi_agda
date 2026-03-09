module DASHI.Physics.Closure.CanonicalStageCTheoremBundle where

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Closure.CanonicalStageC as CSC
open import DASHI.Physics.Closure.CanonicalConstraintClosureTheorem as CCCT
open import DASHI.Physics.Closure.CanonicalGaugeConstraintBridgeTheorem as CGCBT
open import DASHI.Physics.Closure.ParametricGaugeConstraintTheorem as PGCT
open import DASHI.Physics.Closure.ParametricAlgebraicClosureTheorem as PACT
open import DASHI.Physics.Closure.ParametricAlgebraicCoherenceTheorem as PACTC
open import DASHI.Physics.Closure.ParametricAlgebraicStabilityTheorem as PACTS
open import DASHI.Physics.Closure.ParametricAlgebraicClosureBundleTheorem as PACTB
open import DASHI.Physics.Closure.ParametricAlgebraicConsistencyTheorem as PACTX
open import DASHI.Physics.Closure.ParametricAlgebraicAdmissibilityTransportTheorem as PACTAT
open import DASHI.Physics.Closure.ParametricAlgebraicPersistenceTheorem as PACTP
open import DASHI.Physics.Closure.ParametricAlgebraicGaugeSectorPersistenceTheorem as PAGSP
open import DASHI.Physics.Closure.ParametricAlgebraicTransportInvarianceTheorem as PATI
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeInvarianceTheorem as PARI
open import DASHI.Physics.Closure.ParametricAlgebraicRegimePersistenceTheorem as PARP
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportTheorem as PAWOT
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableGeometryTheorem as PAWOG
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometryCoherenceTheorem as PAWOTGC
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.Theorem as PAWOTGR
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.CoherenceTheorem as PAWOTGRC
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.StabilityTheorem as PAWOTGRS
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.CompletenessTheorem as PAWOTGRC
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.SoundnessTheorem as PAWOTGRSO
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.ConsistencyTheorem as PAWOTGRCONS
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.InvarianceTheorem as PAWOTGRINV
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.RobustnessTheorem as PAWOTGRROB
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.ResilienceTheorem as PAWOTGRRES
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportGeometry.Regime.IntegrityTheorem as PAWOTGRINT
open import DASHI.Physics.Closure.SecondaryConstraintGaugeInstance as SCGI
open import DASHI.Physics.Closure.KnownLimitsLocalRecoveryTheorem as KLRT
open import DASHI.Physics.Closure.KnownLimitsEffectiveGeometryTheorem as KLET
open import DASHI.Physics.Closure.KnownLimitsCausalPropagationTheorem as KLCPT
open import DASHI.Physics.Closure.KnownLimitsGeometryTransportTheorem as KLGT
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
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveObservableGeometryTheorem as KLRWOG
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveObservableTransportGeometryTheorem as KLRWOTG
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveObservableTransportGeometryCoherenceTheorem as KLRWOTGC
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveObservableTransportGeometry.Regime.Theorem as KLRWOTGR
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveObservableTransportGeometry.Regime.CoherenceTheorem as KLRWOTGRC
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveObservableTransportGeometry.Regime.StabilityTheorem as KLRWOTGRS
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveObservableTransportGeometry.Regime.CompletenessTheorem as KLRWOTGRC
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveObservableTransportGeometry.Regime.SoundnessTheorem as KLRWOTGRSO
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveObservableTransportGeometry.Regime.ConsistencyTheorem as KLRWOTGRCONS
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveObservableTransportGeometry.Regime.InvarianceTheorem as KLRWOTGRINV
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveObservableTransportGeometry.Regime.RobustnessTheorem as KLRWOTGRROB
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveObservableTransportGeometry.Regime.ResilienceTheorem as KLRWOTGRRES
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveObservableTransportGeometry.Regime.IntegrityTheorem as KLRWOTGRINT
open import DASHI.Physics.Closure.SpinLocalLorentzBridgeTheorem as SLLB

record CanonicalStageCTheoremBundle : Setω where
  field
    constraintTheoremSummary : CCCT.CanonicalConstraintClosureTheorem
    gaugeBridgeSummary : CGCBT.CanonicalGaugeConstraintBridgeTheorem
    canonicalParametricGaugeSummary :
      PGCT.ParametricGaugeConstraintTheorem CSC.canonicalConstraintGaugePackage
    secondaryParametricGaugeSummary :
      PGCT.ParametricGaugeConstraintTheorem SCGI.secondaryConstraintGaugePackage
    canonicalParametricAlgebraicSummary :
      PACT.ParametricAlgebraicClosureTheorem CSC.canonicalConstraintGaugePackage
    secondaryParametricAlgebraicSummary :
      PACT.ParametricAlgebraicClosureTheorem SCGI.secondaryConstraintGaugePackage
    canonicalParametricAlgebraicCoherenceSummary :
      PACTC.ParametricAlgebraicCoherenceTheorem
        CSC.canonicalConstraintGaugePackage
    secondaryParametricAlgebraicCoherenceSummary :
      PACTC.ParametricAlgebraicCoherenceTheorem
        SCGI.secondaryConstraintGaugePackage
    canonicalParametricAlgebraicStabilitySummary :
      PACTS.ParametricAlgebraicStabilityTheorem
        CSC.canonicalConstraintGaugePackage
    secondaryParametricAlgebraicStabilitySummary :
      PACTS.ParametricAlgebraicStabilityTheorem
        SCGI.secondaryConstraintGaugePackage
    canonicalParametricAlgebraicBundleSummary :
      PACTB.ParametricAlgebraicClosureBundleTheorem
        CSC.canonicalConstraintGaugePackage
    secondaryParametricAlgebraicBundleSummary :
      PACTB.ParametricAlgebraicClosureBundleTheorem
        SCGI.secondaryConstraintGaugePackage
    canonicalParametricAlgebraicConsistencySummary :
      PACTX.ParametricAlgebraicConsistencyTheorem
        CSC.canonicalConstraintGaugePackage
    secondaryParametricAlgebraicConsistencySummary :
      PACTX.ParametricAlgebraicConsistencyTheorem
        SCGI.secondaryConstraintGaugePackage
    canonicalParametricAlgebraicAdmissibilityTransportSummary :
      PACTAT.ParametricAlgebraicAdmissibilityTransportTheorem
        CSC.canonicalConstraintGaugePackage
    secondaryParametricAlgebraicAdmissibilityTransportSummary :
      PACTAT.ParametricAlgebraicAdmissibilityTransportTheorem
        SCGI.secondaryConstraintGaugePackage
    canonicalParametricAlgebraicPersistenceSummary :
      PACTP.ParametricAlgebraicPersistenceTheorem
        CSC.canonicalConstraintGaugePackage
    secondaryParametricAlgebraicPersistenceSummary :
      PACTP.ParametricAlgebraicPersistenceTheorem
        SCGI.secondaryConstraintGaugePackage
    canonicalParametricAlgebraicGaugeSectorPersistenceSummary :
      PAGSP.ParametricAlgebraicGaugeSectorPersistenceTheorem
        CSC.canonicalConstraintGaugePackage
    secondaryParametricAlgebraicGaugeSectorPersistenceSummary :
      PAGSP.ParametricAlgebraicGaugeSectorPersistenceTheorem
        SCGI.secondaryConstraintGaugePackage
    canonicalParametricAlgebraicTransportInvarianceSummary :
      PATI.ParametricAlgebraicTransportInvarianceTheorem
        CSC.canonicalConstraintGaugePackage
    secondaryParametricAlgebraicTransportInvarianceSummary :
      PATI.ParametricAlgebraicTransportInvarianceTheorem
        SCGI.secondaryConstraintGaugePackage
    canonicalParametricAlgebraicRegimeInvarianceSummary :
      PARI.ParametricAlgebraicRegimeInvarianceTheorem
        CSC.canonicalConstraintGaugePackage
    secondaryParametricAlgebraicRegimeInvarianceSummary :
      PARI.ParametricAlgebraicRegimeInvarianceTheorem
        SCGI.secondaryConstraintGaugePackage
    canonicalParametricAlgebraicRegimePersistenceSummary :
      PARP.ParametricAlgebraicRegimePersistenceTheorem
        CSC.canonicalConstraintGaugePackage
    secondaryParametricAlgebraicRegimePersistenceSummary :
      PARP.ParametricAlgebraicRegimePersistenceTheorem
        SCGI.secondaryConstraintGaugePackage
    canonicalParametricAlgebraicRegimeCoherenceSummary :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem
        CSC.canonicalConstraintGaugePackage
    secondaryParametricAlgebraicRegimeCoherenceSummary :
      PARC.ParametricAlgebraicRegimeCoherenceTheorem
        SCGI.secondaryConstraintGaugePackage
    canonicalParametricAlgebraicWaveObservableTransportSummary :
      PAWOT.ParametricAlgebraicWaveObservableTransportTheorem
        CSC.canonicalConstraintGaugePackage
    secondaryParametricAlgebraicWaveObservableTransportSummary :
      PAWOT.ParametricAlgebraicWaveObservableTransportTheorem
        SCGI.secondaryConstraintGaugePackage
    canonicalParametricAlgebraicWaveObservableGeometrySummary :
      PAWOG.ParametricAlgebraicWaveObservableGeometryTheorem
        CSC.canonicalConstraintGaugePackage
    secondaryParametricAlgebraicWaveObservableGeometrySummary :
      PAWOG.ParametricAlgebraicWaveObservableGeometryTheorem
        SCGI.secondaryConstraintGaugePackage
    canonicalParametricAlgebraicWaveObservableTransportGeometryCoherenceSummary :
      PAWOTGC.ParametricAlgebraicWaveObservableTransportGeometryCoherenceTheorem
        CSC.canonicalConstraintGaugePackage
    secondaryParametricAlgebraicWaveObservableTransportGeometryCoherenceSummary :
      PAWOTGC.ParametricAlgebraicWaveObservableTransportGeometryCoherenceTheorem
        SCGI.secondaryConstraintGaugePackage
    canonicalParametricAlgebraicWaveObservableTransportGeometryRegimeSummary :
      PAWOTGR.ParametricAlgebraicWaveObservableTransportGeometryRegimeTheorem
        CSC.canonicalConstraintGaugePackage
    secondaryParametricAlgebraicWaveObservableTransportGeometryRegimeSummary :
      PAWOTGR.ParametricAlgebraicWaveObservableTransportGeometryRegimeTheorem
        SCGI.secondaryConstraintGaugePackage
    canonicalParametricAlgebraicWaveObservableTransportGeometryRegimeCoherenceSummary :
      PAWOTGRC.ParametricAlgebraicWaveObservableTransportGeometryRegimeCoherenceTheorem
        CSC.canonicalConstraintGaugePackage
    secondaryParametricAlgebraicWaveObservableTransportGeometryRegimeCoherenceSummary :
      PAWOTGRC.ParametricAlgebraicWaveObservableTransportGeometryRegimeCoherenceTheorem
        SCGI.secondaryConstraintGaugePackage
    canonicalParametricAlgebraicWaveObservableTransportGeometryRegimeStabilitySummary :
      PAWOTGRS.ParametricAlgebraicWaveObservableTransportGeometryRegimeStabilityTheorem
        CSC.canonicalConstraintGaugePackage
    secondaryParametricAlgebraicWaveObservableTransportGeometryRegimeStabilitySummary :
      PAWOTGRS.ParametricAlgebraicWaveObservableTransportGeometryRegimeStabilityTheorem
        SCGI.secondaryConstraintGaugePackage
    canonicalParametricAlgebraicWaveObservableTransportGeometryRegimeCompletenessSummary :
      PAWOTGRC.ParametricAlgebraicWaveObservableTransportGeometryRegimeCompletenessTheorem
        CSC.canonicalConstraintGaugePackage
    secondaryParametricAlgebraicWaveObservableTransportGeometryRegimeCompletenessSummary :
      PAWOTGRC.ParametricAlgebraicWaveObservableTransportGeometryRegimeCompletenessTheorem
        SCGI.secondaryConstraintGaugePackage
    canonicalParametricAlgebraicWaveObservableTransportGeometryRegimeSoundnessSummary :
      PAWOTGRSO.ParametricAlgebraicWaveObservableTransportGeometryRegimeSoundnessTheorem
        CSC.canonicalConstraintGaugePackage
    secondaryParametricAlgebraicWaveObservableTransportGeometryRegimeSoundnessSummary :
      PAWOTGRSO.ParametricAlgebraicWaveObservableTransportGeometryRegimeSoundnessTheorem
        SCGI.secondaryConstraintGaugePackage
    canonicalParametricAlgebraicWaveObservableTransportGeometryRegimeConsistencySummary :
      PAWOTGRCONS.ParametricAlgebraicWaveObservableTransportGeometryRegimeConsistencyTheorem
        CSC.canonicalConstraintGaugePackage
    secondaryParametricAlgebraicWaveObservableTransportGeometryRegimeConsistencySummary :
      PAWOTGRCONS.ParametricAlgebraicWaveObservableTransportGeometryRegimeConsistencyTheorem
        SCGI.secondaryConstraintGaugePackage
    canonicalParametricAlgebraicWaveObservableTransportGeometryRegimeInvarianceSummary :
      PAWOTGRINV.ParametricAlgebraicWaveObservableTransportGeometryRegimeInvarianceTheorem
        CSC.canonicalConstraintGaugePackage
    secondaryParametricAlgebraicWaveObservableTransportGeometryRegimeInvarianceSummary :
      PAWOTGRINV.ParametricAlgebraicWaveObservableTransportGeometryRegimeInvarianceTheorem
        SCGI.secondaryConstraintGaugePackage
    canonicalParametricAlgebraicWaveObservableTransportGeometryRegimeRobustnessSummary :
      PAWOTGRROB.ParametricAlgebraicWaveObservableTransportGeometryRegimeRobustnessTheorem
        CSC.canonicalConstraintGaugePackage
    secondaryParametricAlgebraicWaveObservableTransportGeometryRegimeRobustnessSummary :
      PAWOTGRROB.ParametricAlgebraicWaveObservableTransportGeometryRegimeRobustnessTheorem
        SCGI.secondaryConstraintGaugePackage
    canonicalParametricAlgebraicWaveObservableTransportGeometryRegimeResilienceSummary :
      PAWOTGRRES.ParametricAlgebraicWaveObservableTransportGeometryRegimeResilienceTheorem
        CSC.canonicalConstraintGaugePackage
    secondaryParametricAlgebraicWaveObservableTransportGeometryRegimeResilienceSummary :
      PAWOTGRRES.ParametricAlgebraicWaveObservableTransportGeometryRegimeResilienceTheorem
        SCGI.secondaryConstraintGaugePackage
    canonicalParametricAlgebraicWaveObservableTransportGeometryRegimeIntegritySummary :
      PAWOTGRINT.ParametricAlgebraicWaveObservableTransportGeometryRegimeIntegrityTheorem
        CSC.canonicalConstraintGaugePackage
    secondaryParametricAlgebraicWaveObservableTransportGeometryRegimeIntegritySummary :
      PAWOTGRINT.ParametricAlgebraicWaveObservableTransportGeometryRegimeIntegrityTheorem
        SCGI.secondaryConstraintGaugePackage
    localRecoverySummary : KLRT.KnownLimitsLocalRecoveryTheorem
    effectiveGeometrySummary : KLET.KnownLimitsEffectiveGeometryTheorem
    causalPropagationSummary : KLCPT.KnownLimitsCausalPropagationTheorem
    geometryTransportSummary : KLGT.KnownLimitsGeometryTransportTheorem
    extendedLocalRecoverySummary : KLER.KnownLimitsExtendedLocalRecoveryTheorem
    localPhysicsCoherenceSummary : KLLPC.KnownLimitsLocalPhysicsCoherenceTheorem
    recoveredLocalRegimeSummary : KLRLR.KnownLimitsRecoveredLocalRegimeTheorem
    completeLocalRegimeSummary : KLCLR.KnownLimitsCompleteLocalRegimeTheorem
    recoveredDynamicsSummary : KLRDT.KnownLimitsRecoveredDynamicsTheorem
    recoveredObservablesSummary : KLROT.KnownLimitsRecoveredObservablesTheorem
    recoveredObservableGeometrySummary :
      KLROG.KnownLimitsRecoveredObservableGeometryTheorem
    recoveredTransportConsistencySummary :
      KLRTC.KnownLimitsRecoveredTransportConsistencyTheorem
    recoveredWavefrontSummary :
      KLRWF.KnownLimitsRecoveredWavefrontTheorem
    recoveredWaveGeometrySummary :
      KLRWG.KnownLimitsRecoveredWaveGeometryTheorem
    recoveredWaveRegimeSummary :
      KLRWR.KnownLimitsRecoveredWaveRegimeTheorem
    recoveredWaveObservablesSummary :
      KLRWO.KnownLimitsRecoveredWaveObservablesTheorem
    recoveredWaveObservableTransportSummary :
      KLRWOT.KnownLimitsRecoveredWaveObservableTransportTheorem
    recoveredWaveObservableGeometrySummary :
      KLRWOG.KnownLimitsRecoveredWaveObservableGeometryTheorem
    recoveredWaveObservableTransportGeometrySummary :
      KLRWOTG.KnownLimitsRecoveredWaveObservableTransportGeometryTheorem
    recoveredWaveObservableTransportGeometryCoherenceSummary :
      KLRWOTGC.KnownLimitsRecoveredWaveObservableTransportGeometryCoherenceTheorem
    recoveredWaveObservableTransportGeometryRegimeSummary :
      KLRWOTGR.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeTheorem
    recoveredWaveObservableTransportGeometryRegimeCoherenceSummary :
      KLRWOTGRC.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeCoherenceTheorem
    recoveredWaveObservableTransportGeometryRegimeStabilitySummary :
      KLRWOTGRS.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeStabilityTheorem
    recoveredWaveObservableTransportGeometryRegimeCompletenessSummary :
      KLRWOTGRC.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeCompletenessTheorem
    recoveredWaveObservableTransportGeometryRegimeSoundnessSummary :
      KLRWOTGRSO.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeSoundnessTheorem
    recoveredWaveObservableTransportGeometryRegimeConsistencySummary :
      KLRWOTGRCONS.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeConsistencyTheorem
    recoveredWaveObservableTransportGeometryRegimeInvarianceSummary :
      KLRWOTGRINV.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeInvarianceTheorem
    recoveredWaveObservableTransportGeometryRegimeRobustnessSummary :
      KLRWOTGRROB.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeRobustnessTheorem
    recoveredWaveObservableTransportGeometryRegimeResilienceSummary :
      KLRWOTGRRES.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeResilienceTheorem
    recoveredWaveObservableTransportGeometryRegimeIntegritySummary :
      KLRWOTGRINT.KnownLimitsRecoveredWaveObservableTransportGeometryRegimeIntegrityTheorem
    spinBridgeSummary : SLLB.SpinLocalLorentzBridge CSC.canonicalClosure

canonicalStageCTheoremBundle : CanonicalStageCTheoremBundle
canonicalStageCTheoremBundle =
  record
    { constraintTheoremSummary = CSC.canonicalConstraintTheorem
    ; gaugeBridgeSummary = CSC.canonicalGaugeConstraintBridgeTheorem
    ; canonicalParametricGaugeSummary = CSC.canonicalParametricGaugeConstraintTheorem
    ; secondaryParametricGaugeSummary = SCGI.secondaryParametricGaugeConstraintTheorem
    ; canonicalParametricAlgebraicSummary =
        CSC.canonicalParametricAlgebraicClosureTheorem
    ; secondaryParametricAlgebraicSummary =
        CSC.secondaryParametricAlgebraicClosureTheorem
    ; canonicalParametricAlgebraicCoherenceSummary =
        CSC.canonicalParametricAlgebraicCoherenceTheorem
    ; secondaryParametricAlgebraicCoherenceSummary =
        CSC.secondaryParametricAlgebraicCoherenceTheorem
    ; canonicalParametricAlgebraicStabilitySummary =
        CSC.canonicalParametricAlgebraicStabilityTheorem
    ; secondaryParametricAlgebraicStabilitySummary =
        CSC.secondaryParametricAlgebraicStabilityTheorem
    ; canonicalParametricAlgebraicBundleSummary =
        CSC.canonicalParametricAlgebraicClosureBundleTheorem
    ; secondaryParametricAlgebraicBundleSummary =
        CSC.secondaryParametricAlgebraicClosureBundleTheorem
    ; canonicalParametricAlgebraicConsistencySummary =
        CSC.canonicalParametricAlgebraicConsistencyTheorem
    ; secondaryParametricAlgebraicConsistencySummary =
        CSC.secondaryParametricAlgebraicConsistencyTheorem
    ; canonicalParametricAlgebraicAdmissibilityTransportSummary =
        CSC.canonicalParametricAlgebraicAdmissibilityTransportTheorem
    ; secondaryParametricAlgebraicAdmissibilityTransportSummary =
        CSC.secondaryParametricAlgebraicAdmissibilityTransportTheorem
    ; canonicalParametricAlgebraicPersistenceSummary =
        CSC.canonicalParametricAlgebraicPersistenceTheorem
    ; secondaryParametricAlgebraicPersistenceSummary =
        CSC.secondaryParametricAlgebraicPersistenceTheorem
    ; canonicalParametricAlgebraicGaugeSectorPersistenceSummary =
        CSC.canonicalParametricAlgebraicGaugeSectorPersistenceTheorem
    ; secondaryParametricAlgebraicGaugeSectorPersistenceSummary =
        CSC.secondaryParametricAlgebraicGaugeSectorPersistenceTheorem
    ; canonicalParametricAlgebraicTransportInvarianceSummary =
        CSC.canonicalParametricAlgebraicTransportInvarianceTheorem
    ; secondaryParametricAlgebraicTransportInvarianceSummary =
        CSC.secondaryParametricAlgebraicTransportInvarianceTheorem
    ; canonicalParametricAlgebraicRegimeInvarianceSummary =
        CSC.canonicalParametricAlgebraicRegimeInvarianceTheorem
    ; secondaryParametricAlgebraicRegimeInvarianceSummary =
        CSC.secondaryParametricAlgebraicRegimeInvarianceTheorem
    ; canonicalParametricAlgebraicRegimePersistenceSummary =
        CSC.canonicalParametricAlgebraicRegimePersistenceTheorem
    ; secondaryParametricAlgebraicRegimePersistenceSummary =
        CSC.secondaryParametricAlgebraicRegimePersistenceTheorem
    ; canonicalParametricAlgebraicRegimeCoherenceSummary =
        CSC.canonicalParametricAlgebraicRegimeCoherenceTheorem
    ; secondaryParametricAlgebraicRegimeCoherenceSummary =
        CSC.secondaryParametricAlgebraicRegimeCoherenceTheorem
    ; canonicalParametricAlgebraicWaveObservableTransportSummary =
        CSC.canonicalParametricAlgebraicWaveObservableTransportTheorem
    ; secondaryParametricAlgebraicWaveObservableTransportSummary =
        CSC.secondaryParametricAlgebraicWaveObservableTransportTheorem
    ; canonicalParametricAlgebraicWaveObservableGeometrySummary =
        CSC.canonicalParametricAlgebraicWaveObservableGeometryTheorem
    ; secondaryParametricAlgebraicWaveObservableGeometrySummary =
        CSC.secondaryParametricAlgebraicWaveObservableGeometryTheorem
    ; canonicalParametricAlgebraicWaveObservableTransportGeometryCoherenceSummary =
        CSC.canonicalParametricAlgebraicWaveObservableTransportGeometryCoherenceTheorem
    ; secondaryParametricAlgebraicWaveObservableTransportGeometryCoherenceSummary =
        CSC.secondaryParametricAlgebraicWaveObservableTransportGeometryCoherenceTheorem
    ; canonicalParametricAlgebraicWaveObservableTransportGeometryRegimeSummary =
        CSC.canonicalParametricAlgebraicWaveObservableTransportGeometryRegimeTheorem
    ; secondaryParametricAlgebraicWaveObservableTransportGeometryRegimeSummary =
        CSC.secondaryParametricAlgebraicWaveObservableTransportGeometryRegimeTheorem
    ; canonicalParametricAlgebraicWaveObservableTransportGeometryRegimeCoherenceSummary =
        CSC.canonicalParametricAlgebraicWaveObservableTransportGeometryRegimeCoherenceTheorem
    ; secondaryParametricAlgebraicWaveObservableTransportGeometryRegimeCoherenceSummary =
        CSC.secondaryParametricAlgebraicWaveObservableTransportGeometryRegimeCoherenceTheorem
    ; canonicalParametricAlgebraicWaveObservableTransportGeometryRegimeStabilitySummary =
        CSC.canonicalParametricAlgebraicWaveObservableTransportGeometryRegimeStabilityTheorem
    ; secondaryParametricAlgebraicWaveObservableTransportGeometryRegimeStabilitySummary =
        CSC.secondaryParametricAlgebraicWaveObservableTransportGeometryRegimeStabilityTheorem
    ; canonicalParametricAlgebraicWaveObservableTransportGeometryRegimeCompletenessSummary =
        CSC.canonicalParametricAlgebraicWaveObservableTransportGeometryRegimeCompletenessTheorem
    ; secondaryParametricAlgebraicWaveObservableTransportGeometryRegimeCompletenessSummary =
        CSC.secondaryParametricAlgebraicWaveObservableTransportGeometryRegimeCompletenessTheorem
    ; canonicalParametricAlgebraicWaveObservableTransportGeometryRegimeSoundnessSummary =
        CSC.canonicalParametricAlgebraicWaveObservableTransportGeometryRegimeSoundnessTheorem
    ; secondaryParametricAlgebraicWaveObservableTransportGeometryRegimeSoundnessSummary =
        CSC.secondaryParametricAlgebraicWaveObservableTransportGeometryRegimeSoundnessTheorem
    ; canonicalParametricAlgebraicWaveObservableTransportGeometryRegimeConsistencySummary =
        CSC.canonicalParametricAlgebraicWaveObservableTransportGeometryRegimeConsistencyTheorem
    ; secondaryParametricAlgebraicWaveObservableTransportGeometryRegimeConsistencySummary =
        CSC.secondaryParametricAlgebraicWaveObservableTransportGeometryRegimeConsistencyTheorem
    ; canonicalParametricAlgebraicWaveObservableTransportGeometryRegimeInvarianceSummary =
        CSC.canonicalParametricAlgebraicWaveObservableTransportGeometryRegimeInvarianceTheorem
    ; secondaryParametricAlgebraicWaveObservableTransportGeometryRegimeInvarianceSummary =
        CSC.secondaryParametricAlgebraicWaveObservableTransportGeometryRegimeInvarianceTheorem
    ; canonicalParametricAlgebraicWaveObservableTransportGeometryRegimeRobustnessSummary =
        CSC.canonicalParametricAlgebraicWaveObservableTransportGeometryRegimeRobustnessTheorem
    ; secondaryParametricAlgebraicWaveObservableTransportGeometryRegimeRobustnessSummary =
        CSC.secondaryParametricAlgebraicWaveObservableTransportGeometryRegimeRobustnessTheorem
    ; canonicalParametricAlgebraicWaveObservableTransportGeometryRegimeResilienceSummary =
        CSC.canonicalParametricAlgebraicWaveObservableTransportGeometryRegimeResilienceTheorem
    ; secondaryParametricAlgebraicWaveObservableTransportGeometryRegimeResilienceSummary =
        CSC.secondaryParametricAlgebraicWaveObservableTransportGeometryRegimeResilienceTheorem
    ; canonicalParametricAlgebraicWaveObservableTransportGeometryRegimeIntegritySummary =
        CSC.canonicalParametricAlgebraicWaveObservableTransportGeometryRegimeIntegrityTheorem
    ; secondaryParametricAlgebraicWaveObservableTransportGeometryRegimeIntegritySummary =
        CSC.secondaryParametricAlgebraicWaveObservableTransportGeometryRegimeIntegrityTheorem
    ; localRecoverySummary = CSC.canonicalKnownLimitsLocalRecoveryTheorem
    ; effectiveGeometrySummary = CSC.canonicalKnownLimitsEffectiveGeometryTheorem
    ; causalPropagationSummary = CSC.canonicalKnownLimitsCausalPropagationTheorem
    ; geometryTransportSummary = KLGT.canonicalKnownLimitsGeometryTransportTheorem
    ; extendedLocalRecoverySummary =
        CSC.canonicalKnownLimitsExtendedLocalRecoveryTheorem
    ; localPhysicsCoherenceSummary =
        CSC.canonicalKnownLimitsLocalPhysicsCoherenceTheorem
    ; recoveredLocalRegimeSummary =
        CSC.canonicalKnownLimitsRecoveredLocalRegimeTheorem
    ; completeLocalRegimeSummary =
        CSC.canonicalKnownLimitsCompleteLocalRegimeTheorem
    ; recoveredDynamicsSummary =
        CSC.canonicalKnownLimitsRecoveredDynamicsTheorem
    ; recoveredObservablesSummary =
        CSC.canonicalKnownLimitsRecoveredObservablesTheorem
    ; recoveredObservableGeometrySummary =
        CSC.canonicalKnownLimitsRecoveredObservableGeometryTheorem
    ; recoveredTransportConsistencySummary =
        CSC.canonicalKnownLimitsRecoveredTransportConsistencyTheorem
    ; recoveredWavefrontSummary =
        CSC.canonicalKnownLimitsRecoveredWavefrontTheorem
    ; recoveredWaveGeometrySummary =
        CSC.canonicalKnownLimitsRecoveredWaveGeometryTheorem
    ; recoveredWaveRegimeSummary =
        CSC.canonicalKnownLimitsRecoveredWaveRegimeTheorem
    ; recoveredWaveObservablesSummary =
        CSC.canonicalKnownLimitsRecoveredWaveObservablesTheorem
    ; recoveredWaveObservableTransportSummary =
        CSC.canonicalKnownLimitsRecoveredWaveObservableTransportTheorem
    ; recoveredWaveObservableGeometrySummary =
        CSC.canonicalKnownLimitsRecoveredWaveObservableGeometryTheorem
    ; recoveredWaveObservableTransportGeometrySummary =
        CSC.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryTheorem
    ; recoveredWaveObservableTransportGeometryCoherenceSummary =
        CSC.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryCoherenceTheorem
    ; recoveredWaveObservableTransportGeometryRegimeSummary =
        CSC.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeTheorem
    ; recoveredWaveObservableTransportGeometryRegimeCoherenceSummary =
        CSC.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeCoherenceTheorem
    ; recoveredWaveObservableTransportGeometryRegimeStabilitySummary =
        CSC.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeStabilityTheorem
    ; recoveredWaveObservableTransportGeometryRegimeCompletenessSummary =
        CSC.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeCompletenessTheorem
    ; recoveredWaveObservableTransportGeometryRegimeSoundnessSummary =
        CSC.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeSoundnessTheorem
    ; recoveredWaveObservableTransportGeometryRegimeConsistencySummary =
        CSC.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeConsistencyTheorem
    ; recoveredWaveObservableTransportGeometryRegimeInvarianceSummary =
        CSC.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeInvarianceTheorem
    ; recoveredWaveObservableTransportGeometryRegimeRobustnessSummary =
        CSC.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeRobustnessTheorem
    ; recoveredWaveObservableTransportGeometryRegimeResilienceSummary =
        CSC.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeResilienceTheorem
    ; recoveredWaveObservableTransportGeometryRegimeIntegritySummary =
        CSC.canonicalKnownLimitsRecoveredWaveObservableTransportGeometryRegimeIntegrityTheorem
    ; spinBridgeSummary = CSC.canonicalSpinLocalLorentzBridge
    }
