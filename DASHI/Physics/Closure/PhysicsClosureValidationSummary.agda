module DASHI.Physics.Closure.PhysicsClosureValidationSummary where

-- Repo-facing validation summary entrypoint for the current Stage C snapshot.
-- Current explicit rigidity outcomes:
--   signed-permutation self-check      -> exactMatch
--   synthetic one-minus admissible case -> exactMatch
--   Bool inversion secondary case      -> signatureOnlyMatch
--   tail-permutation negative control  -> mismatch
-- This surface is intended to make the present validation state easy to cite
-- from the main closure entrypoints without drilling into the validation
-- implementation modules directly.

open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.Bool using (Bool)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import DASHI.Geometry.ConeTimeIsotropy as CTI
import DASHI.Algebra.GaugeGroupContract as GGC
import DASHI.Physics.Constraints.ConcreteInstance as CI

open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureValidation as MCPCV public
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosureValidationShiftInstance as MCPCVS public
open import DASHI.Physics.Closure.MinimalCrediblePhysicsClosure as MCPC
open import DASHI.Physics.Closure.CanonicalStageCStatus as CSS public
  using (ClosureSurfaceStatus)
import DASHI.Physics.Closure.CanonicalStageC as CSC
open import DASHI.Physics.Closure.DynamicalClosure as DC
open import DASHI.Physics.Closure.DynamicalClosureWitness as DCW public
  using (DynamicalClosureWitness)
open import DASHI.Physics.Closure.Validation.FejerOverChiSquared as FCS public
  using (Chi2FalsifierStatus; FejerBenchmarkVerdict)
open import DASHI.Physics.Closure.Validation.FejerOverChiSquaredReport as FCSR
open import DASHI.Physics.Closure.Validation.FejerOverChiSquaredShift as FCSS
open import DASHI.Physics.Closure.Validation.Chi2BoundaryShiftLibrary as CBSL
open import DASHI.Physics.Closure.Validation.ObservableCollapse as OC public
  using (ObservableCollapseVerdict)
open import DASHI.Physics.Closure.Validation.ObservableCollapseReport as OCR
open import DASHI.Physics.Closure.Validation.ObservableCollapseShift as OCS
open import DASHI.Physics.Closure.Validation.SnapThresholdLaw as STL public
  using (SnapThresholdVerdict)
open import DASHI.Physics.Closure.Validation.SnapThresholdLawReport as STLR
open import DASHI.Physics.Closure.Validation.SnapThresholdLawShift as STLS
open import DASHI.Physics.Closure.Validation.SyntheticOneMinusShellComparison as SOSC public
  using (SyntheticPromotionStatus)
open import DASHI.Physics.Closure.Validation.SyntheticOneMinusPromotionBridge as SOPB public
  using
    ( SyntheticOrientationStatus
    ; SyntheticSignatureStatus
    ; SyntheticPromotionBridgeStatus
    )
open import DASHI.Physics.Closure.Validation.RootSystemB4ShellComparison as B4C public
  using (B4ShellComparisonVerdict; B4PromotionStatus)
open import DASHI.Physics.Closure.Validation.OrbitShellSeriesComparison as OSSC public
  using (OrbitShellSeriesVerdict)
open import DASHI.Physics.Closure.Validation.RealizationProfileRigidity as RPR public
  using (RigidityVerdict)
open import DASHI.Physics.Closure.Validation.RealizationProfileRigidityReport as RPRR
open import DASHI.Physics.Closure.Validation.RealizationProfileRigidityShift as RPRS
import DASHI.Physics.Closure.Validation.SyntheticOneMinusAdmissible as SOA
open import DASHI.Physics.OrbitShellGeneratingSeries as OSG public
  using (OrbitShellSeries; SizeMultiplicity)
open import DASHI.Physics.OrbitShellGeneratingSeriesShift as OSGS
open import DASHI.Physics.OrbitShellGeneratingSeriesRootSystemB4 as OSGB4
open import DASHI.Physics.Moonshine.FiniteGradedShellSeries as MFGSS public
  using (FiniteGradedShellSeries)
import DASHI.Physics.Moonshine.FiniteGradedShellSeriesShift as MFGSSS
import DASHI.Physics.Moonshine.FiniteGradedShellSeriesRootSystemB4 as MFGSSB4
open import DASHI.Physics.Moonshine.FiniteTwinedShellTrace as MFTST public
  using (FiniteTwinedShellTrace)
import DASHI.Physics.Moonshine.FiniteTwinedShellTraceShift as MFTSTS
import DASHI.Physics.Moonshine.FiniteTwinedShellTraceRootSystemB4 as MFTSTB4
open import DASHI.Physics.Moonshine.WaveGradedShellModule as MWGSM public
  using (WaveGradedShellModule)
import DASHI.Physics.Moonshine.WaveGradedShellTracePrototype as MWGSTP
open import DASHI.Physics.ShellNeighborhoodClass as SNC public
  using (ShellNeighborhoodClass)
open import DASHI.Physics.OneMinusShellFamilyParametric as OMSFP
open import DASHI.Physics.LorentzNeighborhoodDynamicCandidate as LNDC public
  using (DynamicCandidateStatus)
open import DASHI.Physics.Closure.DynamicalClosureStatus as DCS public
  using
    ( DynamicalClosureStatus
    ; PropagationStatus
    ; CausalAdmissibilityStatus
    ; MonotoneQuantityStatus
    ; EffectiveGeometryStatus
    )
open import DASHI.Physics.OrbitProfileData as OPD
open import DASHI.Physics.Closure.CanonicalConstraintClosureStatus as CCCS public
  using (CanonicalConstraintClosureStatus; CanonicalConstraintClosureState)
open import DASHI.Physics.Closure.CanonicalConstraintClosureWitness as CCCW public
  using (CanonicalConstraintClosureWitness)
open import DASHI.Physics.Closure.CanonicalConstraintClosureTheorem as CCCT public
  using (CanonicalConstraintClosureTheorem)
open import DASHI.Physics.Closure.CanonicalGaugeContractTheorem as CGCT public
  using (canonicalGaugeAdmissible; canonicalGaugeContractTheorem; canonicalGaugeEmergence)
open import DASHI.Physics.Closure.CanonicalGaugeConstraintBridgeTheorem as CGCBT public
  using (CanonicalGaugeConstraintBridgeTheorem)
open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP public
  using (CanonicalConstraintGaugePackage)
open import DASHI.Physics.Closure.ParametricGaugeConstraintTheorem as PGCT public
  using (ParametricGaugeConstraintTheorem)
open import DASHI.Physics.Closure.SecondaryConstraintGaugeInstance as SCGI public
  using (secondaryConstraintGaugePackage; secondaryParametricGaugeConstraintTheorem)
open import DASHI.Physics.Closure.ParametricGaugeConstraintBridgeTheorem as PGCBT public
  using (ParametricGaugeConstraintBridgeTheorem)
open import DASHI.Physics.Closure.ParametricAlgebraicClosureTheorem as PACT public
  using (ParametricAlgebraicClosureTheorem)
open import DASHI.Physics.Closure.ParametricAlgebraicCoherenceTheorem as PACTC public
  using (ParametricAlgebraicCoherenceTheorem)
open import DASHI.Physics.Closure.ParametricAlgebraicStabilityTheorem as PACTS public
  using (ParametricAlgebraicStabilityTheorem)
open import DASHI.Physics.Closure.ParametricAlgebraicClosureBundleTheorem as PACTB public
  using (ParametricAlgebraicClosureBundleTheorem)
open import DASHI.Physics.Closure.ParametricAlgebraicConsistencyTheorem as PACTX public
  using (ParametricAlgebraicConsistencyTheorem)
open import DASHI.Physics.Closure.ParametricAlgebraicAdmissibilityTransportTheorem as PACTAT public
  using (ParametricAlgebraicAdmissibilityTransportTheorem)
open import DASHI.Physics.Closure.ParametricAlgebraicPersistenceTheorem as PACTP public
  using (ParametricAlgebraicPersistenceTheorem)
open import DASHI.Physics.Closure.ParametricAlgebraicGaugeSectorPersistenceTheorem as PAGSP public
  using (ParametricAlgebraicGaugeSectorPersistenceTheorem)
open import DASHI.Physics.Closure.ParametricAlgebraicTransportInvarianceTheorem as PATI public
  using (ParametricAlgebraicTransportInvarianceTheorem)
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeInvarianceTheorem as PARI public
  using (ParametricAlgebraicRegimeInvarianceTheorem)
open import DASHI.Physics.Closure.ParametricAlgebraicRegimePersistenceTheorem as PARP public
  using (ParametricAlgebraicRegimePersistenceTheorem)
open import DASHI.Physics.Closure.ParametricAlgebraicRegimeCoherenceTheorem as PARC public
  using (ParametricAlgebraicRegimeCoherenceTheorem)
open import DASHI.Physics.Closure.ParametricAlgebraicWaveObservableTransportTheorem as PAWOT public
  using (ParametricAlgebraicWaveObservableTransportTheorem)
open import DASHI.Physics.Closure.CanonicalGaugeConstraintRealizedInstances as CGCRI public
  using (CanonicalGaugeConstraintRealizedInstances)
open import DASHI.Physics.Closure.KnownLimitsStatus as KLS public
  using
    ( KnownLimitsStatus
    ; LocalLorentzStatus
    ; PropagationLimitStatus
    ; GRLikeStatus
    ; QFTLikeStatus
    )
open import DASHI.Physics.Closure.KnownLimitsRecovery as KLR public
  using (KnownLimitsRecoveryWitness)
open import DASHI.Physics.Closure.KnownLimitsEffectiveGeometryTheorem as KLET public
  using (KnownLimitsEffectiveGeometryTheorem)
open import DASHI.Physics.Closure.KnownLimitsLocalRecoveryTheorem as KLRT public
  using (KnownLimitsLocalRecoveryTheorem)
open import DASHI.Physics.Closure.KnownLimitsRecoveryWitness as KLRW public
  using (KnownLimitsRecoveryWitnessPlus)
open import DASHI.Physics.Closure.KnownLimitsLocalRecoveryTheorem as KLRT public
  using (KnownLimitsLocalRecoveryTheorem)
open import DASHI.Physics.Closure.KnownLimitsRecoveryWitness as KLRW public
  using (KnownLimitsRecoveryWitnessPlus)
open import DASHI.Physics.Closure.CanonicalSpinDiracConsumer as CSDC public
  using (SpinDiracConsumerFromMinimal)
open import DASHI.Physics.Closure.CanonicalPropagationConsumer as CPC public
  using (PropagationConsumerFromMinimal)
open import DASHI.Physics.Closure.SpinLocalLorentzBridgeTheorem as SLLB public
  using (SpinLocalLorentzBridge)
open import DASHI.Physics.Closure.KnownLimitsPropagationSpinTheorem as KLPST public
  using (KnownLimitsPropagationSpinTheorem)
open import DASHI.Physics.Closure.KnownLimitsRecoveryPackage as KLRP public
  using (KnownLimitsRecoveryPackage)
open import DASHI.Physics.Closure.KnownLimitsCausalPropagationTheorem as KLCPT public
  using (KnownLimitsCausalPropagationTheorem)
open import DASHI.Physics.Closure.KnownLimitsGeometryTransportTheorem as KLGT public
  using (KnownLimitsGeometryTransportTheorem)
open import DASHI.Physics.Closure.KnownLimitsLocalCoherenceTheorem as KLLCT public
  using (KnownLimitsLocalCoherenceTheorem)
open import DASHI.Physics.Closure.KnownLimitsExtendedLocalRecoveryTheorem as KLER public
  using (KnownLimitsExtendedLocalRecoveryTheorem)
open import DASHI.Physics.Closure.KnownLimitsLocalPhysicsCoherenceTheorem as KLLPC public
  using (KnownLimitsLocalPhysicsCoherenceTheorem)
open import DASHI.Physics.Closure.KnownLimitsRecoveredLocalRegimeTheorem as KLRLR public
  using (KnownLimitsRecoveredLocalRegimeTheorem)
open import DASHI.Physics.Closure.KnownLimitsCompleteLocalRegimeTheorem as KLCLR public
  using (KnownLimitsCompleteLocalRegimeTheorem)
open import DASHI.Physics.Closure.KnownLimitsRecoveredDynamicsTheorem as KLRDT public
  using (KnownLimitsRecoveredDynamicsTheorem)
open import DASHI.Physics.Closure.KnownLimitsRecoveredObservablesTheorem as KLROT public
  using (KnownLimitsRecoveredObservablesTheorem)
open import DASHI.Physics.Closure.KnownLimitsRecoveredObservableGeometryTheorem as KLROG public
  using (KnownLimitsRecoveredObservableGeometryTheorem)
open import DASHI.Physics.Closure.KnownLimitsRecoveredTransportConsistencyTheorem as KLRTC public
  using (KnownLimitsRecoveredTransportConsistencyTheorem)
open import DASHI.Physics.Closure.KnownLimitsRecoveredWavefrontTheorem as KLRWF public
  using (KnownLimitsRecoveredWavefrontTheorem)
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveGeometryTheorem as KLRWG public
  using (KnownLimitsRecoveredWaveGeometryTheorem)
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveRegimeTheorem as KLRWR public
  using (KnownLimitsRecoveredWaveRegimeTheorem)
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveObservablesTheorem as KLRWO public
  using (KnownLimitsRecoveredWaveObservablesTheorem)
open import DASHI.Physics.Closure.KnownLimitsRecoveredWaveObservableTransportTheorem as KLRWOT public
  using (KnownLimitsRecoveredWaveObservableTransportTheorem)
open import DASHI.Physics.Closure.CanonicalStageCTheoremBundle as CSTB public
  using (CanonicalStageCTheoremBundle)
open import DASHI.Physics.Closure.CanonicalStageCSummaryBundle as CSSB public
  using (CanonicalStageCSummaryBundle)
open import DASHI.Physics.Closure.CanonicalGeometryConsumer as CGC public
  using (GeometryConsumerFromMinimal)
open import DASHI.Physics.Closure.CanonicalObservableConsumer as COC public
  using (ObservableConsumerFromMinimal)
open import DASHI.Physics.Closure.CanonicalRegimeConsumer as CRC public
  using (RegimeConsumerFromMinimal)
open import DASHI.Physics.Closure.CanonicalRecoveryTransportConsumer as CRTC public
  using (RecoveryTransportConsumerFromMinimal)
open import DASHI.Physics.Closure.CanonicalWavefrontConsumer as CWFC public
  using (WavefrontConsumerFromMinimal)
open import DASHI.Physics.Closure.CanonicalWaveGeometryConsumer as CWGC public
  using (WaveGeometryConsumerFromMinimal)
open import DASHI.Physics.Closure.CanonicalWaveRegimeConsumer as CWRC public
  using (WaveRegimeConsumerFromMinimal)
open import DASHI.Physics.Closure.CanonicalWaveObservableConsumer as CWOC public
  using (WaveObservableConsumerFromMinimal)
open import DASHI.Physics.Closure.CanonicalWaveObservableTransportConsumer as CWOTC public
  using (WaveObservableTransportConsumerFromMinimal)
open import DASHI.Physics.Moonshine.FiniteTwinedTraceDetailedReport as MFTDR public
  using (FiniteTwinedTraceDetailedReport)
open import DASHI.Physics.Moonshine.WaveGradedShellPrototypeSummary as MWGSPS public
  using (WaveGradedShellPrototypeSummary)
open import DASHI.Physics.Moonshine.TwinedComparisonSummary as MTCS public
  using (TwinedComparisonSummary)
open import DASHI.Physics.Moonshine.MoonshinePrototypeComparisonBundle as MPCB public
  using (MoonshinePrototypeComparisonBundle)
open import DASHI.Physics.Moonshine.MoonshineTraceFamilySummary as MTFS public
  using (MoonshineTraceFamilySummary)
open import DASHI.Physics.Moonshine.MoonshineWaveTraceConsistencySummary as MWTCS public
  using (MoonshineWaveTraceConsistencySummary)
open import DASHI.Physics.Moonshine.MoonshineTwinedWaveBundleSummary as MTWBS public
  using (MoonshineTwinedWaveBundleSummary)
open import DASHI.Physics.Moonshine.MoonshineTwinedWaveRegimeSummary as MTWRS public
  using (MoonshineTwinedWaveRegimeSummary)
open import DASHI.Physics.Moonshine.MoonshineTwinedWaveObservableSummary as MTWOS public
  using (MoonshineTwinedWaveObservableSummary)
open import DASHI.Physics.Moonshine.MoonshineTwinedWaveObservableTransportSummary as MTWOTS public
  using (MoonshineTwinedWaveObservableTransportSummary)

validationBundle : MCPCV.MinimalCrediblePhysicsClosureValidation
validationBundle = MCPCVS.minimumCredibleClosureValidationShift

canonicalStageCStatus : CSS.ClosureSurfaceStatus
canonicalStageCStatus = CSC.canonicalClosureStatus

canonicalDynamicsWitnessSummary : DCW.DynamicalClosureWitness
canonicalDynamicsWitnessSummary = CSC.canonicalDynamicsWitness

canonicalConstraintStatusSummary : CCCS.CanonicalConstraintClosureStatus
canonicalConstraintStatusSummary = CSC.canonicalConstraintStatus

canonicalConstraintWitnessSummary : CCCW.CanonicalConstraintClosureWitness
canonicalConstraintWitnessSummary = CSC.canonicalConstraintWitness

canonicalConstraintTheoremSummary : CCCT.CanonicalConstraintClosureTheorem
canonicalConstraintTheoremSummary = CSC.canonicalConstraintTheorem

canonicalGaugeContractTheoremSummary : GGC.UniquenessClaim CI.C
canonicalGaugeContractTheoremSummary = CSC.canonicalGaugeContractTheorem

canonicalGaugeConstraintBridgeTheoremSummary :
  CGCBT.CanonicalGaugeConstraintBridgeTheorem
canonicalGaugeConstraintBridgeTheoremSummary =
  CSC.canonicalGaugeConstraintBridgeTheorem

canonicalConstraintGaugePackageSummary :
  CCGP.CanonicalConstraintGaugePackage
canonicalConstraintGaugePackageSummary =
  CSC.canonicalConstraintGaugePackage

canonicalParametricGaugeConstraintTheoremSummary :
  PGCT.ParametricGaugeConstraintTheorem
    canonicalConstraintGaugePackageSummary
canonicalParametricGaugeConstraintTheoremSummary =
  CSC.canonicalParametricGaugeConstraintTheorem

secondaryConstraintGaugePackageSummary :
  CCGP.CanonicalConstraintGaugePackage
secondaryConstraintGaugePackageSummary =
  CSC.secondaryConstraintGaugePackage

secondaryParametricGaugeConstraintTheoremSummary :
  PGCT.ParametricGaugeConstraintTheorem
    secondaryConstraintGaugePackageSummary
secondaryParametricGaugeConstraintTheoremSummary =
  CSC.secondaryParametricGaugeConstraintTheorem

canonicalParametricGaugeConstraintBridgeTheoremSummary :
  PGCBT.ParametricGaugeConstraintBridgeTheorem
    canonicalConstraintGaugePackageSummary
canonicalParametricGaugeConstraintBridgeTheoremSummary =
  CSC.canonicalParametricGaugeConstraintBridgeTheorem

secondaryParametricGaugeConstraintBridgeTheoremSummary :
  PGCBT.ParametricGaugeConstraintBridgeTheorem
    secondaryConstraintGaugePackageSummary
secondaryParametricGaugeConstraintBridgeTheoremSummary =
  CSC.secondaryParametricGaugeConstraintBridgeTheorem

canonicalGaugeConstraintRealizedInstancesSummary :
  CGCRI.CanonicalGaugeConstraintRealizedInstances
canonicalGaugeConstraintRealizedInstancesSummary =
  CSC.canonicalGaugeConstraintRealizedInstances

canonicalParametricAlgebraicClosureTheoremSummary :
  PACT.ParametricAlgebraicClosureTheorem
    canonicalConstraintGaugePackageSummary
canonicalParametricAlgebraicClosureTheoremSummary =
  CSC.canonicalParametricAlgebraicClosureTheorem

secondaryParametricAlgebraicClosureTheoremSummary :
  PACT.ParametricAlgebraicClosureTheorem
    secondaryConstraintGaugePackageSummary
secondaryParametricAlgebraicClosureTheoremSummary =
  CSC.secondaryParametricAlgebraicClosureTheorem

canonicalParametricAlgebraicCoherenceTheoremSummary :
  PACTC.ParametricAlgebraicCoherenceTheorem
    canonicalConstraintGaugePackageSummary
canonicalParametricAlgebraicCoherenceTheoremSummary =
  CSC.canonicalParametricAlgebraicCoherenceTheorem

secondaryParametricAlgebraicCoherenceTheoremSummary :
  PACTC.ParametricAlgebraicCoherenceTheorem
    secondaryConstraintGaugePackageSummary
secondaryParametricAlgebraicCoherenceTheoremSummary =
  CSC.secondaryParametricAlgebraicCoherenceTheorem

canonicalParametricAlgebraicStabilityTheoremSummary :
  PACTS.ParametricAlgebraicStabilityTheorem
    canonicalConstraintGaugePackageSummary
canonicalParametricAlgebraicStabilityTheoremSummary =
  CSC.canonicalParametricAlgebraicStabilityTheorem

secondaryParametricAlgebraicStabilityTheoremSummary :
  PACTS.ParametricAlgebraicStabilityTheorem
    secondaryConstraintGaugePackageSummary
secondaryParametricAlgebraicStabilityTheoremSummary =
  CSC.secondaryParametricAlgebraicStabilityTheorem

canonicalParametricAlgebraicClosureBundleTheoremSummary :
  PACTB.ParametricAlgebraicClosureBundleTheorem
    canonicalConstraintGaugePackageSummary
canonicalParametricAlgebraicClosureBundleTheoremSummary =
  CSC.canonicalParametricAlgebraicClosureBundleTheorem

secondaryParametricAlgebraicClosureBundleTheoremSummary :
  PACTB.ParametricAlgebraicClosureBundleTheorem
    secondaryConstraintGaugePackageSummary
secondaryParametricAlgebraicClosureBundleTheoremSummary =
  CSC.secondaryParametricAlgebraicClosureBundleTheorem

canonicalParametricAlgebraicConsistencyTheoremSummary :
  PACTX.ParametricAlgebraicConsistencyTheorem
    canonicalConstraintGaugePackageSummary
canonicalParametricAlgebraicConsistencyTheoremSummary =
  CSC.canonicalParametricAlgebraicConsistencyTheorem

secondaryParametricAlgebraicConsistencyTheoremSummary :
  PACTX.ParametricAlgebraicConsistencyTheorem
    secondaryConstraintGaugePackageSummary
secondaryParametricAlgebraicConsistencyTheoremSummary =
  CSC.secondaryParametricAlgebraicConsistencyTheorem

canonicalParametricAlgebraicAdmissibilityTransportTheoremSummary :
  PACTAT.ParametricAlgebraicAdmissibilityTransportTheorem
    canonicalConstraintGaugePackageSummary
canonicalParametricAlgebraicAdmissibilityTransportTheoremSummary =
  CSC.canonicalParametricAlgebraicAdmissibilityTransportTheorem

secondaryParametricAlgebraicAdmissibilityTransportTheoremSummary :
  PACTAT.ParametricAlgebraicAdmissibilityTransportTheorem
    secondaryConstraintGaugePackageSummary
secondaryParametricAlgebraicAdmissibilityTransportTheoremSummary =
  CSC.secondaryParametricAlgebraicAdmissibilityTransportTheorem

canonicalParametricAlgebraicPersistenceTheoremSummary :
  PACTP.ParametricAlgebraicPersistenceTheorem
    canonicalConstraintGaugePackageSummary
canonicalParametricAlgebraicPersistenceTheoremSummary =
  CSC.canonicalParametricAlgebraicPersistenceTheorem

secondaryParametricAlgebraicPersistenceTheoremSummary :
  PACTP.ParametricAlgebraicPersistenceTheorem
    secondaryConstraintGaugePackageSummary
secondaryParametricAlgebraicPersistenceTheoremSummary =
  CSC.secondaryParametricAlgebraicPersistenceTheorem

canonicalParametricAlgebraicGaugeSectorPersistenceTheoremSummary :
  PAGSP.ParametricAlgebraicGaugeSectorPersistenceTheorem
    canonicalConstraintGaugePackageSummary
canonicalParametricAlgebraicGaugeSectorPersistenceTheoremSummary =
  CSC.canonicalParametricAlgebraicGaugeSectorPersistenceTheorem

secondaryParametricAlgebraicGaugeSectorPersistenceTheoremSummary :
  PAGSP.ParametricAlgebraicGaugeSectorPersistenceTheorem
    secondaryConstraintGaugePackageSummary
secondaryParametricAlgebraicGaugeSectorPersistenceTheoremSummary =
  CSC.secondaryParametricAlgebraicGaugeSectorPersistenceTheorem

canonicalParametricAlgebraicTransportInvarianceTheoremSummary :
  PATI.ParametricAlgebraicTransportInvarianceTheorem
    canonicalConstraintGaugePackageSummary
canonicalParametricAlgebraicTransportInvarianceTheoremSummary =
  CSC.canonicalParametricAlgebraicTransportInvarianceTheorem

secondaryParametricAlgebraicTransportInvarianceTheoremSummary :
  PATI.ParametricAlgebraicTransportInvarianceTheorem
    secondaryConstraintGaugePackageSummary
secondaryParametricAlgebraicTransportInvarianceTheoremSummary =
  CSC.secondaryParametricAlgebraicTransportInvarianceTheorem

canonicalParametricAlgebraicRegimeInvarianceTheoremSummary :
  PARI.ParametricAlgebraicRegimeInvarianceTheorem
    canonicalConstraintGaugePackageSummary
canonicalParametricAlgebraicRegimeInvarianceTheoremSummary =
  CSC.canonicalParametricAlgebraicRegimeInvarianceTheorem

secondaryParametricAlgebraicRegimeInvarianceTheoremSummary :
  PARI.ParametricAlgebraicRegimeInvarianceTheorem
    secondaryConstraintGaugePackageSummary
secondaryParametricAlgebraicRegimeInvarianceTheoremSummary =
  CSC.secondaryParametricAlgebraicRegimeInvarianceTheorem

canonicalParametricAlgebraicRegimePersistenceTheoremSummary :
  PARP.ParametricAlgebraicRegimePersistenceTheorem
    canonicalConstraintGaugePackageSummary
canonicalParametricAlgebraicRegimePersistenceTheoremSummary =
  CSC.canonicalParametricAlgebraicRegimePersistenceTheorem

secondaryParametricAlgebraicRegimePersistenceTheoremSummary :
  PARP.ParametricAlgebraicRegimePersistenceTheorem
    secondaryConstraintGaugePackageSummary
secondaryParametricAlgebraicRegimePersistenceTheoremSummary =
  CSC.secondaryParametricAlgebraicRegimePersistenceTheorem

canonicalParametricAlgebraicRegimeCoherenceTheoremSummary :
  PARC.ParametricAlgebraicRegimeCoherenceTheorem
    CSC.canonicalConstraintGaugePackage
canonicalParametricAlgebraicRegimeCoherenceTheoremSummary =
  CSC.canonicalParametricAlgebraicRegimeCoherenceTheorem

canonicalParametricAlgebraicWaveObservableTransportTheoremSummary :
  PAWOT.ParametricAlgebraicWaveObservableTransportTheorem
    CSC.canonicalConstraintGaugePackage
canonicalParametricAlgebraicWaveObservableTransportTheoremSummary =
  CSC.canonicalParametricAlgebraicWaveObservableTransportTheorem

secondaryParametricAlgebraicRegimeCoherenceTheoremSummary :
  PARC.ParametricAlgebraicRegimeCoherenceTheorem
    CSC.secondaryConstraintGaugePackage
secondaryParametricAlgebraicRegimeCoherenceTheoremSummary =
  CSC.secondaryParametricAlgebraicRegimeCoherenceTheorem

canonicalKnownLimitsStatusSummary : KLS.KnownLimitsStatus
canonicalKnownLimitsStatusSummary = CSC.canonicalKnownLimitsStatus

canonicalKnownLimitsRecoverySummary : KLR.KnownLimitsRecoveryWitness
canonicalKnownLimitsRecoverySummary = CSC.canonicalKnownLimitsRecovery

canonicalKnownLimitsRecoveryWitnessSummary :
  KLRW.KnownLimitsRecoveryWitnessPlus
canonicalKnownLimitsRecoveryWitnessSummary =
  CSC.canonicalKnownLimitsRecoveryWitness

canonicalKnownLimitsLocalRecoveryTheoremSummary :
  KLRT.KnownLimitsLocalRecoveryTheorem
canonicalKnownLimitsLocalRecoveryTheoremSummary =
  CSC.canonicalKnownLimitsLocalRecoveryTheorem

canonicalKnownLimitsEffectiveGeometryTheoremSummary :
  KLET.KnownLimitsEffectiveGeometryTheorem
canonicalKnownLimitsEffectiveGeometryTheoremSummary =
  CSC.canonicalKnownLimitsEffectiveGeometryTheorem

canonicalKnownLimitsRecoveryPackageSummary :
  KLRP.KnownLimitsRecoveryPackage
canonicalKnownLimitsRecoveryPackageSummary =
  CSC.canonicalKnownLimitsRecoveryPackage

canonicalKnownLimitsCausalPropagationTheoremSummary :
  KLCPT.KnownLimitsCausalPropagationTheorem
canonicalKnownLimitsCausalPropagationTheoremSummary =
  CSC.canonicalKnownLimitsCausalPropagationTheorem

canonicalKnownLimitsGeometryTransportTheoremSummary :
  KLGT.KnownLimitsGeometryTransportTheorem
canonicalKnownLimitsGeometryTransportTheoremSummary =
  CSC.canonicalKnownLimitsGeometryTransportTheorem

canonicalKnownLimitsLocalCoherenceTheoremSummary :
  KLLCT.KnownLimitsLocalCoherenceTheorem
canonicalKnownLimitsLocalCoherenceTheoremSummary =
  CSC.canonicalKnownLimitsLocalCoherenceTheorem

canonicalKnownLimitsExtendedLocalRecoveryTheoremSummary :
  KLER.KnownLimitsExtendedLocalRecoveryTheorem
canonicalKnownLimitsExtendedLocalRecoveryTheoremSummary =
  CSC.canonicalKnownLimitsExtendedLocalRecoveryTheorem

canonicalKnownLimitsLocalPhysicsCoherenceTheoremSummary :
  KLLPC.KnownLimitsLocalPhysicsCoherenceTheorem
canonicalKnownLimitsLocalPhysicsCoherenceTheoremSummary =
  CSC.canonicalKnownLimitsLocalPhysicsCoherenceTheorem

canonicalKnownLimitsRecoveredLocalRegimeTheoremSummary :
  KLRLR.KnownLimitsRecoveredLocalRegimeTheorem
canonicalKnownLimitsRecoveredLocalRegimeTheoremSummary =
  CSC.canonicalKnownLimitsRecoveredLocalRegimeTheorem

canonicalKnownLimitsCompleteLocalRegimeTheoremSummary :
  KLCLR.KnownLimitsCompleteLocalRegimeTheorem
canonicalKnownLimitsCompleteLocalRegimeTheoremSummary =
  CSC.canonicalKnownLimitsCompleteLocalRegimeTheorem

canonicalKnownLimitsRecoveredDynamicsTheoremSummary :
  KLRDT.KnownLimitsRecoveredDynamicsTheorem
canonicalKnownLimitsRecoveredDynamicsTheoremSummary =
  CSC.canonicalKnownLimitsRecoveredDynamicsTheorem

canonicalKnownLimitsRecoveredObservablesTheoremSummary :
  KLROT.KnownLimitsRecoveredObservablesTheorem
canonicalKnownLimitsRecoveredObservablesTheoremSummary =
  CSC.canonicalKnownLimitsRecoveredObservablesTheorem

canonicalKnownLimitsRecoveredObservableGeometryTheoremSummary :
  KLROG.KnownLimitsRecoveredObservableGeometryTheorem
canonicalKnownLimitsRecoveredObservableGeometryTheoremSummary =
  CSC.canonicalKnownLimitsRecoveredObservableGeometryTheorem

canonicalKnownLimitsRecoveredTransportConsistencyTheoremSummary :
  KLRTC.KnownLimitsRecoveredTransportConsistencyTheorem
canonicalKnownLimitsRecoveredTransportConsistencyTheoremSummary =
  CSC.canonicalKnownLimitsRecoveredTransportConsistencyTheorem

canonicalKnownLimitsRecoveredWavefrontTheoremSummary :
  KLRWF.KnownLimitsRecoveredWavefrontTheorem
canonicalKnownLimitsRecoveredWavefrontTheoremSummary =
  CSC.canonicalKnownLimitsRecoveredWavefrontTheorem

canonicalKnownLimitsRecoveredWaveGeometryTheoremSummary :
  KLRWG.KnownLimitsRecoveredWaveGeometryTheorem
canonicalKnownLimitsRecoveredWaveGeometryTheoremSummary =
  CSC.canonicalKnownLimitsRecoveredWaveGeometryTheorem

canonicalKnownLimitsRecoveredWaveRegimeTheoremSummary :
  KLRWR.KnownLimitsRecoveredWaveRegimeTheorem
canonicalKnownLimitsRecoveredWaveRegimeTheoremSummary =
  CSC.canonicalKnownLimitsRecoveredWaveRegimeTheorem

canonicalKnownLimitsRecoveredWaveObservablesTheoremSummary :
  KLRWO.KnownLimitsRecoveredWaveObservablesTheorem
canonicalKnownLimitsRecoveredWaveObservablesTheoremSummary =
  CSC.canonicalKnownLimitsRecoveredWaveObservablesTheorem

canonicalKnownLimitsRecoveredWaveObservableTransportTheoremSummary :
  KLRWOT.KnownLimitsRecoveredWaveObservableTransportTheorem
canonicalKnownLimitsRecoveredWaveObservableTransportTheoremSummary =
  CSC.canonicalKnownLimitsRecoveredWaveObservableTransportTheorem

canonicalSpinLocalLorentzBridgeSummary :
  SLLB.SpinLocalLorentzBridge CSC.canonicalClosure
canonicalSpinLocalLorentzBridgeSummary =
  CSC.canonicalSpinLocalLorentzBridge

canonicalKnownLimitsPropagationSpinTheoremSummary :
  KLPST.KnownLimitsPropagationSpinTheorem
canonicalKnownLimitsPropagationSpinTheoremSummary =
  CSC.canonicalKnownLimitsPropagationSpinTheorem

canonicalSpinDiracConsumerSummary :
  CSDC.SpinDiracConsumerFromMinimal CSC.canonicalClosure
canonicalSpinDiracConsumerSummary = CSC.canonicalSpinDiracConsumer

canonicalPropagationConsumerSummary :
  CPC.PropagationConsumerFromMinimal CSC.canonicalClosure
canonicalPropagationConsumerSummary = CSC.canonicalPropagationConsumer

canonicalGeometryConsumerSummary :
  CGC.GeometryConsumerFromMinimal CSC.canonicalClosure
canonicalGeometryConsumerSummary = CSC.canonicalGeometryConsumer

canonicalObservableConsumerSummary :
  COC.ObservableConsumerFromMinimal CSC.canonicalClosure
canonicalObservableConsumerSummary = CSC.canonicalObservableConsumer

canonicalRegimeConsumerSummary :
  CRC.RegimeConsumerFromMinimal CSC.canonicalClosure
canonicalRegimeConsumerSummary = CSC.canonicalRegimeConsumer

canonicalRecoveryTransportConsumerSummary :
  CRTC.RecoveryTransportConsumerFromMinimal CSC.canonicalClosure
canonicalRecoveryTransportConsumerSummary =
  CSC.canonicalRecoveryTransportConsumer

canonicalWavefrontConsumerSummary :
  CWFC.WavefrontConsumerFromMinimal CSC.canonicalClosure
canonicalWavefrontConsumerSummary =
  CSC.canonicalWavefrontConsumer

canonicalWaveGeometryConsumerSummary :
  CWGC.WaveGeometryConsumerFromMinimal CSC.canonicalClosure
canonicalWaveGeometryConsumerSummary =
  CSC.canonicalWaveGeometryConsumer

canonicalWaveRegimeConsumerSummary :
  CWRC.WaveRegimeConsumerFromMinimal CSC.canonicalClosure
canonicalWaveRegimeConsumerSummary =
  CSC.canonicalWaveRegimeConsumer

canonicalWaveObservableConsumerSummary :
  CWOC.WaveObservableConsumerFromMinimal CSC.canonicalClosure
canonicalWaveObservableConsumerSummary =
  CSC.canonicalWaveObservableConsumer

canonicalWaveObservableTransportConsumerSummary :
  CWOTC.WaveObservableTransportConsumerFromMinimal CSC.canonicalClosure
canonicalWaveObservableTransportConsumerSummary =
  CSC.canonicalWaveObservableTransportConsumer

canonicalTheoremBundleSummary : CSTB.CanonicalStageCTheoremBundle
canonicalTheoremBundleSummary = CSTB.canonicalStageCTheoremBundle

canonicalSummaryBundle : CSSB.CanonicalStageCSummaryBundle
canonicalSummaryBundle = CSSB.canonicalStageCSummaryBundle

canonicalMoonshinePrototypeComparisonBundleSummary :
  MPCB.MoonshinePrototypeComparisonBundle
canonicalMoonshinePrototypeComparisonBundleSummary =
  MPCB.canonicalMoonshinePrototypeComparisonBundle

canonicalMoonshineTraceFamilySummary :
  MTFS.MoonshineTraceFamilySummary
canonicalMoonshineTraceFamilySummary =
  MTFS.canonicalMoonshineTraceFamilySummary

canonicalMoonshineWaveTraceConsistencySummary :
  MWTCS.MoonshineWaveTraceConsistencySummary
canonicalMoonshineWaveTraceConsistencySummary =
  MWTCS.canonicalMoonshineWaveTraceConsistencySummary

canonicalMoonshineTwinedWaveBundleSummary :
  MTWBS.MoonshineTwinedWaveBundleSummary
canonicalMoonshineTwinedWaveBundleSummary =
  MTWBS.canonicalMoonshineTwinedWaveBundleSummary

canonicalMoonshineTwinedWaveRegimeSummary :
  MTWRS.MoonshineTwinedWaveRegimeSummary
canonicalMoonshineTwinedWaveRegimeSummary =
  MTWRS.canonicalMoonshineTwinedWaveRegimeSummary

canonicalMoonshineTwinedWaveObservableSummary :
  MTWOS.MoonshineTwinedWaveObservableSummary
canonicalMoonshineTwinedWaveObservableSummary =
  MTWOS.canonicalMoonshineTwinedWaveObservableSummary

canonicalMoonshineTwinedWaveObservableTransportSummary :
  MTWOTS.MoonshineTwinedWaveObservableTransportSummary
canonicalMoonshineTwinedWaveObservableTransportSummary =
  MTWOTS.canonicalMoonshineTwinedWaveObservableTransportSummary

selfSnapshotVerdict : RPR.RigidityVerdict
selfSnapshotVerdict = MCPCV.selfVerdict validationBundle

admissibleSnapshotVerdict : RPR.RigidityVerdict
admissibleSnapshotVerdict = MCPCV.admissibleVerdict validationBundle

boolInvSnapshotVerdict : RPR.RigidityVerdict
boolInvSnapshotVerdict = RPRS.boolInvVerdict

negativeControlSnapshotVerdict : RPR.RigidityVerdict
negativeControlSnapshotVerdict = MCPCV.negativeControlVerdict validationBundle

fejerShiftVerdict : FCS.FejerBenchmarkVerdict
fejerShiftVerdict = FCSS.shiftVerdict

canonicalDynamicsStatus : DCS.DynamicalClosureStatus
canonicalDynamicsStatus =
  DC.DynamicalClosure.status
    (MCPC.authoritativeDynamics
      (MCPCV.MinimalCrediblePhysicsClosureValidation.closure validationBundle))

fejerShiftChi2Status : FCS.Chi2FalsifierStatus
fejerShiftChi2Status =
  FCS.FejerOverChi2Harness.chi2FalsifierStatus
    (FCSR.FejerOverChi2Report.harness FCSS.shiftReport)

chi2BoundaryCaseCount : Nat
chi2BoundaryCaseCount = CBSL.caseCount

observableCollapseShiftVerdict : OC.ObservableCollapseVerdict
observableCollapseShiftVerdict =
  OCR.ObservableCollapseReport.verdict OCS.shiftReport

snapThresholdShiftVerdict : STL.SnapThresholdVerdict
snapThresholdShiftVerdict =
  STLR.SnapThresholdReport.verdict STLS.shiftReport

syntheticOneMinusShellMatch : Bool
syntheticOneMinusShellMatch =
  SOSC.SyntheticShellComparisonReport.shell1Matches SOSC.report

syntheticOneMinusProfileMatch : Bool
syntheticOneMinusProfileMatch =
  SOSC.SyntheticShellComparisonReport.shell2Matches SOSC.report

syntheticOneMinusPromotionStatus : SOSC.SyntheticPromotionStatus
syntheticOneMinusPromotionStatus =
  SOSC.SyntheticShellComparisonReport.promotionStatus SOSC.report

syntheticOneMinusOrientationStatus : SOPB.SyntheticOrientationStatus
syntheticOneMinusOrientationStatus =
  SOPB.SyntheticPromotionBridge.orientationStatus SOPB.bridge

syntheticOneMinusSignatureStatus : SOPB.SyntheticSignatureStatus
syntheticOneMinusSignatureStatus =
  SOPB.SyntheticPromotionBridge.signatureStatus SOPB.bridge

syntheticOneMinusBridgeStatus : SOPB.SyntheticPromotionBridgeStatus
syntheticOneMinusBridgeStatus =
  SOPB.SyntheticPromotionBridge.promotionStatus SOPB.bridge

syntheticOneMinusBridgedOrientationTag : Nat
syntheticOneMinusBridgedOrientationTag =
  SOPB.SyntheticPromotionBridge.orientationTag SOPB.bridge

syntheticOneMinusBridgedSignature : CTI.Signature
syntheticOneMinusBridgedSignature =
  SOPB.SyntheticPromotionBridge.signature SOPB.bridge

lorentzDynamicCandidateStatus : LNDC.DynamicCandidateStatus
lorentzDynamicCandidateStatus =
  LNDC.LorentzNeighborhoodDynamicCandidate.status LNDC.syntheticReady

syntheticAdmissibleVerdict : RPR.RigidityVerdict
syntheticAdmissibleVerdict = SOA.syntheticAdmissibleVerdict

b4ShellComparisonVerdict : B4C.B4ShellComparisonVerdict
b4ShellComparisonVerdict =
  B4C.B4ShellComparisonReport.verdict B4C.report

b4PromotionStatus : B4C.B4PromotionStatus
b4PromotionStatus =
  B4C.B4ShellComparisonReport.promotionStatus B4C.report

shiftShellNeighborhood : SNC.ShellNeighborhoodClass
shiftShellNeighborhood =
  SNC.classifyShell1Neighborhood OPD.shell1_p3_q1

shiftMatchesParametricOneMinus :
  shiftShellNeighborhood ≡ SNC.oneMinusShellNeighborhood
shiftMatchesParametricOneMinus = OMSFP.shiftMatchesParametricFamily

parametricOneMinusFamilyTheorem :
  ∀ m →
  OMSFP.familyFormulaNeighborhood (suc (suc m))
  ≡ SNC.oneMinusShellNeighborhood
parametricOneMinusFamilyTheorem = OMSFP.familyFormulaNeighborhood-theorem

b4ShellNeighborhood : SNC.ShellNeighborhoodClass
b4ShellNeighborhood =
  B4C.B4ShellComparisonReport.shellNeighborhood B4C.report

shiftOrbitShellSeries : OSG.OrbitShellSeries
shiftOrbitShellSeries = OSGS.shiftSeries

b4OrbitShellSeries : OSG.OrbitShellSeries
b4OrbitShellSeries = OSGB4.b4Series

b4SeriesVerdict : OSSC.OrbitShellSeriesVerdict
b4SeriesVerdict =
  B4C.B4ShellComparisonReport.seriesVerdict B4C.report

shiftFiniteGradedShellSeries : MFGSS.FiniteGradedShellSeries
shiftFiniteGradedShellSeries = MFGSSS.shiftFiniteGradedShellSeries

b4FiniteGradedShellSeries : MFGSS.FiniteGradedShellSeries
b4FiniteGradedShellSeries = MFGSSB4.b4FiniteGradedShellSeries

shiftIdentityTwinedTrace : MFTST.FiniteTwinedShellTrace
shiftIdentityTwinedTrace = MFTSTS.shiftIdentityTwinedTrace

shiftNontrivialTwinedTrace : MFTST.FiniteTwinedShellTrace
shiftNontrivialTwinedTrace = MFTSTS.shiftNontrivialTwinedTrace

b4IdentityTwinedTrace : MFTST.FiniteTwinedShellTrace
b4IdentityTwinedTrace = MFTSTB4.b4IdentityTwinedTrace

b4NontrivialTwinedTrace : MFTST.FiniteTwinedShellTrace
b4NontrivialTwinedTrace = MFTSTB4.b4NontrivialTwinedTrace

finiteTwinedDetailedReport : MFTDR.FiniteTwinedTraceDetailedReport
finiteTwinedDetailedReport = MFTDR.finiteTwinedTraceDetailedReport

shiftWaveGradedShellPrototype : MWGSM.WaveGradedShellModule
shiftWaveGradedShellPrototype = MWGSTP.shiftWaveGradedShellModulePrototype

shiftWaveGradedShellPrototypeSummary :
  MWGSPS.WaveGradedShellPrototypeSummary
shiftWaveGradedShellPrototypeSummary =
  MWGSPS.shiftWaveGradedShellPrototypeSummary

canonicalTwinedComparisonSummary : MTCS.TwinedComparisonSummary
canonicalTwinedComparisonSummary = MTCS.canonicalTwinedComparisonSummary
