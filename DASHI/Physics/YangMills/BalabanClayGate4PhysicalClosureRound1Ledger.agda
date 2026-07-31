module DASHI.Physics.YangMills.BalabanClayGate4PhysicalClosureRound1Ledger where

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicProjectionNormalizationExact as Projection
import DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicSupportBudgetsExact as Support
import DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicCellWeightExact as Weight
import DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicEnvelopeSchurExact as Schur
import DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicPrintedPhysicalInstantiationExact as PrintedPhysical
import DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicFrechetAssemblyExact as Frechet
import DASHI.Physics.YangMills.BalabanClayGate4TwoFamilyChannelMajorantExact as Channels
import DASHI.Physics.YangMills.BalabanClayGate4T3TwoFamilyChannelReuseExact as T3Channels
import DASHI.Physics.YangMills.BalabanClayGate4TreeBackgroundSliceTransitionExact as Slice
import DASHI.Physics.YangMills.BalabanClayGate4HRBetaLocalToUniformExact as HRBeta
import DASHI.Physics.YangMills.BalabanClayOSWilsonReflectionPositivityExact as OS

------------------------------------------------------------------------
-- Highest-alpha continuation beyond the finite proof-engineering tranche.
--
-- This round closes the repository-specific four-dimensional dyadic geometry
-- and normalization, supplies explicit 128/8 Schur envelopes, fixes the printed
-- equation-(0.12) instance to that geometry and principal log, assembles its
-- exact componentwise Fréchet kernel, factors the five Hessian channels through
-- two shared analytic majorants and discharges the five T3 form estimates from
-- those two families.  It also fixes the local tree/background-slice transition,
-- reduces the uniform H-R_beta estimate to local absorption, and records the
-- exact Menotti--Pelissetto Wilson-action reflection-positivity result without
-- conflating it with RG preservation.
------------------------------------------------------------------------

dyadicCyclicSplitRoundTripLevel =
  Projection.dyadicCyclicSplitRoundTripLevel

dyadicFourTorusProjectionLevel =
  Projection.dyadicFourTorusProjectionLevel

dyadicFourTorusFibreBijectionLevel =
  Projection.dyadicFourTorusFibreBijectionLevel

dyadicFourTorusFibreCardinalityLevel =
  Projection.dyadicFourTorusFibreCardinalityLevel

cmp109DyadicFourDimensionalNormalizationLevel =
  Projection.cmp109DyadicFourDimensionalNormalizationLevel

cmp109DyadicRowEnvelopeLevel = Support.cmp109DyadicRowEnvelopeLevel
cmp109DyadicRowCardinality128Level =
  Support.cmp109DyadicRowCardinality128Level
periodicStepInverseCertificateDecisionLevel =
  Support.periodicStepInverseCertificateDecisionLevel
periodicStepInverseCertificateUniversalLiftLevel =
  Support.periodicStepInverseCertificateUniversalLiftLevel
cmp109DyadicColumnEnvelopeLevel = Support.cmp109DyadicColumnEnvelopeLevel
cmp109DyadicColumnCardinality8Level =
  Support.cmp109DyadicColumnCardinality8Level

cmp109DyadicCellWeightScalingLevel =
  Weight.cmp109DyadicCellWeightScalingLevel
cmp109DyadicWeightedAdjointRatioLevel =
  Weight.cmp109DyadicWeightedAdjointRatioLevel
cmp109DyadicBlockAverageCancellationLevel =
  Weight.cmp109DyadicBlockAverageCancellationLevel

cmp109DyadicRow128EntryBudgetLevel =
  Schur.cmp109DyadicRow128EntryBudgetLevel
cmp109DyadicColumn8EntryBudgetLevel =
  Schur.cmp109DyadicColumn8EntryBudgetLevel

cmp109DyadicPrintedMapInstantiationLevel =
  PrintedPhysical.cmp109DyadicPrintedMapInstantiationLevel
cmp109DyadicSupportIdentificationLevel =
  PrintedPhysical.cmp109DyadicSupportIdentificationLevel
cmp109DyadicNormalizationIdentificationLevel =
  PrintedPhysical.cmp109DyadicNormalizationIdentificationLevel
cmp109DyadicPrincipalLogTermIdentificationLevel =
  PrintedPhysical.cmp109DyadicPrincipalLogTermIdentificationLevel

cmp109FrechetKernelDefinitionLevel =
  Frechet.cmp109FrechetKernelDefinitionLevel
cmp109FrechetEndpointSupportLevel =
  Frechet.cmp109FrechetEndpointSupportLevel
cmp109PhysicalDerivativeChainAssemblyLevel =
  Frechet.cmp109PhysicalDerivativeChainAssemblyLevel

twoFamilyFiveChannelReductionLevel =
  Channels.twoFamilyFiveChannelReductionLevel
su2NonlinearityFamilyProvenanceLevel =
  Channels.su2NonlinearityFamilyProvenanceLevel
resolventRelativeBoundFamilyProvenanceLevel =
  Channels.resolventRelativeBoundFamilyProvenanceLevel
t3TwoFamilyFiveEstimateDischargeLevel =
  T3Channels.t3TwoFamilyFiveEstimateDischargeLevel

localSliceTangentIsomorphismAssemblyLevel =
  Slice.localSliceTangentIsomorphismAssemblyLevel
sliceHessianEigenpairTransportLevel =
  Slice.sliceHessianEigenpairTransportLevel
sliceCoercivityTransportLevel =
  Slice.sliceCoercivityTransportLevel

hrBetaFiniteAbsoluteTriangleLevel =
  HRBeta.hrBetaFiniteAbsoluteTriangleLevel
hrBetaLocalToUniformAbsorptionLevel =
  HRBeta.hrBetaLocalToUniformAbsorptionLevel
hrBetaPhysicalHalfNormalizationAssemblyLevel =
  HRBeta.hrBetaPhysicalHalfNormalizationAssemblyLevel

menottiPelissettoBibliographyLevel = OS.menottiPelissettoBibliographyLevel
wilsonLinkPlaneReflectionPositivityLevel =
  OS.wilsonLinkPlaneReflectionPositivityLevel
wilsonSitePlaneReflectionPositivityLevel =
  OS.wilsonSitePlaneReflectionPositivityLevel
wilsonAllSeparationParityAssemblyLevel =
  OS.wilsonAllSeparationParityAssemblyLevel
wilsonTransferMatrixPositivityProvenanceLevel =
  OS.wilsonTransferMatrixPositivityProvenanceLevel

------------------------------------------------------------------------
-- Remaining analytic/physical inhabitants after this round.
------------------------------------------------------------------------

physicalCMP109ContourValueInputsLevel =
  PrintedPhysical.physicalCMP109ContourValueInputsLevel
physicalCMP109PrincipalChartInputsLevel =
  PrintedPhysical.physicalCMP109PrincipalChartInputsLevel
physicalCMP109FrechetKernelInputsLevel =
  PrintedPhysical.physicalCMP109FrechetKernelInputsLevel
physicalCMP109ComponentDerivativeInputsLevel =
  Frechet.physicalCMP109ComponentDerivativeInputsLevel
physicalCMP109ProductChainRuleInputsLevel =
  Frechet.physicalCMP109ProductChainRuleInputsLevel

physicalScalarCellWeightInstantiationInputsLevel =
  Weight.physicalScalarCellWeightInstantiationInputsLevel
physicalDyadicEnvelopeDominationInputsLevel =
  Schur.physicalDyadicEnvelopeDominationInputsLevel
physicalDyadicEntryNormBoundInputsLevel =
  Schur.physicalDyadicEntryNormBoundInputsLevel

physicalSU2DefectMajorantInputsLevel =
  Channels.physicalSU2DefectMajorantInputsLevel
physicalResolventDefectMajorantInputsLevel =
  Channels.physicalResolventDefectMajorantInputsLevel
physicalT3SU2FamilyIdentificationInputsLevel =
  T3Channels.physicalT3SU2FamilyIdentificationInputsLevel
physicalT3ResolventFamilyIdentificationInputsLevel =
  T3Channels.physicalT3ResolventFamilyIdentificationInputsLevel

physicalTreeBackgroundLocalTransitionInputsLevel =
  Slice.physicalTreeBackgroundLocalTransitionInputsLevel
physicalFaddeevPopovInvertibilityInputsLevel =
  Slice.physicalFaddeevPopovInvertibilityInputsLevel
physicalSliceNormIsometryInputsLevel =
  Slice.physicalSliceNormIsometryInputsLevel

physicalHRBetaLocalDecompositionInputsLevel =
  HRBeta.physicalHRBetaLocalDecompositionInputsLevel
physicalHRBetaLocalAbsoluteEstimatesInputsLevel =
  HRBeta.physicalHRBetaLocalAbsoluteEstimatesInputsLevel

physicalWilsonActionOSIdentificationInputsLevel =
  OS.physicalWilsonActionOSIdentificationInputsLevel
rgEffectiveActionReflectionPositivityPreservationInputsLevel =
  OS.rgEffectiveActionReflectionPositivityPreservationInputsLevel

physicalClosureRound1LedgerLevel : ProofLevel
physicalClosureRound1LedgerLevel = machineChecked
