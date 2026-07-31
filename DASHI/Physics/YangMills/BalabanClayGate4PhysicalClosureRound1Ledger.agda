module DASHI.Physics.YangMills.BalabanClayGate4PhysicalClosureRound1Ledger where

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicProjectionNormalizationExact as Projection
import DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicSupportBudgetsExact as Support
import DASHI.Physics.YangMills.BalabanClayGate4CMP109DyadicCellWeightExact as Weight
import DASHI.Physics.YangMills.BalabanClayGate4TwoFamilyChannelMajorantExact as Channels
import DASHI.Physics.YangMills.BalabanClayGate4HRBetaLocalToUniformExact as HRBeta
import DASHI.Physics.YangMills.BalabanClayOSWilsonReflectionPositivityExact as OS

------------------------------------------------------------------------
-- Highest-alpha continuation beyond the finite proof-engineering tranche.
--
-- This round closes the repository-specific four-dimensional dyadic geometry
-- and normalization, supplies explicit 128/8 support envelopes, factors the
-- five Hessian channels through two shared analytic majorants, and reduces the
-- uniform H-R_beta estimate to local absorption.  It also records the exact
-- Menotti--Pelissetto Wilson-action reflection-positivity theorem for the later
-- Osterwalder--Schrader lane without conflating it with RG preservation.
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

twoFamilyFiveChannelReductionLevel =
  Channels.twoFamilyFiveChannelReductionLevel
su2NonlinearityFamilyProvenanceLevel =
  Channels.su2NonlinearityFamilyProvenanceLevel
resolventRelativeBoundFamilyProvenanceLevel =
  Channels.resolventRelativeBoundFamilyProvenanceLevel

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

physicalScalarCellWeightInstantiationInputsLevel =
  Weight.physicalScalarCellWeightInstantiationInputsLevel

physicalSU2DefectMajorantInputsLevel =
  Channels.physicalSU2DefectMajorantInputsLevel
physicalResolventDefectMajorantInputsLevel =
  Channels.physicalResolventDefectMajorantInputsLevel

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
