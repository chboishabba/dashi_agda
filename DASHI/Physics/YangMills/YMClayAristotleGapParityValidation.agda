module DASHI.Physics.YangMills.YMClayAristotleGapParityValidation where

open import Agda.Builtin.Equality using (_≡_)

-- Validation contract for the Aristotle donor tranche.  The production owners
-- below keep four authority/evidence classes separate:
--
--   native Agda theorem term
--   verified Lean donor theorem/worker receipt
--   bounded empirical collider contact
--   still-open physical Yang--Mills inhabitant
--
-- The 2026-09-17 varying-carrier tranche removes F2 as an independent physical
-- payment.  The live physical frontier is F1/F3/F4; embeddings remain input to
-- F3, but Hamiltonian/vacuum compatibility are not primitive F2 hypotheses.

import DASHI.Physics.YangMills.YMClayAristotleDonorAtlasExact as Atlas
import DASHI.Physics.YangMills.YMClayVacuumSectorSpectralGapParityExact as Spectral
import DASHI.Physics.YangMills.YMClayLiteralSU2LatticeDonorExact as Lattice
import DASHI.Physics.YangMills.YMClayVaryingCarrierTransportParityExact as Varying
import DASHI.Physics.YangMills.YMClayUniformGapReductionParityExact as UniformGap
import DASHI.Physics.YangMills.YMClayCorrelationCriterionParityExact as Correlation
import DASHI.Physics.YangMills.YMClayCorrelationCriterionParityValidation as CorrelationValidation
import DASHI.Physics.YangMills.YMClayUrsellTransferMixingBoundaryExact as UrsellBoundary
import DASHI.Physics.YangMills.YMClayUrsellTransferMixingBoundaryValidation as UrsellBoundaryValidation
import DASHI.Physics.YangMills.YMClayF1MixingSourceAuditExact as MixingSources
import DASHI.Physics.YangMills.YMClayF1MixingSourceAuditValidation as MixingSourcesValidation
import DASHI.Physics.YangMills.YMClayCMSDrellYanEmpiricalContactBoundaryExact as CMSBoundary
import DASHI.Physics.YangMills.YMClayCMSDrellYanEmpiricalContactBoundaryValidation as CMSBoundaryValidation
import DASHI.Physics.YangMills.YMClayF134ContinuumWeldParityExact as F134
import DASHI.Physics.YangMills.YMClayClosedWorldResidualAudit20260917Exact as ResidualAudit
import DASHI.Physics.YangMills.YMClayF1CanonicalSourceApplicationValidation as F1Canonical
import DASHI.Physics.YangMills.YMClayR387PhysicalMassGapCertificateExact as R387Physical
import DASHI.Physics.YangMills.YMClayOutstandingPhysicalFrontierExact as Frontier
import DASHI.Physics.YangMills.YMClayCanonicalMassGapConclusionExact as Endgame

open Atlas
open Spectral
open Lattice
open Varying
open UniformGap
open Correlation
open CorrelationValidation
open UrsellBoundary
open UrsellBoundaryValidation
open MixingSources
open MixingSourcesValidation
open CMSBoundary
open CMSBoundaryValidation
open F134
open ResidualAudit
open F1Canonical
open R387Physical
open Frontier
open Endgame

vacuumSectorDonorAvailable : Set
vacuumSectorDonorAvailable = VacuumSectorLeanDonorPresent

literalLatticeDonorAvailable : Set
literalLatticeDonorAvailable = LiteralSU2LatticeLeanDonorPresent

varyingCarrierTransportDonorAvailable : Set
varyingCarrierTransportDonorAvailable = VaryingCarrierTransportLeanDonorPresent

uniformGapReductionDonorAvailable : Set
uniformGapReductionDonorAvailable = UniformGapReductionLeanDonorPresent

correlationCriterionDonorAvailableInAggregate : Set
correlationCriterionDonorAvailableInAggregate = CorrelationCriterionLeanDonorPresent

ursellTransferBoundaryAvailableInAggregate : Set
ursellTransferBoundaryAvailableInAggregate = UrsellTransferMixingBoundaryPresent

mixingSourceAuditAvailableInAggregate : Set
mixingSourceAuditAvailableInAggregate = MixingSourceAuditPresent

cmsEmpiricalContactAvailableInAggregate : Set
cmsEmpiricalContactAvailableInAggregate = CMSDrellYanEmpiricalContactPresent

transferOperatorArtifactAvailable : Atlas.LeanTheoremArtifact
transferOperatorArtifactAvailable = Atlas.literalSU2TransferOperatorGapLean

-- Second-round transfer-operator sharpening: the continuum weld does not need
-- one trajectory-uniform c<1.  It only consumes the per-step defect relation
-- Delta*a_k <= 1-c_k; hence c_k may approach one at O(a_k).
trajectoryUniformDecorrelatorConstantNotRequired :
  UniformGap.trajectoryUniformCRequired ≡ false
trajectoryUniformDecorrelatorConstantNotRequired =
  UniformGap.trajectoryUniformCRequiredIsFalse

perStepTransferDefectSuffices :
  UniformGap.perStepSpectralDefectConditionSuffices ≡ true
perStepTransferDefectSuffices =
  UniformGap.perStepSpectralDefectConditionSufficesIsTrue

literalTransferOperatorParityAvailable :
  UniformGap.literalTransferOperatorPaymentRecorded ≡ true
literalTransferOperatorParityAvailable =
  UniformGap.literalTransferOperatorPaymentRecordedIsTrue

truncatedCorrelationAlternativeAvailable :
  Correlation.truncatedCorrelationBoundImpliesTwoSliceDecorrelator ≡ true
truncatedCorrelationAlternativeAvailable =
  Correlation.truncatedCorrelationBoundImpliesTwoSliceDecorrelatorIsTrue

uniformJointDensityAlternativeAvailable :
  Correlation.uniformJointDensityMixingImpliesTwoSliceDecorrelator ≡ true
uniformJointDensityAlternativeAvailable =
  Correlation.uniformJointDensityMixingImpliesTwoSliceDecorrelatorIsTrue

interactingMixingStillPhysicalDebt :
  Correlation.interactingWilsonMixingBoundProvedByDonor ≡ false
interactingMixingStillPhysicalDebt =
  Correlation.interactingWilsonMixingBoundProvedByDonorIsFalse

pairwiseUrsellDoesNotSilentlyPayOperatorMixing :
  UrsellBoundary.pairwiseObservableUrsellDecayPaysUniformL2Mixing ≡ false
pairwiseUrsellDoesNotSilentlyPayOperatorMixing =
  UrsellBoundary.pairwiseObservableUrsellDecayPaysUniformL2MixingIsFalse

observableToUniformMixingUpgradeStillOpen :
  UrsellBoundary.observableToUniformMixingUpgradeStillRequired ≡ true
observableToUniformMixingUpgradeStillOpen =
  UrsellBoundary.observableToUniformMixingUpgradeStillRequiredIsTrue

balabanClusterExpansionDoesNotSilentlyPayDensityDefect :
  MixingSources.balabanCMP116DirectlyPaysUniformTwoSliceDensity ≡ false
balabanClusterExpansionDoesNotSilentlyPayDensityDefect =
  MixingSources.balabanCMP116DirectlyPaysUniformTwoSliceDensityIsFalse

finiteAbelianComparatorDoesNotPaySU2F1 :
  MixingSources.finiteAbelianCorrelationDecayPaysSU2ContinuumF1 ≡ false
finiteAbelianComparatorDoesNotPaySU2F1 =
  MixingSources.finiteAbelianCorrelationDecayPaysSU2ContinuumF1IsFalse

sourceAuditConfirmsInteractingMixingOpen :
  MixingSources.interactingSU2TrajectoryMixingStillOpen ≡ true
sourceAuditConfirmsInteractingMixingOpen =
  MixingSources.interactingSU2TrajectoryMixingStillOpenIsTrue

-- Collider contact is retained as an independent evidence axis, never promoted
-- into the analytic proof frontier.
cmsContactDoesNotPayF1InAggregate : CMSBoundary.cmsContactPaysF1 ≡ false
cmsContactDoesNotPayF1InAggregate = CMSBoundary.cmsContactPaysF1IsFalse

cmsContactDoesNotPayF3InAggregate : CMSBoundary.cmsContactPaysF3 ≡ false
cmsContactDoesNotPayF3InAggregate = CMSBoundary.cmsContactPaysF3IsFalse

cmsContactDoesNotPayF4InAggregate : CMSBoundary.cmsContactPaysF4 ≡ false
cmsContactDoesNotPayF4InAggregate = CMSBoundary.cmsContactPaysF4IsFalse

cmsContactRemainsBoundedEmpiricalContact :
  CMSBoundary.cmsContactIsBoundedExperimentalQCDContact ≡ true
cmsContactRemainsBoundedEmpiricalContact =
  CMSBoundary.cmsContactIsBoundedExperimentalQCDContactIsTrue

frontierNoLongerChargesUniformC :
  Frontier.f1TrajectoryUniformCRequired ≡ false
frontierNoLongerChargesUniformC =
  Frontier.f1TrajectoryUniformCRequiredIsFalse

frontierUsesPerStepTransferDefect :
  Frontier.f1PerStepTransferDefectForm ≡ true
frontierUsesPerStepTransferDefect =
  Frontier.f1PerStepTransferDefectFormIsTrue

f134ContinuumWeldDonorAvailable : Set
f134ContinuumWeldDonorAvailable = F134ContinuumWeldLeanDonorPresent

closedWorldResidualAuditAvailable : Set
closedWorldResidualAuditAvailable = ClosedWorldResidualAuditPresent

f1CanonicalSourceApplicationCompilerAvailable : Set
f1CanonicalSourceApplicationCompilerAvailable = f1CanonicalCompilerAvailable

r387PhysicalCompilerAvailable : Set
r387PhysicalCompilerAvailable = PhysicalCertificateCompilerPresent

outstandingFrontierAvailable : Set₁
outstandingFrontierAvailable = OutstandingPhysicalFrontier

f2NoLongerPrimitiveResearchPayment :
  f2PrimitiveResearchPayment ≡ false
f2NoLongerPrimitiveResearchPayment = f2PrimitiveResearchPaymentIsFalse

canonicalConclusionAvailable : ∀ Hamiltonian Vacuum Gap → Set₁
canonicalConclusionAvailable = CanonicalMassGapConclusion

canonicalEndgameCompilerAvailable : Set
canonicalEndgameCompilerAvailable = CanonicalEndgameCompilerPresent
