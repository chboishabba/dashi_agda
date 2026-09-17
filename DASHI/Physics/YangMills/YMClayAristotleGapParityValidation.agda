module DASHI.Physics.YangMills.YMClayAristotleGapParityValidation where

open import Agda.Builtin.Equality using (_≡_)

-- Validation contract for the Aristotle donor tranche.  The production owners
-- below keep three authority classes separate:
--
--   native Agda theorem term
--   verified Lean donor theorem/worker receipt
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