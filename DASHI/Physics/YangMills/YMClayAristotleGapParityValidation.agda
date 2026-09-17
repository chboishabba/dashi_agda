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

f134ContinuumWeldDonorAvailable : Set
f134ContinuumWeldDonorAvailable = F134ContinuumWeldLeanDonorPresent

closedWorldResidualAuditAvailable : Set
closedWorldResidualAuditAvailable = ClosedWorldResidualAuditPresent

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
