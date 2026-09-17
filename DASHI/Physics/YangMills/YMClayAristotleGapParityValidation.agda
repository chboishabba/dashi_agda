module DASHI.Physics.YangMills.YMClayAristotleGapParityValidation where

-- RED contract for the Aristotle donor tranche.  The production owners below
-- must keep three authority classes separate:
--
--   native Agda theorem term
--   verified Lean donor theorem/worker receipt
--   still-open physical Yang--Mills inhabitant
--
-- The validation root names the exact surfaces required after comparing the
-- 2026-09-17 Aristotle tar with the merged #987 Agda parity lane.

import DASHI.Physics.YangMills.YMClayAristotleDonorAtlasExact as Atlas
import DASHI.Physics.YangMills.YMClayVacuumSectorSpectralGapParityExact as Spectral
import DASHI.Physics.YangMills.YMClayLiteralSU2LatticeDonorExact as Lattice
import DASHI.Physics.YangMills.YMClayR387PhysicalMassGapCertificateExact as R387Physical
import DASHI.Physics.YangMills.YMClayOutstandingPhysicalFrontierExact as Frontier
import DASHI.Physics.YangMills.YMClayCanonicalMassGapConclusionExact as Endgame

open Atlas
open Spectral
open Lattice
open R387Physical
open Frontier
open Endgame

vacuumSectorDonorAvailable : Set
vacuumSectorDonorAvailable = VacuumSectorLeanDonorPresent

literalLatticeDonorAvailable : Set
literalLatticeDonorAvailable = LiteralSU2LatticeLeanDonorPresent

r387PhysicalCompilerAvailable : Set
r387PhysicalCompilerAvailable = PhysicalCertificateCompilerPresent

outstandingFrontierAvailable : Set₁
outstandingFrontierAvailable = OutstandingPhysicalFrontier

canonicalConclusionAvailable : ∀ Hamiltonian Vacuum Gap → Set₁
canonicalConclusionAvailable = CanonicalMassGapConclusion

canonicalEndgameCompilerAvailable : Set
canonicalEndgameCompilerAvailable = CanonicalEndgameCompilerPresent
