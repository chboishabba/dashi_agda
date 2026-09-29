{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YangMillsClayCMP119OSReconstructionAuthorityExact where

------------------------------------------------------------------------
-- SAME CMP119 OS RECONSTRUCTION -> LIGHTWEIGHT OS AUTHORITY.
--
-- PinnedCMP119OSReconstruction already owns the actual reconstructed Hilbert
-- space, Hamiltonian, vacuum and observable algebra.  The lighter
-- BalabanOSMassGapClosure.OSReconstructionAuthority should therefore be a
-- projection of that exact datum, not a separately selected reconstruction.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as OSSystem
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSReconstructionExact as Pinned
import DASHI.Physics.YangMills.BalabanOSReconstructionMassGapProduction as OSR
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

asPreGapOSReconstructionAuthority :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      sequenceLimit limitLaws quotient division S coreInputs}
    (pinned :
      Pinned.PinnedCMP119PreGapOSReconstruction
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = S}
        coreInputs)
    (group : G) →
  OS.PreGapOSReconstructionAuthority
    (Configuration → ℝ)
    Position
    ℝ
    (OSSystem.continuumOSCoreSystem coreInputs group)
asPreGapOSReconstructionAuthority pinned group = record
  { OS.PreGapOSReconstructionAuthority.HilbertSpaceCore = Hilbert
  ; OS.PreGapOSReconstructionAuthority.HamiltonianCore = Hamiltonian
  ; OS.PreGapOSReconstructionAuthority.VacuumCore = Vector
  ; OS.PreGapOSReconstructionAuthority.WightmanTheoryCore = Algebra
  ; OS.PreGapOSReconstructionAuthority.hilbertSpaceCore =
      OSR.reconstructedHilbertSpaceCore
        (Pinned.reconstructionCore pinned group)
  ; OS.PreGapOSReconstructionAuthority.hamiltonianCore =
      OSR.reconstructedHamiltonianCore
        (Pinned.reconstructionCore pinned group)
  ; OS.PreGapOSReconstructionAuthority.vacuumCore =
      OSR.reconstructedVacuumCore
        (Pinned.reconstructionCore pinned group)
  ; OS.PreGapOSReconstructionAuthority.wightmanTheoryCore =
      OSR.reconstructedObservableAlgebraCore
        (Pinned.reconstructionCore pinned group)
  }

asOSReconstructionAuthority :
  ∀ {G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
      sequenceLimit limitLaws quotient division S osInputs}
    (pinned :
      Pinned.PinnedCMP119OSReconstruction
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient StressTensor Hilbert Vector Hamiltonian Algebra
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = S}
        osInputs)
    (group : G) →
  OS.OSReconstructionAuthority
    (Configuration → ℝ)
    Position
    ℝ
    (OSSystem.continuumOSSystem osInputs group)
asOSReconstructionAuthority pinned group = record
  { OS.OSReconstructionAuthority.HilbertSpace = Hilbert
  ; OS.OSReconstructionAuthority.Hamiltonian = Hamiltonian
  ; OS.OSReconstructionAuthority.Vacuum = Vector
  ; OS.OSReconstructionAuthority.WightmanTheory = Algebra
  ; OS.OSReconstructionAuthority.hilbertSpace =
      OSR.reconstructedHilbertSpace (Pinned.reconstruction pinned group)
  ; OS.OSReconstructionAuthority.hamiltonian =
      OSR.reconstructedHamiltonian (Pinned.reconstruction pinned group)
  ; OS.OSReconstructionAuthority.vacuum =
      OSR.reconstructedVacuum (Pinned.reconstruction pinned group)
  ; OS.OSReconstructionAuthority.wightmanTheory =
      OSR.reconstructedObservableAlgebra (Pinned.reconstruction pinned group)
  }

cmp119LightweightPreGapOSAuthorityCompilerLevel : ProofLevel
cmp119LightweightPreGapOSAuthorityCompilerLevel = machineChecked

cmp119LightweightOSAuthorityCompilerLevel : ProofLevel
cmp119LightweightOSAuthorityCompilerLevel = machineChecked

cmp119LightweightOSAuthorityAdditionalPhysicalPaymentLevel : ProofLevel
cmp119LightweightOSAuthorityAdditionalPhysicalPaymentLevel = machineChecked
