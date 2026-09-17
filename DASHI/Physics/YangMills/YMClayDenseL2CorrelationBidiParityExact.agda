{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayDenseL2CorrelationBidiParityExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Dense-local-observable <-> full physical L2_0 F1 compiler.
--
-- Source-written Lean companion (2026-09-17 attachment worktree):
--   RequestProject/YangMills/Lattice/DenseCorrelationCriterion.lean
--
-- Intended theorem family:
--
--   dense_vacuum_decorrelation_iff_full
--     dense D subset of the closed vacuum complement
--     + transfer-pairing inequality on D
--       <->
--     transfer-pairing inequality on every physical L2_0 state
--
--   truncated_correlation_eq_decorrelation
--     connected two-slice correlation = literal transfer pairing on L2_0
--
--   truncated_correlation_iff_decorrelation
--     pointwise connected-correlation bound <-> transfer decorrelation bound
--
--   decorrelation_of_dense_truncated_correlation
--     dense local/cylinder connected-correlation bound
--       -> full physical L2_0 transfer decorrelator
--
-- The proof strategy is ordinary Hilbert/topological compiler mathematics:
-- the transfer pairing and c*||psi||^2 comparison are continuous on the closed
-- vacuum complement, so a closed inequality set containing a dense subset is
-- the whole complement.  This removes the logical need for an L-infinity
-- Radon--Nikodym density defect if the source can instead pay a uniform bound on
-- a dense local/cylinder observable algebra.
--
-- AUTHORITY / VALIDATION BOUNDARY
--
-- This Agda owner records the theorem grammar and status only.  The new Lean
-- file was written RED-first against the supplied Aristotle archive, but this
-- runtime has no Lean binary/dependency cache, so no fresh Lean kernel receipt
-- is claimed here.  Nor does this compiler prove the physical Bałaban/CMP
-- dense-algebra correlation estimate itself.
------------------------------------------------------------------------

leanSourcePath : String
leanSourcePath =
  "RequestProject/YangMills/Lattice/DenseCorrelationCriterion.lean"

denseFullTheorem : String
denseFullTheorem =
  "dense_vacuum_decorrelation_iff_full"

connectedPairingEqualityTheorem : String
connectedPairingEqualityTheorem =
  "truncated_correlation_eq_decorrelation"

connectedPairingBidiTheorem : String
connectedPairingBidiTheorem =
  "truncated_correlation_iff_decorrelation"

denseConnectedToFullTheorem : String
denseConnectedToFullTheorem =
  "decorrelation_of_dense_truncated_correlation"

denseSubsetLivesInsidePhysicalVacuumComplement : Bool
denseSubsetLivesInsidePhysicalVacuumComplement = true

denseSubsetLivesInsidePhysicalVacuumComplementIsTrue :
  denseSubsetLivesInsidePhysicalVacuumComplement ≡ true
denseSubsetLivesInsidePhysicalVacuumComplementIsTrue = refl

connectedCorrelationEqualsTransferPairingOnVacuumComplement : Bool
connectedCorrelationEqualsTransferPairingOnVacuumComplement = true

connectedCorrelationEqualsTransferPairingOnVacuumComplementIsTrue :
  connectedCorrelationEqualsTransferPairingOnVacuumComplement ≡ true
connectedCorrelationEqualsTransferPairingOnVacuumComplementIsTrue = refl

denseTransferCriterionEquivalentToFullL2VacuumCriterion : Bool
denseTransferCriterionEquivalentToFullL2VacuumCriterion = true

denseTransferCriterionEquivalentToFullL2VacuumCriterionIsTrue :
  denseTransferCriterionEquivalentToFullL2VacuumCriterion ≡ true
denseTransferCriterionEquivalentToFullL2VacuumCriterionIsTrue = refl

fullJointDensityLinfinityDefectRequiredByCompiler : Bool
fullJointDensityLinfinityDefectRequiredByCompiler = false

fullJointDensityLinfinityDefectRequiredByCompilerIsFalse :
  fullJointDensityLinfinityDefectRequiredByCompiler ≡ false
fullJointDensityLinfinityDefectRequiredByCompilerIsFalse = refl

-- The remaining physical payment is now allowed to be a uniform connected
-- correlation estimate on a source-native dense local/cylinder algebra.
physicalDenseLocalCorrelationEstimateConstructedHere : Bool
physicalDenseLocalCorrelationEstimateConstructedHere = false

physicalDenseLocalCorrelationEstimateConstructedHereIsFalse :
  physicalDenseLocalCorrelationEstimateConstructedHere ≡ false
physicalDenseLocalCorrelationEstimateConstructedHereIsFalse = refl

-- Static/source-written status only until the supplied Lean project is rerun.
freshLeanKernelReceiptObservedHere : Bool
freshLeanKernelReceiptObservedHere = false

freshLeanKernelReceiptObservedHereIsFalse :
  freshLeanKernelReceiptObservedHere ≡ false
freshLeanKernelReceiptObservedHereIsFalse = refl

denseL2BidiCompilerLevel : ProofLevel
denseL2BidiCompilerLevel = conditional

physicalDenseLocalCorrelationInputLevel : ProofLevel
physicalDenseLocalCorrelationInputLevel = conditional

data DenseL2CorrelationBidiSourceWritten : Set where
  denseL2CorrelationBidiSourceWritten : DenseL2CorrelationBidiSourceWritten

denseL2CorrelationBidiSourceWrittenWitness : DenseL2CorrelationBidiSourceWritten
denseL2CorrelationBidiSourceWrittenWitness = denseL2CorrelationBidiSourceWritten
