module DASHI.Physics.YangMills.YMAristotleOperatorReturn2026Exact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Physics.YangMills.YMOperatorDomainContinuumSources2026Exact as Src

------------------------------------------------------------------------
-- CROSS-PROVER RETURN: September 2026 Yang--Mills Lean tranche -> Agda.
--
-- This owner records exact theorem surfaces and the strongest bounded reading
-- justified by the sibling Lean files.  Lean proof terms are not transported
-- into Agda.  In particular:
--
--   no boundedness assumption on a total function
--     /= a domain-theoretic unbounded operator theorem,
--
-- and
--
--   strong pointwise transport for E ->L[C] E
--     /= an unbounded closed-form / resolvent continuum theorem.
------------------------------------------------------------------------

data ProofOwner : Set where
  leanOwner agdaOwner openPhysicalObligation : ProofOwner

record LeanReturnStatus : Set where
  constructor lean-return-status
  field
    source : Src.LeanSourceArtifact
    theoremName : String
    owner : ProofOwner
    machineCheckedInLean : Bool
    transportedIntoAgda : Bool
    boundedContinuousOperatorTheorem : Bool
    fullUnboundedDomainTheorem : Bool
    boundedReading : String

open LeanReturnStatus public

generatorUniquenessStatus : LeanReturnStatus
generatorUniquenessStatus = lean-return-status
  Src.generatorUniquenessLean
  "generator_unique_of_evolution_eq / generator_clm_unique"
  leanOwner
  true false
  false false
  "Derivative uniqueness proves equality on a common core for total functions H -> H without assuming boundedness or self-adjointness.  Global operator equality is separately proved for continuous linear maps on a dense core.  No partial-domain unbounded-operator structure is supplied."

nullPreservationFromSymmetryStatus : LeanReturnStatus
nullPreservationFromSymmetryStatus = lean-return-status
  Src.physicalNullQuotientLean
  "preservesNull_of_isSymmetricOp"
  leanOwner
  true false
  false false
  "For an everywhere-defined complex linear map, symmetry of the physical pairing implies preservation of the norm-zero relation.  This does not by itself prove domain invariance for a partial unbounded Hamiltonian."

gaugeInvariantCarrierStatus : LeanReturnStatus
gaugeInvariantCarrierStatus = lean-return-status
  Src.gaugeInvariantCarrierLean
  "hamiltonian_eqOn_core_of_same_evolution / hamiltonian_unique_of_same_evolution_on_dense_core"
  leanOwner
  true false
  false false
  "The gauge-invariant L2 carrier is a closed complete subspace; same-evolution generator uniqueness is instantiated there.  The unbounded wording means no boundedness hypothesis on total functions, not a formalized operator domain D(H)."

gaugeInvariantWitnessStatus : LeanReturnStatus
gaugeInvariantWitnessStatus = lean-return-status
  Src.gaugeInvariantWitnessLean
  "physicalCarrier_nontrivial"
  leanOwner
  true false
  false false
  "ZMod 2 with counting measure and nontrivial translation gauge action has a provably nonzero invariant constant wavefunction, so the carrier interface is non-vacuous."

massGapStrongLimitStatus : LeanReturnStatus
massGapStrongLimitStatus = lean-return-status
  Src.massGapFormTransportLean
  "hasFormGap_of_tendsto / hasFormGap_of_tendsto_of_gap_tendsto"
  leanOwner
  true false
  true false
  "A quadratic-form lower bound above a fixed vacuum survives pointwise strong convergence of bounded continuous linear operators, including converging gap constants.  This is not yet an unbounded-Hamiltonian form/resolvent/Mosco continuum theorem."

currentLeanReturns : List LeanReturnStatus
currentLeanReturns =
  generatorUniquenessStatus ∷
  nullPreservationFromSymmetryStatus ∷
  gaugeInvariantCarrierStatus ∷
  gaugeInvariantWitnessStatus ∷
  massGapStrongLimitStatus ∷ []

------------------------------------------------------------------------
-- Literal audit coverage found in the sibling Lean files.
------------------------------------------------------------------------

record HeadlineAuditCoverage : Set where
  constructor headline-audit-coverage
  field
    generatorUniquenessPrintAxioms : Bool
    physicalNullQuotientPrintAxioms : Bool
    gaugeInvariantCarrierPrintAxioms : Bool
    gaugeInvariantWitnessPrintAxioms : Bool
    massGapFormTransportPrintAxioms : Bool
    everyHeadlineFileHasPrintAxioms : Bool

open HeadlineAuditCoverage public

canonicalHeadlineAuditCoverage : HeadlineAuditCoverage
canonicalHeadlineAuditCoverage = headline-audit-coverage
  true false false true true false

everyHeadlineFileHasPrintAxiomsIsFalse :
  everyHeadlineFileHasPrintAxioms canonicalHeadlineAuditCoverage ≡ false
everyHeadlineFileHasPrintAxiomsIsFalse = refl

------------------------------------------------------------------------
-- Build/source receipt boundary.
------------------------------------------------------------------------

record LeanRoundReceiptBoundary : Set where
  constructor lean-round-receipt-boundary
  field
    reportedLakeBuildGreen : Bool
    reportedBuildJobs : String
    sourceScanFoundProofHoleDeclaration : Bool
    sourceScanFoundImplementedBy : Bool
    replayedByAgdaKernel : Bool
    leanProofIsAgdaProof : Bool

open LeanRoundReceiptBoundary public

canonicalLeanRoundReceiptBoundary : LeanRoundReceiptBoundary
canonicalLeanRoundReceiptBoundary = lean-round-receipt-boundary
  true
  "8175 jobs reported by the attached Lean round"
  false
  false
  false
  false

leanProofIsAgdaProofIsFalse :
  leanProofIsAgdaProof canonicalLeanRoundReceiptBoundary ≡ false
leanProofIsAgdaProofIsFalse = refl

replayedByAgdaKernelIsFalse :
  replayedByAgdaKernel canonicalLeanRoundReceiptBoundary ≡ false
replayedByAgdaKernelIsFalse = refl
