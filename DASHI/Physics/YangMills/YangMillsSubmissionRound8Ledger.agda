module DASHI.Physics.YangMills.YangMillsSubmissionRound8Ledger where

open import Agda.Builtin.String using (String)

import DASHI.Physics.YangMills.YangMillsSubmissionRound7Ledger as Round7
open import DASHI.Physics.YangMills.CompactLieProofLevel

record SubmissionRound8Ledger : Set where
  field
    bishopRatioMonotonicityStatus : Round7.SubmissionGroupStatus
    bishopFirstOmittedReductionStatus : Round7.SubmissionGroupStatus
    bishopConcreteBracketStatus : Round7.SubmissionGroupStatus

    p06CanonicalAnimalConstantStatus : Round7.SubmissionGroupStatus
    p06PhysicalModelLeafStatus : Round7.SubmissionGroupStatus
    a1a2a3FiniteInfluenceStatus : Round7.SubmissionGroupStatus
    scalarGeometricSummationStatus : Round7.SubmissionGroupStatus

    p11PrefixTailReductionStatus : Round7.SubmissionGroupStatus
    p11PhysicalPrefixTailStatus : Round7.SubmissionGroupStatus

    stepVLogAnimalMarginStatus : Round7.SubmissionGroupStatus
    stepVPhysicalLogExpStatus : Round7.SubmissionGroupStatus

    recentInfluenceManuscriptStatus : Round7.SubmissionGroupStatus
    boundary : String

open SubmissionRound8Ledger public

currentSubmissionRound8Ledger : SubmissionRound8Ledger
currentSubmissionRound8Ledger = record
  { bishopRatioMonotonicityStatus = Round7.ownedReducerAvailable
  ; bishopFirstOmittedReductionStatus = Round7.ownedReducerAvailable
  ; bishopConcreteBracketStatus = Round7.physicalInputsConditional
  ; p06CanonicalAnimalConstantStatus = Round7.ownedReducerAvailable
  ; p06PhysicalModelLeafStatus = Round7.openAnalyticFrontier
  ; a1a2a3FiniteInfluenceStatus = Round7.ownedReducerAvailable
  ; scalarGeometricSummationStatus = Round7.physicalInputsConditional
  ; p11PrefixTailReductionStatus = Round7.ownedReducerAvailable
  ; p11PhysicalPrefixTailStatus = Round7.openAnalyticFrontier
  ; stepVLogAnimalMarginStatus = Round7.ownedReducerAvailable
  ; stepVPhysicalLogExpStatus = Round7.physicalInputsConditional
  ; recentInfluenceManuscriptStatus = Round7.externalAuditGate
  ; boundary =
      "Round eight proves ratio-to-monotone coefficient transport, alternating-bracket-to-first-omitted-tail transport, canonical extraction of P06 skeleton/decoration/animal constants, finite A1/A2/A3 influence assembly, P11 prefix/tail minimum recombination, logarithmic animal-margin transport, and finite-to-uniform influence composition from an explicit geometric kernel. Physical coefficient brackets, P06 model leaves, P11 prefix/tail estimates, log/exp laws and scalar summation remain explicit inputs."
  }

submissionRound8LedgerLevel : ProofLevel
submissionRound8LedgerLevel = machineChecked
