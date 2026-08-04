module DASHI.Physics.YangMills.YangMillsSubmissionRound8Ledger where

open import Agda.Builtin.String using (String)

import DASHI.Physics.YangMills.YangMillsSubmissionRound7Ledger as Round7
open import DASHI.Physics.YangMills.CompactLieProofLevel

record SubmissionRound8Ledger : Set where
  field
    bishopConcreteHalfBallStatus : Round7.SubmissionGroupStatus
    bishopConcreteRatioBoundsStatus : Round7.SubmissionGroupStatus
    bishopSetoidRatioMonotonicityStatus : Round7.SubmissionGroupStatus
    bishopSetoidFirstOmittedReductionStatus : Round7.SubmissionGroupStatus
    bishopConcreteCoefficientRecurrenceStatus : Round7.SubmissionGroupStatus
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
  { bishopConcreteHalfBallStatus = Round7.ownedReducerAvailable
  ; bishopConcreteRatioBoundsStatus = Round7.ownedReducerAvailable
  ; bishopSetoidRatioMonotonicityStatus = Round7.ownedReducerAvailable
  ; bishopSetoidFirstOmittedReductionStatus = Round7.ownedReducerAvailable
  ; bishopConcreteCoefficientRecurrenceStatus = Round7.physicalInputsConditional
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
      "Round eight instantiates the half-ball square and exact 1/24, 1/8 ratio bounds on Bishop reals; proves setoid ratio-to-monotone and alternating-bracket-to-first-omitted transports; extracts canonical P06 skeleton/decoration/animal constants; assembles finite A1/A2/A3 influence; recombines P11 prefix/tail minima; transports the logarithmic animal margin; and composes finite activity bounds with an explicit scalar geometric kernel. Concrete sine/cosine coefficient recurrences and partial-sum brackets, the P06 physical model leaf, P11 prefix/tail estimates, log/exp laws and scalar summation remain explicit inputs."
  }

submissionRound8LedgerLevel : ProofLevel
submissionRound8LedgerLevel = machineChecked
