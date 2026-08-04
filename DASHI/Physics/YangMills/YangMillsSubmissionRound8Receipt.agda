module DASHI.Physics.YangMills.YangMillsSubmissionRound8Receipt where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Core.Prelude using (_×_)

import DASHI.Physics.YangMills.YangMillsSubmissionRound8SourceAudit as Sources
open import DASHI.Physics.YangMills.CompactLieProofLevel

record SubmissionRound8Receipt : Set where
  field
    bishopRatioReductionLevel : ProofLevel
    bishopTailReductionLevel : ProofLevel
    p06CanonicalConstantLevel : ProofLevel
    a1a2a3FiniteAssemblyLevel : ProofLevel
    p11PrefixTailReductionLevel : ProofLevel
    stepVAnimalMarginLevel : ProofLevel
    geometricInfluenceCompositionLevel : ProofLevel

    remainingPhysicalInputsLevel : ProofLevel
    recentAuditLeadLevel : ProofLevel

    recentAuditLeadsCannotInhabit :
      (Sources.Round8SourceEntry.mayInhabitImportedTheorem
        Sources.recent26020070AuditLead ≡ false)
      ×
      (Sources.Round8SourceEntry.mayInhabitImportedTheorem
        Sources.recent26020072AuditLead ≡ false)

open SubmissionRound8Receipt public

currentSubmissionRound8Receipt : SubmissionRound8Receipt
currentSubmissionRound8Receipt = record
  { bishopRatioReductionLevel = machineChecked
  ; bishopTailReductionLevel = machineChecked
  ; p06CanonicalConstantLevel = machineChecked
  ; a1a2a3FiniteAssemblyLevel = machineChecked
  ; p11PrefixTailReductionLevel = machineChecked
  ; stepVAnimalMarginLevel = machineChecked
  ; geometricInfluenceCompositionLevel = machineChecked
  ; remainingPhysicalInputsLevel = conditional
  ; recentAuditLeadLevel = conjectural
  ; recentAuditLeadsCannotInhabit = Sources.recentAuditLeadsCannotInhabit
  }

submissionRound8ReceiptLevel : ProofLevel
submissionRound8ReceiptLevel = machineChecked
