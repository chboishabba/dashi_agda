module DASHI.Physics.YangMills.BalabanClayGate4Attachment254IntegratedReceipt where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4Attachment254IntegratedLedger as Ledger

record Attachment254IntegratedReceipt : Set where
  constructor attachment254IntegratedReceipt
  field
    repositoryHead : String
    completionLedgerChecked : Bool
    cmp109SelectionChecked : Bool
    weightedL2NormalizationChecked : Bool
    weightedSchurSlackAdapterChecked : Bool
    t3SelfAdjointFormNormChecked : Bool
    validationWrapperChecked : Bool
    producerWrapperChecked : Bool
    integratedTranchePostulateFree : Bool

open Attachment254IntegratedReceipt public

record AuthoritativeAttachment254IntegratedEvidence
    (receipt : Attachment254IntegratedReceipt) : Set₁ where
  field
    completionLedgerTypechecks : Set
    cmp109SelectionTypechecks : Set
    weightedL2NormalizationTypechecks : Set
    weightedSchurSlackAdapterTypechecks : Set
    t3SelfAdjointFormNormTypechecks : Set
    validationWrapperTypechecks : Set
    producerWrapperTypechecks : Set
    integratedTrancheHasNoPostulatesOrUnsolvedMetas : Set

open AuthoritativeAttachment254IntegratedEvidence public

attachment254CompletionLedgerTypecheckLevel : ProofLevel
attachment254CompletionLedgerTypecheckLevel = conditional

attachment254CMP109SelectionTypecheckLevel : ProofLevel
attachment254CMP109SelectionTypecheckLevel = conditional

attachment254WeightedL2NormalizationTypecheckLevel : ProofLevel
attachment254WeightedL2NormalizationTypecheckLevel = conditional

attachment254WeightedSchurSlackAdapterTypecheckLevel : ProofLevel
attachment254WeightedSchurSlackAdapterTypecheckLevel = conditional

attachment254T3SelfAdjointFormNormTypecheckLevel : ProofLevel
attachment254T3SelfAdjointFormNormTypecheckLevel = conditional

attachment254ValidationWrapperTypecheckLevel : ProofLevel
attachment254ValidationWrapperTypecheckLevel = conditional

attachment254ProducerWrapperTypecheckLevel : ProofLevel
attachment254ProducerWrapperTypecheckLevel = conditional

attachment254IntegratedPostulateFreeLevel : ProofLevel
attachment254IntegratedPostulateFreeLevel = conditional
