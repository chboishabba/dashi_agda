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
    fiveChannelAggregationChecked : Bool
    t3FiveChannelInstantiationChecked : Bool
    finiteTangentMatrixChecked : Bool
    finiteMatrixSpectrumDeterminantChecked : Bool
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
    fiveChannelAggregationTypechecks : Set
    t3FiveChannelInstantiationTypechecks : Set
    finiteTangentMatrixTypechecks : Set
    finiteMatrixSpectrumDeterminantTypechecks : Set
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

attachment254FiveChannelAggregationTypecheckLevel : ProofLevel
attachment254FiveChannelAggregationTypecheckLevel = conditional

attachment254T3FiveChannelInstantiationTypecheckLevel : ProofLevel
attachment254T3FiveChannelInstantiationTypecheckLevel = conditional

attachment254FiniteTangentMatrixTypecheckLevel : ProofLevel
attachment254FiniteTangentMatrixTypecheckLevel = conditional

attachment254FiniteMatrixSpectrumDeterminantTypecheckLevel : ProofLevel
attachment254FiniteMatrixSpectrumDeterminantTypecheckLevel = conditional

attachment254ValidationWrapperTypecheckLevel : ProofLevel
attachment254ValidationWrapperTypecheckLevel = conditional

attachment254ProducerWrapperTypecheckLevel : ProofLevel
attachment254ProducerWrapperTypecheckLevel = conditional

attachment254IntegratedPostulateFreeLevel : ProofLevel
attachment254IntegratedPostulateFreeLevel = conditional
