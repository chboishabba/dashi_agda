module DASHI.Physics.YangMills.BalabanClayGate4SevenGroupRound6AdvanceReceipt where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayGate4SevenGroupRound6AdvanceLedger as Ledger

record SevenGroupRound6AdvanceReceipt : Set where
  constructor sevenGroupRound6AdvanceReceipt
  field
    repositoryHead : String
    previousSevenGroupLedgerChecked : Bool
    physicalClosureRound6LedgerChecked : Bool
    physicalClosureRound6ReceiptChecked : Bool
    physicalClosureRound6ValidationChecked : Bool
    physicalClosureRound6ProducerChecked : Bool
    round6ExactCutsetChecked : Bool
    round6FocusedCheckerChecked : Bool
    round6WorkflowChecked : Bool
    round6PostulateFree : Bool

open SevenGroupRound6AdvanceReceipt public

record AuthoritativeSevenGroupRound6Evidence
    (receipt : SevenGroupRound6AdvanceReceipt) : Set₁ where
  field
    previousSevenGroupLedgerTypechecks : Set
    physicalClosureRound6LedgerTypechecks : Set
    physicalClosureRound6ReceiptTypechecks : Set
    physicalClosureRound6ValidationTypechecks : Set
    physicalClosureRound6ProducerTypechecks : Set
    round6ExactCutsetTypechecks : Set
    round6FocusedCheckerRuns : Set
    round6WorkflowRuns : Set
    round6HasNoPostulatesOrUnsolvedMetas : Set

open AuthoritativeSevenGroupRound6Evidence public

sevenGroupRound6AdvanceLedgerLevel = Ledger.sevenGroupRound6AdvanceLedgerLevel

sevenGroupRound6TypecheckLevel : ProofLevel
sevenGroupRound6TypecheckLevel = conditional

sevenGroupRound6PostulateFreeLevel : ProofLevel
sevenGroupRound6PostulateFreeLevel = conditional
