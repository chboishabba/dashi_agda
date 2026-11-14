module DASHI.Biology.QuailEggIBSTransferLadderRegression where

open import DASHI.Core.Prelude using (⊥)
open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
import DASHI.Biology.QuailEggIBSTransferLadderExact as Q

ladderRegression : Q.QuailEggIBSTransferLadder
ladderRegression = Q.canonicalQuailEggIBSTransferLadder

terminalRemainsOpenRegression :
  Q.HumanIBSQuailTerminalReceipt.terminalClosed Q.canonicalHumanIBSQuailTerminalReceipt ≡ false
terminalRemainsOpenRegression = refl

terminalStageStatusRegression :
  Q.TransferStageReceipt.status Q.humanIBSQuailStageReceipt ≡ Q.openTerminal
terminalStageStatusRegression = refl

ladderTerminalStatusRegression :
  Q.TransferStageReceipt.status
    (Q.QuailEggIBSTransferLadder.ibsQuailStage Q.canonicalQuailEggIBSTransferLadder)
    ≡ Q.openTerminal
ladderTerminalStatusRegression = refl

adjacentEvidenceDoesNotCloseTerminal : Q.AdjacentEvidenceClosesHumanIBSPermission → ⊥
adjacentEvidenceDoesNotCloseTerminal = Q.adjacentEvidenceDoesNotCloseHumanIBS

boundaryOpenRegression :
  Q.QuailEggIBSTransferLadderBoundary.quailSpecificHumanIBSTerminalClosed
    Q.canonicalQuailEggIBSTransferLadderBoundary ≡ false
boundaryOpenRegression = refl
