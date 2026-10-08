module DASHI.Biology.QuailEggIBSTransferLadderRegression where

open import DASHI.Core.Prelude using (⊥)
import DASHI.Biology.QuailEggIBSTransferLadderExact as Q

ladderRegression : Q.QuailEggIBSTransferLadder
ladderRegression = Q.canonicalQuailEggIBSTransferLadder

missingTerminalRegression : Q.HumanIBSQuailTerminalReceipt
missingTerminalRegression = Q.canonicalHumanIBSQuailTerminalReceipt

adjacentEvidenceDoesNotCloseTerminal : Q.AdjacentEvidenceClosesHumanIBSPermission → ⊥
adjacentEvidenceDoesNotCloseTerminal = Q.adjacentEvidenceDoesNotCloseHumanIBS

boundaryRegression : Q.QuailEggIBSTransferLadderBoundary
boundaryRegression = Q.canonicalQuailEggIBSTransferLadderBoundary
