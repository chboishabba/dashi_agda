module DASHI.Reasoning.TrialecticT27PNF369RealizationASTValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.TrialecticT27PNF369RealizationASTExact as AST

boundary : AST.PNF369T27RealizationASTBoundary
boundary = AST.canonicalPNF369T27RealizationASTBoundary

finiteInvariantSetPaid : AST.finiteInvariantSetEnumerated boundary ≡ true
finiteInvariantSetPaid = refl

keyOpenLemmaStated : AST.sameObjectRealizationExistenceLemmaStated boundary ≡ true
keyOpenLemmaStated = refl

projectionPaid : AST.t18ProjectionInvariantPaid boundary ≡ true
projectionPaid = refl

roundTripsOpen : AST.coordinateRoundTripsPaid boundary ≡ false
roundTripsOpen = refl

c3IntertwinerOpen : AST.c3IntertwinerPaid boundary ≡ false
c3IntertwinerOpen = refl

semanticsOpen : AST.semanticCompatibilityPaid boundary ≡ false
semanticsOpen = refl

physicsOpen : AST.physicalDynamicsCompatibilityPaid boundary ≡ false
physicsOpen = refl

empiricalOpen : AST.empiricalSameObjectAttachmentPaid boundary ≡ false
empiricalOpen = refl

terminalNotClaimed : AST.terminalSameObjectRealizationClaimed boundary ≡ false
terminalNotClaimed = refl

canonicalAst : AST.PNF369T27RealizationAST AST.nativePolicy
canonicalAst = AST.canonicalCandidateAST

canonicalOpenLedger : AST.RealizationObligationLedger AST.nativePolicy
canonicalOpenLedger = AST.canonicalOpenLedger
