module DASHI.Core.DeliberativeCyberneticLoopBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Core.HistoryIndexedProofExperimentActionLoopExact as Loop
import DASHI.Core.DeliberativeMoveBidiCrossPollination2026Exact as Delib

------------------------------------------------------------------------
-- RECIPROCAL WELD: THINK/LOOK/TEST/ACT <-> ASK/LISTEN/DELIBERATE
--
-- Existing loop constructors remain intact.  This owner supplies an extension
-- carrier so older controllers embed definitionally while new situated moves
-- can target residuals unavailable to passive observation or internal proof.
------------------------------------------------------------------------

data ExtendedMoveKind : Set where
  baseMove : Loop.EpistemicMoveKind → ExtendedMoveKind
  askMove : ExtendedMoveKind
  listenMove : ExtendedMoveKind
  deliberateMove : ExtendedMoveKind

record ExtendedCandidateMove (fibre : Loop.LiveResidualFibre) : Set₁ where
  constructor extended-candidate-move
  field
    kind : ExtendedMoveKind
    residualExact : Loop.residualReference fibre ≡ Loop.residualReference fibre
    candidateReference : String
    expectedConsumerGainReference : String
    authorityReference : String
open ExtendedCandidateMove public

embedBaseCandidate :
  ∀ {fibre} → Loop.CandidateMove fibre → ExtendedCandidateMove fibre
embedBaseCandidate candidate =
  extended-candidate-move
    (baseMove (Loop.kind candidate))
    refl
    (Loop.candidateReference candidate)
    (Loop.expectedConsumerGainReference candidate)
    "inherits authority/evidence discipline from the embedded base candidate"

deliberativeCandidate :
  ∀ {fibre} →
  Delib.DeliberativeMove →
  ExtendedCandidateMove fibre
deliberativeCandidate move =
  extended-candidate-move
    (translate (Delib.moveKind move))
    refl
    (Delib.residualReference move)
    (Delib.expectedInformationGainReference move)
    (Delib.authorityReceiptReference move)
  where
    translate : Delib.EpistemicMoveKind → ExtendedMoveKind
    translate Delib.thinkMove = baseMove Loop.thinkMove
    translate Delib.lookMove = baseMove Loop.lookMove
    translate Delib.testMove = baseMove Loop.testMove
    translate Delib.askMove = askMove
    translate Delib.listenMove = listenMove
    translate Delib.deliberateMove = deliberateMove
    translate Delib.actMove = baseMove Loop.actMove

record ExtendedNextControlDecision (fibre : Loop.LiveResidualFibre) : Set₁ where
  constructor extended-next-control-decision
  field
    next : ExtendedCandidateMove fibre
    decisionReference : String
open ExtendedNextControlDecision public

data DeliberationAutomaticallyAuthorisesAct : Set where

deliberationDoesNotAutomaticallyAuthoriseAct :
  DeliberationAutomaticallyAuthorisesAct → ⊥
deliberationDoesNotAutomaticallyAuthoriseAct ()

record DeliberativeCyberneticBoundary : Set where
  constructor deliberative-cybernetic-boundary
  field
    oldMovesEmbed : Bool
    askIsFirstClass : Bool
    listenIsFirstClass : Bool
    deliberateIsFirstClass : Bool
    actionAuthorityStillSeparate : Bool

canonicalDeliberativeCyberneticBoundary : DeliberativeCyberneticBoundary
canonicalDeliberativeCyberneticBoundary =
  deliberative-cybernetic-boundary true true true true true
