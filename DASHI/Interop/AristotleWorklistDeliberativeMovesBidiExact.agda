module DASHI.Interop.AristotleWorklistDeliberativeMovesBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.DeliberativeCyberneticLoopBidiExact as Delib
import DASHI.Core.AskListenObservationProducerBidiExact as AskListen

-- Archive donors: RequestProject.Worklist / Reports / repair staging.
data AristotleWorkState : Set where
  coverageMissing
  interpretationAmbiguous
  repairCandidate
  reviewedRepair
  executableRepair : AristotleWorkState

data AristotleDeliberativeRoute : Set where
  lookRoute askListenRoute reformulateRoute testRoute actRoute : AristotleDeliberativeRoute

routeFor : AristotleWorkState → AristotleDeliberativeRoute
routeFor coverageMissing = lookRoute
routeFor interpretationAmbiguous = askListenRoute
routeFor repairCandidate = testRoute
routeFor reviewedRepair = reformulateRoute
routeFor executableRepair = actRoute

-- Worklist/report membership is analysis state, not action authority.
data WorklistMembershipImpliesExecutionAuthority : Set where
worklistMembershipDoesNotCreateExecutionAuthority :
  WorklistMembershipImpliesExecutionAuthority → ⊥
worklistMembershipDoesNotCreateExecutionAuthority ()

record AristotleWorklistDeliberativeBoundary : Set where
  constructor aristotle-worklist-deliberative-boundary
  field
    worklistStateMayRouteDeliberativeMove : Bool
    reportableEqualsRepairable : Bool
    repairableEqualsReviewed : Bool
    reviewedEqualsExecutable : Bool
    worklistMembershipCreatesActionAuthority : Bool

canonicalAristotleWorklistDeliberativeBoundary :
  AristotleWorklistDeliberativeBoundary
canonicalAristotleWorklistDeliberativeBoundary =
  aristotle-worklist-deliberative-boundary true false false false false

worklistDeliberativeStatement : String
worklistDeliberativeStatement =
  "Aristotle-style worklist/report states may route the existing look/ask-listen/reformulate/test/act controller, but reportable, repairable, reviewed and executable remain distinct stages. Worklist membership can schedule investigation; it cannot manufacture action or edit authority."
