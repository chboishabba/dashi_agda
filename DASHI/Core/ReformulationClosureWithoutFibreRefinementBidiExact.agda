module DASHI.Core.ReformulationClosureWithoutFibreRefinementBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.BidiResidualApproximationExact as Bidi
import DASHI.Core.QueryCompatibleFibreConsumerClosureBidiExact as Query
import DASHI.Core.DeliberativeCyberneticLoopBidiExact as Delib

------------------------------------------------------------------------
-- REFORMULATION CAN CLOSE A QUESTION WITHOUT NARROWING THE HIDDEN FIBRE
--
-- This is the Agda return of the checked deliberative Lean weld. Closure is
-- relative to the current question/consumer. A reformulation may change the
-- question so that the answer is constant on exactly the same hidden fibre.
------------------------------------------------------------------------

data Hidden : Set where leftWorld rightWorld : Hidden

data Question : Set where oldQuestion reformulatedQuestion : Question

data Answer : Set where leftAnswer rightAnswer commonAnswer : Answer

liveFibre : Bidi.ResidualFibre Hidden
liveFibre leftWorld = ⊤
liveFibre rightWorld = ⊤

answer : Question → Hidden → Answer
answer oldQuestion leftWorld = leftAnswer
answer oldQuestion rightWorld = rightAnswer
answer reformulatedQuestion leftWorld = commonAnswer
answer reformulatedQuestion rightWorld = commonAnswer

QuestionClosed : Question → Set
QuestionClosed question = Bidi.PointIdentifies liveFibre (answer question)

oldQuestionNotClosed : QuestionClosed oldQuestion → ⊥
oldQuestionNotClosed closed = leftNotRight (closed leftWorld rightWorld tt tt)
  where
    leftNotRight : leftAnswer ≡ rightAnswer → ⊥
    leftNotRight ()

reformulatedQuestionClosed : QuestionClosed reformulatedQuestion
reformulatedQuestionClosed leftWorld leftWorld left right = refl
reformulatedQuestionClosed leftWorld rightWorld left right = refl
reformulatedQuestionClosed rightWorld leftWorld left right = refl
reformulatedQuestionClosed rightWorld rightWorld left right = refl

fibreBefore : Bidi.ResidualFibre Hidden
fibreBefore = liveFibre

fibreAfter : Bidi.ResidualFibre Hidden
fibreAfter = liveFibre

reformulationLeavesFibreUntouched : fibreAfter ≡ fibreBefore
reformulationLeavesFibreUntouched = refl

record ReformulationMove : Set where
  constructor reformulation-move
  field
    fromQuestion : Question
    toQuestion : Question
    moveReference : String
    authorityReference : String

open ReformulationMove public

canonicalReformulation : ReformulationMove
canonicalReformulation = reformulation-move
  oldQuestion
  reformulatedQuestion
  "reformulate the consumer question while retaining the same compatible fibre"
  "question reformulation does not itself create action authority"

------------------------------------------------------------------------
-- No-collapse boundaries.
------------------------------------------------------------------------

data ClosureAlwaysRequiresInformationGain : Set where
data ReformulationIdentifiesHiddenState : Set where
data ReformulationAutomaticallyAuthorisesAct : Set where

closureDoesNotAlwaysRequireInformationGain :
  ClosureAlwaysRequiresInformationGain → ⊥
closureDoesNotAlwaysRequireInformationGain ()

reformulationDoesNotIdentifyHiddenState : ReformulationIdentifiesHiddenState → ⊥
reformulationDoesNotIdentifyHiddenState ()

reformulationDoesNotAuthoriseAct : ReformulationAutomaticallyAuthorisesAct → ⊥
reformulationDoesNotAuthoriseAct ()

record ReformulationClosureBoundary : Set where
  constructor reformulation-closure-boundary
  field
    oldQuestionMayBeOpen : Bool
    reformulatedQuestionMayClose : Bool
    hiddenFibreMayRemainDefinitionallySame : Bool
    closureImpliesFibreRefinement : Bool
    closureImpliesPointIdentification : Bool
    reformulationCreatesActionAuthority : Bool

canonicalReformulationClosureBoundary : ReformulationClosureBoundary
canonicalReformulationClosureBoundary =
  reformulation-closure-boundary true true true false false false
