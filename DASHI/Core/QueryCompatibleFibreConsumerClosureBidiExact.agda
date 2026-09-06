module DASHI.Core.QueryCompatibleFibreConsumerClosureBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.BidiResidualApproximationExact as Bidi

------------------------------------------------------------------------
-- QUERY-RELATIVE COMPATIBLE FIBRE / CONSUMER CLOSURE
--
-- Reverse x-pollination from the Lean Integration kernel extraction described
-- in TOE_XPOLLINATION_KERNELS.md.  No Lean theorem is transported into Agda;
-- this is a DASHI reconstruction over the existing residual-fibre machinery.
--
-- Key separation:
--   query + state -> compatible fibre
--   compatible fibre -> consumer closure
--   consumer closure != point identification.
------------------------------------------------------------------------

record QueryCompatibleProblem
    (Query State Hidden Answer : Set) : Set₁ where
  constructor query-compatible-problem
  field
    compatible : Query → State → Hidden → Set
    consumer : Query → Hidden → Answer
    problemReference : String

open QueryCompatibleProblem public

ConsumerClosedAt :
  ∀ {Query State Hidden Answer : Set} →
  QueryCompatibleProblem Query State Hidden Answer →
  Query → State → Set
ConsumerClosedAt problem query state =
  ∀ left right →
  compatible problem query state left →
  compatible problem query state right →
  consumer problem query left ≡ consumer problem query right

PointIdentifiedAt :
  ∀ {Query State Hidden Answer : Set} →
  QueryCompatibleProblem Query State Hidden Answer →
  Query → State → Set
PointIdentifiedAt problem query state =
  ∀ left right →
  compatible problem query state left →
  compatible problem query state right →
  left ≡ right

pointIdentificationClosesConsumer :
  ∀ {Query State Hidden Answer : Set}
    {problem : QueryCompatibleProblem Query State Hidden Answer}
    {query : Query} {state : State} →
  PointIdentifiedAt problem query state →
  ConsumerClosedAt problem query state
pointIdentificationClosesConsumer point left right leftLive rightLive =
  cong (consumer problem _) (point left right leftLive rightLive)

queryResidualFibre :
  ∀ {Query State Hidden Answer : Set} →
  QueryCompatibleProblem Query State Hidden Answer →
  Query → State → Bidi.ResidualFibre Hidden
queryResidualFibre problem query state hidden = compatible problem query state hidden

------------------------------------------------------------------------
-- Exact finite witness: two hidden states remain compatible, while the queried
-- consumer is already constant.  This is the positive partial-identification
-- answer rather than treating a non-singleton fibre as epistemic failure.
------------------------------------------------------------------------

data ToyQuery : Set where targetQuery : ToyQuery
data ToyState : Set where targetState : ToyState
data ToyHidden : Set where leftHidden rightHidden : ToyHidden
data ToyAnswer : Set where sameAnswer : ToyAnswer

toyCompatible : ToyQuery → ToyState → ToyHidden → Set
toyCompatible targetQuery targetState leftHidden = ⊤
toyCompatible targetQuery targetState rightHidden = ⊤

toyConsumer : ToyQuery → ToyHidden → ToyAnswer
toyConsumer targetQuery leftHidden = sameAnswer
toyConsumer targetQuery rightHidden = sameAnswer

toyProblem : QueryCompatibleProblem ToyQuery ToyState ToyHidden ToyAnswer
toyProblem = query-compatible-problem toyCompatible toyConsumer
  "synthetic non-singleton compatible fibre with consumer closure"

toyConsumerClosed : ConsumerClosedAt toyProblem targetQuery targetState
toyConsumerClosed leftHidden leftHidden leftLive rightLive = refl
toyConsumerClosed leftHidden rightHidden leftLive rightLive = refl
toyConsumerClosed rightHidden leftHidden leftLive rightLive = refl
toyConsumerClosed rightHidden rightHidden leftLive rightLive = refl

leftHiddenNotRightHidden : leftHidden ≡ rightHidden → ⊥
leftHiddenNotRightHidden ()

toyNotPointIdentified : PointIdentifiedAt toyProblem targetQuery targetState → ⊥
toyNotPointIdentified point =
  leftHiddenNotRightHidden (point leftHidden rightHidden tt tt)

record QueryCompatibleFibreBoundary : Set where
  constructor query-compatible-fibre-boundary
  field
    queryAndStateJointlyIndexFibre : Bool
    nonSingletonFibreMayCloseConsumer : Bool
    consumerClosureRequiresPointIdentification : Bool

canonicalQueryCompatibleFibreBoundary : QueryCompatibleFibreBoundary
canonicalQueryCompatibleFibreBoundary =
  query-compatible-fibre-boundary true true false
