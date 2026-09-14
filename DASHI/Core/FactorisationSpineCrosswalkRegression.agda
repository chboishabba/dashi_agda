module DASHI.Core.FactorisationSpineCrosswalkRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Core.QueryFactorisationSufficiency as Query
import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Core.ObserverFactorizedRefinementExact as Factorized
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.CoarseFineFabricCalculusExact as Coarse
import DASHI.Core.FactorisationSpineCrosswalkExact as Crosswalk

data State : Set where left right : State
data Surface : Set where same : Surface
data Outcome : Set where yes : Outcome
\data QueryKey : Set where q : QueryKey

project : State → Surface
project _ = same

consumer : State → Outcome
consumer _ = yes

questions : Query.InquiryQuestionFamily State QueryKey
questions = Query.inquiryQuestionFamily (λ _ → Outcome) (λ _ → consumer)

queryFactor : Query.FactorsThrough questions project q
queryFactor = Query.factorsThrough (λ _ → yes) (λ _ → refl)

nonFactorStyle : NonFactor.FactorsThrough project consumer
nonFactorStyle = Crosswalk.queryFactorsToNonFactor queryFactor

factorizedStyle : Factorized.FactorizedRefinement consumer project
factorizedStyle = Crosswalk.nonFactorToFactorized nonFactorStyle

queryRoundTrip : Query.FactorsThrough questions project q
queryRoundTrip = Crosswalk.nonFactorToQuery questions q nonFactorStyle

record HiddenState : Set where
  constructor hiddenState
  field visible hidden : Bool
open HiddenState public

hiddenProject : HiddenState → Bool
hiddenProject = visible

hiddenConsumer : HiddenState → Bool
hiddenConsumer = hidden

trueNotFalse : true ≡ false → ⊥
trueNotFalse ()

collision : Coarse.ProjectionCollision hiddenProject hiddenConsumer
collision = Coarse.projectionCollision
  (hiddenState false true)
  (hiddenState false false)
  refl
  trueNotFalse

nonFactorWitness : NonFactor.NonFactorabilityWitness hiddenProject hiddenConsumer
nonFactorWitness = Crosswalk.projectionCollisionToNonFactorability collision

descentWitness : Descent.ConsumerNonDescentWitness hiddenProject hiddenConsumer
descentWitness = Crosswalk.projectionCollisionToNonDescent collision

backToCollision : Coarse.ProjectionCollision hiddenProject hiddenConsumer
backToCollision = Crosswalk.nonDescentToProjectionCollision descentWitness

historicalOwnersDeleted : Bool
historicalOwnersDeleted =
  Crosswalk.FactorisationCrosswalkBoundary.historicalOwnersMustBeDeleted
    Crosswalk.canonicalFactorisationCrosswalkBoundary

historicalOwnersDeletedIsFalse : historicalOwnersDeleted ≡ false
historicalOwnersDeletedIsFalse = refl
