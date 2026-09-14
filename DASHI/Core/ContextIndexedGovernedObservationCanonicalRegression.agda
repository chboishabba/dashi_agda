module DASHI.Core.ContextIndexedGovernedObservationCanonicalRegression where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ContextIndexedGovernedObservationExact as Governed

activeCollisionProjectsToCanonicalNonDescent :
  ∀ {State Context Query Surface : Set}
    {observe : State → Surface}
    {family : Governed.ContextIndexedGovernedFamily State Context Query Surface observe}
    {context : Context}
    {query : Query} →
  (defect : Governed.ActiveGovernedCollision family context query) →
  Descent.ConsumerNonDescentWitness
    observe
    (Governed.consume family (Governed.axis defect))
activeCollisionProjectsToCanonicalNonDescent =
  Governed.activeGovernedCollisionAsCanonicalNonDescent
