module DASHI.Core.ConsumerObserverJoinResidualExact where

------------------------------------------------------------------------
-- CONSUMER OBSERVER JOINS + HOT/COLD EXACT REOPENING
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Core.ObserverRefinementLatticeExact as Lattice
import DASHI.Core.ReopenableConsumerInterventionKernelExact as Kernel

record Observer (State : Set) : Set₁ where
  constructor observer
  field
    Value : Set
    observe : State → Value

open Observer public

joinObserver :
  ∀ {State} → Observer State → Observer State → Observer State
joinObserver left right =
  observer
    (Value left × Value right)
    (Lattice.pairObserver (observe left) (observe right))

record Refines
    {State : Set}
    (fine coarse : Observer State) : Set₁ where
  constructor refines
  field
    collisionMapsBack :
      ∀ {left right} →
      observe fine left ≡ observe fine right →
      observe coarse left ≡ observe coarse right

open Refines public

joinRefinesLeft :
  ∀ {State} (left right : Observer State) →
  Refines (joinObserver left right) left
joinRefinesLeft left right =
  refines
    (λ {left = x} {right = y} same →
      Lattice.pairRefinesLeft (observe left) (observe right) x y same)

joinRefinesRight :
  ∀ {State} (left right : Observer State) →
  Refines (joinObserver left right) right
joinRefinesRight left right =
  refines
    (λ {left = x} {right = y} same →
      Lattice.pairRefinesRight (observe left) (observe right) x y same)

record RecoverableHotCold
    (Fine Hot Residual : Set) : Set₁ where
  constructor recoverableHotCold
  field
    hot : Fine → Hot
    residual : Fine → Residual
    reopen : Hot → Residual → Fine
    reopenExact :
      ∀ fine → reopen (hot fine) (residual fine) ≡ fine

open RecoverableHotCold public

sameHotAndResidualSameFine :
  ∀ {Fine Hot Residual}
    (recoverable : RecoverableHotCold Fine Hot Residual)
    {left right : Fine} →
  hot recoverable left ≡ hot recoverable right →
  residual recoverable left ≡ residual recoverable right →
  left ≡ right
sameHotAndResidualSameFine recoverable {left} {right} sameHot sameResidual =
  trans
    (sym (reopenExact recoverable left))
    (trans sameReopened (reopenExact recoverable right))
  where
    sameReopened :
      reopen recoverable (hot recoverable left) (residual recoverable left)
      ≡ reopen recoverable (hot recoverable right) (residual recoverable right)
    sameReopened rewrite sameHot | sameResidual = refl

record ConsumerSufficientHotState
    {Fine Hot Output : Set}
    (hot : Fine → Hot)
    (consume : Fine → Output) : Set₁ where
  constructor consumerSufficientHotState
  field
    descent : Kernel.ConsumerDescent hot consume

open ConsumerSufficientHotState public

record MinimalConsumerSufficientHotState
    {Fine Hot Output : Set}
    (hot : Fine → Hot)
    (consume : Fine → Output) : Set₂ where
  constructor minimalConsumerSufficientHotState
  field
    sufficient : ConsumerSufficientHotState hot consume
    coarsest :
      ∀ {Other : Set}
        (other : Fine → Other) →
      Kernel.ConsumerDescent other consume →
      Σ (Other → Hot)
        (λ factor → ∀ fine → hot fine ≡ factor (other fine))

open MinimalConsumerSufficientHotState public

record ReopenableMinimalConsumerState
    (Fine Hot Residual Output : Set)
    (consume : Fine → Output) : Set₂ where
  constructor reopenableMinimalConsumerState
  field
    recoverable : RecoverableHotCold Fine Hot Residual
    minimalHot :
      MinimalConsumerSufficientHotState (hot recoverable) consume

open ReopenableMinimalConsumerState public
