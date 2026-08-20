module DASHI.Core.ConsumerObserverJoinResidualExact where

------------------------------------------------------------------------
-- CONSUMER OBSERVER JOINS + HOT/COLD EXACT REOPENING
--
-- Incoming PR #588 independently exposes observer pairing as an information
-- join.  This module lands only the theorem consequences needed by the current
-- reopenable-consumer stack, without importing that unrelated branch: joined
-- views refine each component; a hot consumer-sufficient projection may retain
-- a cold residual for exact reopening; and minimality is stated as an explicit
-- universal property rather than inferred from compression size.
--
-- Literature calibration:
-- David Blackwell, "Equivalent Comparisons of Experiments", Annals of
-- Mathematical Statistics 24(2), 1953. DOI: 10.1214/aoms/1177729032.
-- The universal-property formulation below is an internal deterministic DASHI
-- construction, not a theorem imported from Blackwell.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Core.ReopenableConsumerInterventionKernelExact as Kernel

------------------------------------------------------------------------
-- Typed observer and binary join.
------------------------------------------------------------------------

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
    (λ state → observe left state , observe right state)

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
  refines (λ same → cong proj₁ same)

joinRefinesRight :
  ∀ {State} (left right : Observer State) →
  Refines (joinObserver left right) right
joinRefinesRight left right =
  refines (λ same → cong proj₂ same)

------------------------------------------------------------------------
-- Exact hot/cold decomposition.
------------------------------------------------------------------------

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
sameHotAndResidualSameFine recoverable sameHot sameResidual =
  trans
    (sym (reopenExact recoverable _))
    (trans
      (cong
        (λ pair → reopen recoverable (proj₁ pair) (proj₂ pair))
        (cong₂ _,_ sameHot sameResidual))
      (reopenExact recoverable _))
  where
    cong₂ :
      ∀ {A B C : Set}
        (f : A → B → C)
        {a a' : A} {b b' : B} →
      a ≡ a' → b ≡ b' → f a b ≡ f a' b'
    cong₂ f refl refl = refl

------------------------------------------------------------------------
-- Consumer sufficiency is ordinary descent through the hot projection.
------------------------------------------------------------------------

record ConsumerSufficientHotState
    {Fine Hot Output : Set}
    (hot : Fine → Hot)
    (consume : Fine → Output) : Set₁ where
  constructor consumerSufficientHotState
  field
    descent : Kernel.ConsumerDescent hot consume

open ConsumerSufficientHotState public

------------------------------------------------------------------------
-- Minimality is not guessed from bit-count or dimension.  It is the universal
-- property: every other consumer-sufficient projection factors the proposed
-- hot state.  This is intentionally a certificate/obligation, not an automatic
-- theorem for every projection.
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- A performant representation may therefore use
--
--   hot consumer-sufficient state + cold exact residual.
--
-- The hot projection is not claimed to reconstruct the fine state by itself.
------------------------------------------------------------------------

record ReopenableMinimalConsumerState
    (Fine Hot Residual Output : Set)
    (consume : Fine → Output) : Set₂ where
  constructor reopenableMinimalConsumerState
  field
    recoverable : RecoverableHotCold Fine Hot Residual
    minimalHot :
      MinimalConsumerSufficientHotState (hot recoverable) consume

open ReopenableMinimalConsumerState public
