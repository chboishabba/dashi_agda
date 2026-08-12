module DASHI.Crypto.PublicFactoredObservationTraceInvariantExact where

------------------------------------------------------------------------
-- REPEATED PUBLIC-FACTORED OBSERVATIONS ADD NO HIDDEN-STATE RESOLUTION
--
-- A single public-factored observation cannot split a public fibre.  This file
-- strengthens that to arbitrary finite query traces.  Repeatedly deriving new
-- values from already-public state does not create hidden-state information.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong₂)

record PublicTraceObservation : Set₁ where
  constructor publicTraceObservation
  field
    Hidden Public Query Observation : Set
    project : Hidden → Public
    answer : Public → Query → Observation

open PublicTraceObservation public

observe :
  (system : PublicTraceObservation) →
  Hidden system → Query system → Observation system
observe system hidden query = answer system (project system hidden) query

trace :
  (system : PublicTraceObservation) →
  Hidden system → List (Query system) → List (Observation system)
trace system hidden [] = []
trace system hidden (q ∷ qs) =
  observe system hidden q ∷ trace system hidden qs

samePublicSameTrace :
  ∀ {system : PublicTraceObservation}
    {left right : Hidden system} →
  project system left ≡ project system right →
  ∀ queries →
  trace system left queries ≡ trace system right queries
samePublicSameTrace samePublic [] = refl
samePublicSameTrace {system} samePublic (q ∷ qs) =
  cong₂ _∷_
    (congAnswer samePublic)
    (samePublicSameTrace samePublic qs)
  where
  congAnswer : ∀ {l r} →
    project system l ≡ project system r →
    answer system (project system l) q ≡ answer system (project system r) q
  congAnswer refl = refl

------------------------------------------------------------------------
-- Adaptive query choice may itself depend on the public state and prior public
-- answers.  If the policy is still a function only of already-public data,
-- hidden states in one public fibre remain locked together.
------------------------------------------------------------------------

record TwoRoundPublicPolicy (system : PublicTraceObservation) : Set₁ where
  constructor twoRoundPublicPolicy
  field
    firstQuery : Public system → Query system
    secondQuery : Public system → Observation system → Query system

open TwoRoundPublicPolicy public

record TwoRoundTranscript (system : PublicTraceObservation) : Set where
  constructor twoRoundTranscript
  field
    firstObservation secondObservation : Observation system

open TwoRoundTranscript public

twoRoundRun :
  (system : PublicTraceObservation) →
  TwoRoundPublicPolicy system →
  Hidden system →
  TwoRoundTranscript system
twoRoundRun system policy hidden =
  let public = project system hidden
      q1 = firstQuery policy public
      o1 = observe system hidden q1
      q2 = secondQuery policy public o1
      o2 = observe system hidden q2
  in twoRoundTranscript o1 o2

samePublicSameAdaptiveTwoRoundTranscript :
  ∀ {system : PublicTraceObservation}
    (policy : TwoRoundPublicPolicy system)
    {left right : Hidden system} →
  project system left ≡ project system right →
  twoRoundRun system policy left ≡ twoRoundRun system policy right
samePublicSameAdaptiveTwoRoundTranscript policy refl = refl
