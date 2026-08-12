module DASHI.Crypto.BlueTeamAdversaryObservationExact where

------------------------------------------------------------------------
-- BLUE-TEAM ADVERSARY OBSERVATION MODEL
--
-- Canonical defensive observation surface.  The mathematical question is not
-- whether an observation exists, but whether it factors through state that is
-- already public or instead separates two hidden states in one public fibre.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong)

record BlueTeamAdversarySystem : Set₁ where
  constructor blueTeamAdversarySystem
  field
    Hidden Public Query Observation : Set
    project : Hidden → Public
    observe : Hidden → Query → Observation

open BlueTeamAdversarySystem public

record Sample (system : BlueTeamAdversarySystem) : Set where
  constructor sample
  field
    query : Query system
    result : Observation system

open Sample public

Compatible :
  (system : BlueTeamAdversarySystem) →
  Hidden system → Sample system → Set
Compatible system hidden s =
  observe system hidden (query s) ≡ result s

Consistent :
  (system : BlueTeamAdversarySystem) →
  Hidden system → List (Sample system) → Set
Consistent system hidden [] = hidden ≡ hidden
Consistent system hidden (s ∷ transcript) =
  Compatible system hidden s × Consistent system hidden transcript

honestSample :
  (system : BlueTeamAdversarySystem) →
  Hidden system → Query system → Sample system
honestSample system hidden q = sample q (observe system hidden q)

honestStateSurvives :
  ∀ {system : BlueTeamAdversarySystem}
    (hidden : Hidden system) (q : Query system) →
  Compatible system hidden (honestSample system hidden q)
honestStateSurvives hidden q = refl

------------------------------------------------------------------------
-- Public-factored observations.
------------------------------------------------------------------------

record PublicFactored
    (system : BlueTeamAdversarySystem) : Set₁ where
  constructor publicFactored
  field
    answer : Public system → Query system → Observation system
    factorLaw : ∀ hidden q →
      observe system hidden q ≡ answer (project system hidden) q

open PublicFactored public

samePublicFibreSamePublicFactoredObservation :
  ∀ {system : BlueTeamAdversarySystem}
    (factored : PublicFactored system)
    {left right : Hidden system} →
  project system left ≡ project system right →
  ∀ q → observe system left q ≡ observe system right q
samePublicFibreSamePublicFactoredObservation {system} factored samePublic q =
  let
    leftFactor = factorLaw factored _ q
    rightFactor = factorLaw factored _ q
    middle = cong (λ public → answer factored public q) samePublic
  in
  trans leftFactor (trans middle (sym rightFactor))
  where
  open import Relation.Binary.PropositionalEquality using (sym; trans)

------------------------------------------------------------------------
-- Hidden-dependent split witness.
------------------------------------------------------------------------

record HiddenDependentSplit
    (system : BlueTeamAdversarySystem) : Set where
  constructor hiddenDependentSplit
  field
    left right : Hidden system
    samePublic : project system left ≡ project system right
    distinguishingQuery : Query system
    observationDiffers :
      observe system left distinguishingQuery
      ≡ observe system right distinguishingQuery → ⊥

open HiddenDependentSplit public

publicFactoredCannotSplitSamePublicFibre :
  ∀ {system : BlueTeamAdversarySystem} →
  PublicFactored system → HiddenDependentSplit system → ⊥
publicFactoredCannotSplitSamePublicFibre factored split =
  observationDiffers split
    (samePublicFibreSamePublicFactoredObservation
      factored (samePublic split) (distinguishingQuery split))

------------------------------------------------------------------------
-- Observation provenance: model the coordinates the adversary really sees.
------------------------------------------------------------------------

data ObservationOrigin : Set where
  alreadyPublic
  protocolOutcome
  implementationChannel
  physicalChannel : ObservationOrigin

record ObservationCoordinate : Set₁ where
  constructor observationCoordinate
  field
    Value : Set
    origin : ObservationOrigin

open ObservationCoordinate public
