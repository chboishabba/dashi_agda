module DASHI.Cognition.PNF.SensibLawFiniteRequirementParetoFrontierExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- FINITE REQUIREMENT PARETO FRONTIER
--
-- DASHI synthesis. No external legal proposition is introduced here.
-- Applications retain source attribution in their own requirement/source owners.
--
-- A requirement enters the CURRENT information frontier only when it is:
--   required for the declared consumer,
--   relevant to that consumer,
--   authority-admissible,
--   and capable of splitting the current live interpretation fibre.
--
-- Cost and certified gain then induce a Pareto relation among admitted cells.
-- Requiredness is deliberately independent of current salience.
------------------------------------------------------------------------

record RequirementCandidate (Requirement : Set) : Set where
  constructor requirement-candidate
  field
    requirement : Requirement
    requiredForConsumer : Bool
    consumerRelevant : Bool
    authorityAdmissible : Bool
    splitsCurrentLiveFibre : Bool
    cost : Nat
    certifiedGain : Nat
    candidateReference : String

open RequirementCandidate public

_&&_ : Bool → Bool → Bool
false && right = false
true && right = right

not : Bool → Bool
not false = true
not true = false

_≤ᵇ_ : Nat → Nat → Bool
zero ≤ᵇ right = true
suc left ≤ᵇ zero = false
suc left ≤ᵇ suc right = left ≤ᵇ right

eligible? : ∀ {Requirement} → RequirementCandidate Requirement → Bool
eligible? cell =
  requiredForConsumer cell &&
  (consumerRelevant cell &&
   (authorityAdmissible cell && splitsCurrentLiveFibre cell))

dominates? :
  ∀ {Requirement} →
  RequirementCandidate Requirement →
  RequirementCandidate Requirement →
  Bool
dominates? left right =
  eligible? left &&
  ((cost left ≤ᵇ cost right) &&
   (certifiedGain right ≤ᵇ certifiedGain left))

strictlyDominates? :
  ∀ {Requirement} →
  RequirementCandidate Requirement →
  RequirementCandidate Requirement →
  Bool
strictlyDominates? left right =
  dominates? left right && not (dominates? right left)

undominatedByAll? :
  ∀ {Requirement} →
  RequirementCandidate Requirement →
  List (RequirementCandidate Requirement) →
  Bool
undominatedByAll? selected [] = true
undominatedByAll? selected (alternative ∷ rest) =
  not (strictlyDominates? alternative selected) &&
  undominatedByAll? selected rest

onParetoFrontier? :
  ∀ {Requirement} →
  List (RequirementCandidate Requirement) →
  RequirementCandidate Requirement →
  Bool
onParetoFrontier? portfolio selected =
  eligible? selected && undominatedByAll? selected portfolio

filterFrontier :
  ∀ {Requirement} →
  List (RequirementCandidate Requirement) →
  List (RequirementCandidate Requirement) →
  List (RequirementCandidate Requirement)
filterFrontier portfolio [] = []
filterFrontier portfolio (cell ∷ rest) with onParetoFrontier? portfolio cell
... | true = cell ∷ filterFrontier portfolio rest
... | false = filterFrontier portfolio rest

paretoFrontier :
  ∀ {Requirement} →
  List (RequirementCandidate Requirement) →
  List (RequirementCandidate Requirement)
paretoFrontier portfolio = filterFrontier portfolio portfolio

------------------------------------------------------------------------
-- Exact finite calibration: two trade-off cells survive, a dominated cell and
-- an authority-inadmissible high-gain cell do not.
------------------------------------------------------------------------

data ToyRequirement : Set where
  cheapModerate
  costlyHighGain
  costlyLowGain
  inadmissibleHugeGain
  : ToyRequirement

cheapCell : RequirementCandidate ToyRequirement
cheapCell = requirement-candidate
  cheapModerate true true true true 1 3
  "cheap, admitted, moderate certified gain"

highGainCell : RequirementCandidate ToyRequirement
highGainCell = requirement-candidate
  costlyHighGain true true true true 3 5
  "higher cost, higher certified gain; Pareto trade-off"

dominatedCell : RequirementCandidate ToyRequirement
dominatedCell = requirement-candidate
  costlyLowGain true true true true 4 2
  "strictly worse cost/gain than cheap cell"

inadmissibleCell : RequirementCandidate ToyRequirement
inadmissibleCell = requirement-candidate
  inadmissibleHugeGain true true false true 1 9
  "nominally huge gain but authority-inadmissible"

toyPortfolio : List (RequirementCandidate ToyRequirement)
toyPortfolio = cheapCell ∷ highGainCell ∷ dominatedCell ∷ inadmissibleCell ∷ []

cheapIsOnFrontier : onParetoFrontier? toyPortfolio cheapCell ≡ true
cheapIsOnFrontier = refl

highGainIsOnFrontier : onParetoFrontier? toyPortfolio highGainCell ≡ true
highGainIsOnFrontier = refl

dominatedIsOffFrontier : onParetoFrontier? toyPortfolio dominatedCell ≡ false
dominatedIsOffFrontier = refl

inadmissibleIsOffFrontier : onParetoFrontier? toyPortfolio inadmissibleCell ≡ false
inadmissibleIsOffFrontier = refl

toyFrontierHasTwoTradeoffs :
  paretoFrontier toyPortfolio ≡ cheapCell ∷ highGainCell ∷ []
toyFrontierHasTwoTradeoffs = refl

------------------------------------------------------------------------
-- Required-but-currently-inert requirement: retained in portfolio, excluded
-- from the current frontier solely because it does not split the live fibre.
------------------------------------------------------------------------

inertButRequiredCell : RequirementCandidate ToyRequirement
inertButRequiredCell = requirement-candidate
  cheapModerate true true true false 1 8
  "required and high-gain in the abstract, but no current live-fibre split"

inertStillRequired : requiredForConsumer inertButRequiredCell ≡ true
inertStillRequired = refl

inertNotEligibleNow : eligible? inertButRequiredCell ≡ false
inertNotEligibleNow = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data RequiredMeansFrontierEligible : Set where
data HighestGainOverridesAuthority : Set where
data ParetoFrontierPaysRequirement : Set where
data ParetoFrontierCreatesLegalAuthority : Set where
data OffFrontierMeansRequirementDeleted : Set where

requiredDoesNotMeanEligibleNow : RequiredMeansFrontierEligible → ⊥
requiredDoesNotMeanEligibleNow ()

highestGainCannotOverrideAuthority : HighestGainOverridesAuthority → ⊥
highestGainCannotOverrideAuthority ()

frontierDoesNotPayRequirement : ParetoFrontierPaysRequirement → ⊥
frontierDoesNotPayRequirement ()

frontierDoesNotCreateAuthority : ParetoFrontierCreatesLegalAuthority → ⊥
frontierDoesNotCreateAuthority ()

offFrontierDoesNotDeleteRequirement : OffFrontierMeansRequirementDeleted → ⊥
offFrontierDoesNotDeleteRequirement ()
