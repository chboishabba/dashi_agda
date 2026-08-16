module DASHI.Governance.ContestabilityAccessCostExact where

------------------------------------------------------------------------
-- CROSS-POLLINATION CALIBRATION
--
-- Internal producer pollen:
--   * PR #549 / ObservationAcquisitionCostExact separates the informational
--     value of an observation from the cost of acquiring it;
--   * AsymmetricLegibilityContestabilityExact separates formal explanation,
--     appeal and correction witnesses from the information asymmetry itself.
--
-- Governance consequence: a formally available contestability path is not
-- definitionally an affordable/usable path.  This file gives exact finite Nat
-- accounting only.  It does not assign real-world costs, legal thresholds, or
-- a normative verdict to any named institution.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Governance.AsymmetricLegibilityContestabilityExact as Legibility

record ContestabilityCost : Set where
  constructor contestabilityCost
  field
    explanationCost : Nat
    appealCost : Nat
    correctionCost : Nat

open ContestabilityCost public

totalContestabilityCost : ContestabilityCost → Nat
totalContestabilityCost cost =
  explanationCost cost + appealCost cost + correctionCost cost

record SubjectAccessBudget : Set where
  constructor subjectAccessBudget
  field
    budget : Nat

open SubjectAccessBudget public

record AffordableContestability
  (cost : ContestabilityCost)
  (access : SubjectAccessBudget) : Set where
  constructor affordableContestability
  field
    withinBudget : totalContestabilityCost cost ≤ budget access

open AffordableContestability public

------------------------------------------------------------------------
-- Formal availability is a separate witness over the existing contestability
-- interface.
------------------------------------------------------------------------

record FormallyAvailableContestability
  {L : Legibility.LegibilityChannel}
  (C : Legibility.ContestabilityInterface L)
  (subject : Legibility.Subject L) : Set₁ where
  constructor formallyAvailableContestability
  field
    explanation : Legibility.Explanation C subject
    appeal : Legibility.Appeal C subject
    correction : Legibility.Correction C subject

------------------------------------------------------------------------
-- Finite countermodel: all three channels exist, but the declared access cost
-- exceeds the declared subject budget.
------------------------------------------------------------------------

finiteContestabilityInterface :
  Legibility.ContestabilityInterface Legibility.finiteLegibilityChannel
finiteContestabilityInterface =
  Legibility.contestabilityInterface
    (λ subject → ⊤)
    (λ subject → ⊤)
    (λ subject → ⊤)

finiteFormalAvailability :
  FormallyAvailableContestability
    finiteContestabilityInterface
    Legibility.case0
finiteFormalAvailability =
  formallyAvailableContestability tt tt tt

finiteCost : ContestabilityCost
finiteCost = contestabilityCost 2 2 1

finiteBudget : SubjectAccessBudget
finiteBudget = subjectAccessBudget 3

finiteTotalCostIsFive : totalContestabilityCost finiteCost ≡ 5
finiteTotalCostIsFive = refl

fiveNotLeThree : 5 ≤ 3 → ⊥
fiveNotLeThree ()

formalAvailabilityDoesNotEstablishAffordability :
  AffordableContestability finiteCost finiteBudget → ⊥
formalAvailabilityDoesNotEstablishAffordability affordable =
  fiveNotLeThree (withinBudget affordable)

------------------------------------------------------------------------
-- Boundary: accessibility may depend on money, time, cognition, language,
-- representation, procedure, assistance, etc.; Nat is only an abstract exact
-- cost carrier here.
------------------------------------------------------------------------

record ContestabilityAccessCostBoundary : Set where
  constructor contestabilityAccessCostBoundary
  field
    formalAvailabilityImpliesAffordability : Bool
    accessCostMustBeRepresentedSeparately : Bool
    finiteNatCostIsEmpiricalRealWorldCost : Bool
    inaccessiblePathAutomaticallyIllegal : Bool
    subjectResourceConstraintsMayMatter : Bool

canonicalContestabilityAccessCostBoundary : ContestabilityAccessCostBoundary
canonicalContestabilityAccessCostBoundary =
  contestabilityAccessCostBoundary false true false false true
