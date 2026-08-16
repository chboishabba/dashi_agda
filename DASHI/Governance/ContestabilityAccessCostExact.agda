module DASHI.Governance.ContestabilityAccessCostExact where

------------------------------------------------------------------------
-- SOURCE / CROSS-POLLINATION CALIBRATION
--
-- Authoring body: Washington State Access to Justice Board.
-- Title: "Washington State Access to Justice Technology Principles".
-- Venue: Washington Law Review 79(1), first page 5 (2004).
-- DOI: no DOI listed in the cited journal record.
--
-- The published principles motivate access vocabulary in which meaningful
-- access includes procedural information and a just process includes
-- timeliness, affordability and transparency.  They do NOT supply the Nat cost
-- model or a binding legal threshold here; those are deliberately separated.
--
-- Internal producer pollen:
--   * PR #549 / ObservationAcquisitionCostExact separates the informational
--     value of an observation from the cost of acquiring it;
--   * AsymmetricLegibilityContestabilityExact separates formal explanation,
--     appeal and correction witnesses from the information asymmetry itself.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Governance.AsymmetricLegibilityContestabilityExact as Legibility
import DASHI.Governance.DevelopmentalInfluenceSourceAtlas as Sources

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

record FormallyAvailableContestability
  {L : Legibility.LegibilityChannel}
  (C : Legibility.ContestabilityInterface L)
  (subject : Legibility.Subject L) : Set₁ where
  constructor formallyAvailableContestability
  field
    explanation : Legibility.Explanation C subject
    appeal : Legibility.Appeal C subject
    correction : Legibility.Correction C subject

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

record ContestabilityAccessCostReceipt : Set where
  constructor contestabilityAccessCostReceipt
  field
    sources : List Sources.ScholarlySource
    boundary : ContestabilityAccessCostBoundary

canonicalContestabilityAccessCostReceipt : ContestabilityAccessCostReceipt
canonicalContestabilityAccessCostReceipt =
  contestabilityAccessCostReceipt
    (Sources.washingtonAccessJusticeTechnologyPrinciples ∷ [])
    canonicalContestabilityAccessCostBoundary
