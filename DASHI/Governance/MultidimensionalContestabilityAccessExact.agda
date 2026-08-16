module DASHI.Governance.MultidimensionalContestabilityAccessExact where

------------------------------------------------------------------------
-- SOURCE / CROSS-POLLINATION CALIBRATION
--
-- Author/institution: Washington State Access to Justice Board.
-- Title: "Washington State Access to Justice Technology Principles".
-- Venue: Washington Law Review 79(1):5 (2004).
-- DOI: no DOI listed in the cited record.
--
-- The source motivates treating meaningful access as more than formal
-- availability.  The six-coordinate resource geometry below is a DASHI
-- construction.  Coordinates are abstract Nat demands/budgets; they are not
-- empirical dollars, minutes, IQ points, legal thresholds, or disability
-- classifications.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Governance.DevelopmentalInfluenceSourceAtlas as Sources

record AccessResources : Set where
  constructor accessResources
  field
    time : Nat
    money : Nat
    cognitiveLoad : Nat
    languageLoad : Nat
    proceduralLoad : Nat
    assistanceNeed : Nat

open AccessResources public

record ResourceAccessWithin
  (demand budget : AccessResources) : Set where
  constructor resourceAccessWithin
  field
    timeWithin : time demand ≤ time budget
    moneyWithin : money demand ≤ money budget
    cognitiveWithin : cognitiveLoad demand ≤ cognitiveLoad budget
    languageWithin : languageLoad demand ≤ languageLoad budget
    proceduralWithin : proceduralLoad demand ≤ proceduralLoad budget
    assistanceWithin : assistanceNeed demand ≤ assistanceNeed budget

open ResourceAccessWithin public

totalResource : AccessResources → Nat
totalResource r =
  time r
  + money r
  + cognitiveLoad r
  + languageLoad r
  + proceduralLoad r
  + assistanceNeed r

------------------------------------------------------------------------
-- Exact finite countermodel: aggregate slack does not repair a bottleneck.
-- Demand total 5 is below budget total 6, but all demand is concentrated in
-- the time coordinate while only 3 time units are available.
------------------------------------------------------------------------

bottleneckDemand : AccessResources
bottleneckDemand = accessResources 5 0 0 0 0 0

spreadBudget : AccessResources
spreadBudget = accessResources 3 3 0 0 0 0

bottleneckDemandTotalIsFive : totalResource bottleneckDemand ≡ 5
bottleneckDemandTotalIsFive = refl

spreadBudgetTotalIsSix : totalResource spreadBudget ≡ 6
spreadBudgetTotalIsSix = refl

aggregateBudgetLooksSufficient :
  totalResource bottleneckDemand ≤ totalResource spreadBudget
aggregateBudgetLooksSufficient = s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))

fiveNotLeThree : 5 ≤ 3 → ⊥
fiveNotLeThree ()

aggregateSufficiencyDoesNotEstablishCoordinateAccess :
  ResourceAccessWithin bottleneckDemand spreadBudget → ⊥
aggregateSufficiencyDoesNotEstablishCoordinateAccess access =
  fiveNotLeThree (timeWithin access)

------------------------------------------------------------------------
-- Assistance can be modelled as a coordinate rather than being erased into
-- "user effort".  This remains abstract and does not define a legal duty.
------------------------------------------------------------------------

record ContestabilityAccessGeometryBoundary : Set where
  constructor contestabilityAccessGeometryBoundary
  field
    formalAvailabilityEqualsUsableAccess : Bool
    scalarTotalSufficesForAllAccessDimensions : Bool
    coordinateBottlenecksCanMatter : Bool
    assistanceIsRepresentedSeparately : Bool
    natCoordinatesAreEmpiricalRealWorldMeasurements : Bool
    accessGeometryCreatesLegalDuty : Bool

canonicalContestabilityAccessGeometryBoundary :
  ContestabilityAccessGeometryBoundary
canonicalContestabilityAccessGeometryBoundary =
  contestabilityAccessGeometryBoundary false false true true false false

record ContestabilityAccessGeometryReceipt : Set where
  constructor contestabilityAccessGeometryReceipt
  field
    sources : List Sources.ScholarlySource
    boundary : ContestabilityAccessGeometryBoundary

canonicalContestabilityAccessGeometryReceipt :
  ContestabilityAccessGeometryReceipt
canonicalContestabilityAccessGeometryReceipt =
  contestabilityAccessGeometryReceipt
    (Sources.washingtonAccessJusticeTechnologyPrinciples ∷ [])
    canonicalContestabilityAccessGeometryBoundary
