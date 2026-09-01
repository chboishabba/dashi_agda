module DASHI.Reasoning.Spacy369ConsumerPolicyParetoTernaryExact where

open import DASHI.Core.Prelude

import Base369 as Base

------------------------------------------------------------------------
-- PROOF-FIRST PARETO -> TERNARY CONSUMER-POLICY COMPARISON.
--
-- This is a local DASHI policy fixture inspired by the product/Pareto shape in
-- the live intellectual-reception work.  It does not import that draft owner.
-- Ternary classification is produced only after proof of dominance or mutual
-- non-dominance; tri-mid is therefore not pasted on as an unexplained label.
------------------------------------------------------------------------

data AxisLevel : Set where
  weak strong : AxisLevel

data _≤A_ : AxisLevel → AxisLevel → Set where
  weak≤weak : weak ≤A weak
  weak≤strong : weak ≤A strong
  strong≤strong : strong ≤A strong

strongNotBelowWeak : strong ≤A weak → ⊥
strongNotBelowWeak ()

record PolicyProfile : Set where
  constructor policyProfile
  field
    consumerCoverage : AxisLevel
    measurementEconomy : AxisLevel
    provenanceStrength : AxisLevel
    authorityStrength : AxisLevel

open PolicyProfile public

record ParetoNoWorse (left right : PolicyProfile) : Set where
  constructor paretoNoWorse
  field
    coverageNoWorse : consumerCoverage left ≤A consumerCoverage right
    economyNoWorse : measurementEconomy left ≤A measurementEconomy right
    provenanceNoWorse : provenanceStrength left ≤A provenanceStrength right
    authorityNoWorse : authorityStrength left ≤A authorityStrength right

open ParetoNoWorse public

------------------------------------------------------------------------
-- Concrete profiles: one is coverage-rich but measurement-expensive; the other
-- is measurement-efficient but covers fewer declared consumers.  Provenance and
-- authority are intentionally held fixed so the crossing is easy to audit.
------------------------------------------------------------------------

baselinePolicy : PolicyProfile
baselinePolicy = policyProfile weak weak weak weak

governedFullPolicy : PolicyProfile
governedFullPolicy = policyProfile strong strong strong strong

sharedEfficientPolicy : PolicyProfile
sharedEfficientPolicy = policyProfile weak strong strong strong

fullCoverageExpensivePolicy : PolicyProfile
fullCoverageExpensivePolicy = policyProfile strong weak strong strong

baselineBelowGoverned : ParetoNoWorse baselinePolicy governedFullPolicy
baselineBelowGoverned =
  paretoNoWorse weak≤strong weak≤strong weak≤strong weak≤strong

governedNotBelowBaseline :
  ParetoNoWorse governedFullPolicy baselinePolicy → ⊥
governedNotBelowBaseline relation =
  strongNotBelowWeak (coverageNoWorse relation)

sharedNotBelowFull :
  ParetoNoWorse sharedEfficientPolicy fullCoverageExpensivePolicy → ⊥
sharedNotBelowFull relation =
  strongNotBelowWeak (economyNoWorse relation)

fullNotBelowShared :
  ParetoNoWorse fullCoverageExpensivePolicy sharedEfficientPolicy → ⊥
fullNotBelowShared relation =
  strongNotBelowWeak (coverageNoWorse relation)

------------------------------------------------------------------------
-- Three-way result is proof-relevant.
------------------------------------------------------------------------

data ParetoTernary (left right : PolicyProfile) : Set where
  leftDominates :
    ParetoNoWorse right left →
    (ParetoNoWorse left right → ⊥) →
    ParetoTernary left right
  rightDominates :
    ParetoNoWorse left right →
    (ParetoNoWorse right left → ⊥) →
    ParetoTernary left right
  incomparable :
    (ParetoNoWorse left right → ⊥) →
    (ParetoNoWorse right left → ⊥) →
    ParetoTernary left right

paretoTrit :
  ∀ {left right} → ParetoTernary left right → Base.TriTruth
paretoTrit (leftDominates _ _) = Base.tri-high
paretoTrit (rightDominates _ _) = Base.tri-low
paretoTrit (incomparable _ _) = Base.tri-mid

governedDominatesBaseline :
  ParetoTernary governedFullPolicy baselinePolicy
governedDominatesBaseline =
  leftDominates baselineBelowGoverned governedNotBelowBaseline

governedDominanceChartsHigh :
  paretoTrit governedDominatesBaseline ≡ Base.tri-high
governedDominanceChartsHigh = refl

sharedVersusFullIsIncomparable :
  ParetoTernary sharedEfficientPolicy fullCoverageExpensivePolicy
sharedVersusFullIsIncomparable =
  incomparable sharedNotBelowFull fullNotBelowShared

incomparabilityChartsMid :
  paretoTrit sharedVersusFullIsIncomparable ≡ Base.tri-mid
incomparabilityChartsMid = refl

------------------------------------------------------------------------
-- Boundary: the ternary code is downstream of the product-order proofs.
------------------------------------------------------------------------

record Spacy369ConsumerPolicyParetoTernaryBoundary : Set where
  constructor spacy369ConsumerPolicyParetoTernaryBoundary
  field
    ternaryComparisonRequiresRelationalProofHere : Bool
    ternaryComparisonRequiresRelationalProofHereIsTrue :
      ternaryComparisonRequiresRelationalProofHere ≡ true
    triMidHereMeansParetoIncomparability : Bool
    triMidHereMeansParetoIncomparabilityIsTrue :
      triMidHereMeansParetoIncomparability ≡ true
    triMidHereMeansLogicalFalsehood : Bool
    triMidHereMeansLogicalFalsehoodIsFalse :
      triMidHereMeansLogicalFalsehood ≡ false
    triMidHereMeansEqualImportance : Bool
    triMidHereMeansEqualImportanceIsFalse :
      triMidHereMeansEqualImportance ≡ false
    paretoDominanceIsGlobalTruthRanking : Bool
    paretoDominanceIsGlobalTruthRankingIsFalse :
      paretoDominanceIsGlobalTruthRanking ≡ false
    paretoDominanceIsMoralRanking : Bool
    paretoDominanceIsMoralRankingIsFalse :
      paretoDominanceIsMoralRanking ≡ false
    dominanceExtendsBeyondDeclaredAxesAutomatically : Bool
    dominanceExtendsBeyondDeclaredAxesAutomaticallyIsFalse :
      dominanceExtendsBeyondDeclaredAxesAutomatically ≡ false
    binaryInteractionImpliesBinaryOntology : Bool
    binaryInteractionImpliesBinaryOntologyIsFalse :
      binaryInteractionImpliesBinaryOntology ≡ false

canonicalSpacy369ConsumerPolicyParetoTernaryBoundary :
  Spacy369ConsumerPolicyParetoTernaryBoundary
canonicalSpacy369ConsumerPolicyParetoTernaryBoundary =
  spacy369ConsumerPolicyParetoTernaryBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
