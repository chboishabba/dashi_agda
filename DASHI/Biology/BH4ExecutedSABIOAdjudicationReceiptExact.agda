module DASHI.Biology.BH4ExecutedSABIOAdjudicationReceiptExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- Executed SABIO -> finite-Rhea adjudication receipt, schema v2.
--
-- Live execution:
--   932 parameter candidates
--   875 candidate occurrences map to finite matrix columns
--   10 / 12 finite reactions have direct SABIO candidate coverage
--   uncovered: RHEA:11920 (PCBD1), RHEA:19897 (NOS)
--
-- Refined parameter hints:
--   concentration-like       475
--   affinity-like            160
--   rate-like                139
--   inhibitory-like           83
--   catalytic-constant-like   30
--   unclassified              45
--
-- These are descriptive acquisition/adjudication counts only.  No class or
-- rank is itself a solver-facing flux interval.
------------------------------------------------------------------------

record ExecutedSABIOAdjudicationReceipt : Set where
  constructor executed-sabio-adjudication-receipt
  field
    parameterCandidateCount : Nat
    mappedParameterCandidateCount : Nat
    finiteReactionCoverage : Nat
    concentrationLikeCount : Nat
    affinityLikeCount : Nat
    rateLikeCount : Nat
    inhibitoryLikeCount : Nat
    catalyticConstantLikeCount : Nat
    unclassifiedCount : Nat
    coveredFiniteReactions : List String
    uncoveredFiniteReactions : List String
    adjudicationExecuted : Bool

open ExecutedSABIOAdjudicationReceipt public

canonicalExecutedSABIOAdjudicationReceipt : ExecutedSABIOAdjudicationReceipt
canonicalExecutedSABIOAdjudicationReceipt =
  executed-sabio-adjudication-receipt
    932 875 10 475 160 139 83 30 45
    ( "RHEA:16709" ∷ "RHEA:17473" ∷ "RHEA:17865" ∷ "RHEA:17869"
    ∷ "RHEA:18201" ∷ "RHEA:18953" ∷ "RHEA:20273" ∷ "RHEA:22048"
    ∷ "RHEA:32627" ∷ "RHEA:36255" ∷ [] )
    ( "RHEA:11920" ∷ "RHEA:19897" ∷ [] )
    true

executedParameterCandidateCount : Nat
executedParameterCandidateCount = parameterCandidateCount canonicalExecutedSABIOAdjudicationReceipt

executedMappedParameterCandidateCount : Nat
executedMappedParameterCandidateCount = mappedParameterCandidateCount canonicalExecutedSABIOAdjudicationReceipt

executedFiniteReactionCoverage : Nat
executedFiniteReactionCoverage = finiteReactionCoverage canonicalExecutedSABIOAdjudicationReceipt

executedConcentrationLikeCount : Nat
executedConcentrationLikeCount = concentrationLikeCount canonicalExecutedSABIOAdjudicationReceipt

executedAffinityLikeCount : Nat
executedAffinityLikeCount = affinityLikeCount canonicalExecutedSABIOAdjudicationReceipt

executedRateLikeCount : Nat
executedRateLikeCount = rateLikeCount canonicalExecutedSABIOAdjudicationReceipt

executedInhibitoryLikeCount : Nat
executedInhibitoryLikeCount = inhibitoryLikeCount canonicalExecutedSABIOAdjudicationReceipt

executedCatalyticConstantLikeCount : Nat
executedCatalyticConstantLikeCount = catalyticConstantLikeCount canonicalExecutedSABIOAdjudicationReceipt

executedUnclassifiedCount : Nat
executedUnclassifiedCount = unclassifiedCount canonicalExecutedSABIOAdjudicationReceipt

executedClassificationTotalExact :
  executedConcentrationLikeCount + executedAffinityLikeCount + executedRateLikeCount
  + executedInhibitoryLikeCount + executedCatalyticConstantLikeCount + executedUnclassifiedCount
  ≡ 932
executedClassificationTotalExact = refl

record ExecutedSABIOAdjudicationBoundary : Set where
  constructor executed-sabio-adjudication-boundary
  field
    candidateCoverageCreatesFluxPayment : Bool
    candidateCoverageCreatesFluxPaymentIsFalse : candidateCoverageCreatesFluxPayment ≡ false
    parameterKindCreatesFluxPayment : Bool
    parameterKindCreatesFluxPaymentIsFalse : parameterKindCreatesFluxPayment ≡ false
    proteinLinkCreatesSameAssayReactionIdentity : Bool
    proteinLinkCreatesSameAssayReactionIdentityIsFalse : proteinLinkCreatesSameAssayReactionIdentity ≡ false
    missingSABIORowMeansNoPrimaryKinetics : Bool
    missingSABIORowMeansNoPrimaryKineticsIsFalse : missingSABIORowMeansNoPrimaryKinetics ≡ false
    tenOfTwelveCoverageCreatesWholeNetworkClosure : Bool
    tenOfTwelveCoverageCreatesWholeNetworkClosureIsFalse : tenOfTwelveCoverageCreatesWholeNetworkClosure ≡ false

open ExecutedSABIOAdjudicationBoundary public

canonicalExecutedSABIOAdjudicationBoundary : ExecutedSABIOAdjudicationBoundary
canonicalExecutedSABIOAdjudicationBoundary =
  executed-sabio-adjudication-boundary false refl false refl false refl false refl false refl

canonicalExecutedSABIOAdjudicationGenericReceipt : Receipt.GenericReceipt
canonicalExecutedSABIOAdjudicationGenericReceipt =
  Receipt.mkNonPromotingReceipt
    "executed BH4 SABIO adjudication receipt v2"
    "DASHI.Biology.BH4ExecutedSABIOAdjudicationReceiptExact"
    "932 parameter candidates -> 875 finite-column mappings -> 10/12 finite reactions covered; refined hints 475 concentration, 160 affinity, 139 rate, 83 inhibitory, 30 catalytic-constant, 45 unclassified; RHEA:11920 and RHEA:19897 remain uncovered by exact-UniProt SABIO rows"
    "closes acquisition-side candidate classification/coverage accounting and advances the live work to ranked scientific adjudication plus primary-literature translation for the two uncovered columns"
    "candidate coverage and parameter-kind hints are not flux payment; protein-to-Rhea identity is not same-assay identity; missing SABIO rows do not mean absent kinetics; 10/12 candidate coverage is not whole-network closure"
    "python3 scripts/run_bh4_phase4_maxcut.py"
