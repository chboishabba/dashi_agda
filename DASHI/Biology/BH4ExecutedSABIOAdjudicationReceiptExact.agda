module DASHI.Biology.BH4ExecutedSABIOAdjudicationReceiptExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as Receipt

record ExecutedSABIOAdjudicationReceipt : Set where
  constructor executed-sabio-adjudication-receipt
  field
    parameterCandidateCount : Nat
    mappedParameterCandidateCount : Nat
    finiteReactionCoverage : Nat
    affinityLikeCount : Nat
    rateLikeCount : Nat
    turnoverLikeCount : Nat
    unclassifiedCount : Nat
    coveredFiniteReactions : List String
    uncoveredFiniteReactions : List String
    adjudicationExecuted : Bool

open ExecutedSABIOAdjudicationReceipt public

canonicalExecutedSABIOAdjudicationReceipt : ExecutedSABIOAdjudicationReceipt
canonicalExecutedSABIOAdjudicationReceipt =
  executed-sabio-adjudication-receipt
    932 875 10 237 139 30 526
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

record ExecutedSABIOAdjudicationBoundary : Set where
  constructor executed-sabio-adjudication-boundary
  field
    candidateCoverageCreatesFluxPayment : Bool
    candidateCoverageCreatesFluxPaymentIsFalse : candidateCoverageCreatesFluxPayment ≡ false
    proteinLinkCreatesSameAssayReactionIdentity : Bool
    proteinLinkCreatesSameAssayReactionIdentityIsFalse : proteinLinkCreatesSameAssayReactionIdentity ≡ false
    missingSABIORowMeansNoPrimaryKinetics : Bool
    missingSABIORowMeansNoPrimaryKineticsIsFalse : missingSABIORowMeansNoPrimaryKinetics ≡ false
    tenOfTwelveCoverageCreatesWholeNetworkClosure : Bool
    tenOfTwelveCoverageCreatesWholeNetworkClosureIsFalse : tenOfTwelveCoverageCreatesWholeNetworkClosure ≡ false

open ExecutedSABIOAdjudicationBoundary public

canonicalExecutedSABIOAdjudicationBoundary : ExecutedSABIOAdjudicationBoundary
canonicalExecutedSABIOAdjudicationBoundary =
  executed-sabio-adjudication-boundary false refl false refl false refl false refl

canonicalExecutedSABIOAdjudicationGenericReceipt : Receipt.GenericReceipt
canonicalExecutedSABIOAdjudicationGenericReceipt =
  Receipt.mkNonPromotingReceipt
    "executed BH4 SABIO adjudication receipt"
    "DASHI.Biology.BH4ExecutedSABIOAdjudicationReceiptExact"
    "932 parameter candidates -> 875 candidates mapping to finite matrix columns -> 10/12 finite reactions covered; RHEA:11920 and RHEA:19897 remain uncovered by exact-UniProt SABIO rows"
    "closes acquisition-side candidate coverage accounting and isolates the next work to condition/unit adjudication plus primary-literature gap filling"
    "candidate coverage is not flux payment; protein-to-Rhea identity is not same-assay reaction identity; missing SABIO rows do not mean absent kinetics; 10/12 candidate coverage is not whole-network closure"
    "python3 scripts/run_bh4_phase4_maxcut.py"
