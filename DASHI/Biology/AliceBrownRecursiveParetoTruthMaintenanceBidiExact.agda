module DASHI.Biology.AliceBrownRecursiveParetoTruthMaintenanceBidiExact where

open import DASHI.Core.Prelude

import DASHI.Biology.AliceBrownSelectiveInvalidationParetoBidiExact as Alice
import DASHI.Core.ExperimentalOutcomeOrientationBackpropagationBidiExact as Outcome
import DASHI.Core.RecursiveSelectiveInvalidationParetoTruthMaintenanceBidiExact as Recursive
import DASHI.Core.SelectiveInvalidationParetoFrontierBidiExact as Pareto

------------------------------------------------------------------------
-- ALICE BROWN RECURSIVE SELECTIVE-INVALIDATION RETURN
--
-- A changed survey/voice/agency path may generate a next debugging frontier,
-- while an observer path already classified as unrelated remains retained.
-- This is a DASHI methodological scheduler over the existing Alice corpus; it
-- does not attribute this recursive formalism to the source authors.
------------------------------------------------------------------------

data AliceRoundCandidate : Set where
  voiceAgency : AliceRoundCandidate
  parentObserver : AliceRoundCandidate
  consumerReview : AliceRoundCandidate
  authorityReview : AliceRoundCandidate

aliceCertificate : AliceRoundCandidate → Pareto.CertificateCandidate
aliceCertificate voiceAgency = Alice.voiceAgencyCertificate
aliceCertificate parentObserver = Alice.parentObserverCertificate
aliceCertificate consumerReview = Alice.consumerReformulationCandidate
aliceCertificate authorityReview = Alice.authorityCertificate

aliceClass : AliceRoundCandidate → Pareto.RecomputeClass
aliceClass candidate = Pareto.class (aliceCertificate candidate)

parentObserverRemainsUnaffected :
  aliceClass parentObserver ≡ Pareto.provablyUnaffected
parentObserverRemainsUnaffected = refl

voiceAgencyIsCurrentMustRecompute :
  aliceClass voiceAgency ≡ Pareto.mustRecompute
voiceAgencyIsCurrentMustRecompute = refl

authorityRemainsBlocked :
  aliceClass authorityReview ≡ Pareto.authorityBlocked
authorityRemainsBlocked = refl

-- The next Alice debugging round may open a lineage-sensitive diagnostic
-- coordinate while retaining the four semantic Pareto dimensions.
aliceNextAmbient : Pareto.AmbientAxisCapacity
aliceNextAmbient =
  Pareto.ambient-axis-capacity
    4
    (Pareto.selfIndexedCapacity 4)
    4
    19683
    "Alice next recursive maintenance level; 19683 remains visualisation cardinality, not dimension"
    true

aliceSemanticDimensionStillFour :
  Pareto.declaredSemanticAxisCount aliceNextAmbient ≡ 4
aliceSemanticDimensionStillFour = refl

aliceNextCapacityRemainsSymbolic :
  Pareto.capacityExpression aliceNextAmbient ≡ Pareto.selfIndexedCapacity 4
aliceNextCapacityRemainsSymbolic = refl

-- Reuse the generic recursive theorem as the exact maintenance discipline.
aliceRecursiveBoundary : Recursive.RecursiveMaintenanceBoundary
aliceRecursiveBoundary = Recursive.canonicalRecursiveMaintenanceBoundary

aliceParentPathRetainedAcrossGenericLift :
  Recursive.candidateClass Recursive.layer1
    (Recursive.liftCandidate Recursive.recursiveStep01 Recursive.frame0)
  ≡ Pareto.provablyUnaffected
aliceParentPathRetainedAcrossGenericLift =
  Recursive.frameClassStillUnaffectedAfterRecursiveLift

data AliceRecursiveLiftReopensEveryObserver : Set where
data AliceRecursiveParetoCreatesAuthority : Set where
data AliceNextCapacityRequiresFullCorpusEnumeration : Set where

aliceRecursiveLiftDoesNotReopenEveryObserver :
  AliceRecursiveLiftReopensEveryObserver → ⊥
aliceRecursiveLiftDoesNotReopenEveryObserver ()

aliceRecursiveParetoDoesNotCreateAuthority :
  AliceRecursiveParetoCreatesAuthority → ⊥
aliceRecursiveParetoDoesNotCreateAuthority ()

aliceNextCapacityDoesNotRequireFullCorpusEnumeration :
  AliceNextCapacityRequiresFullCorpusEnumeration → ⊥
aliceNextCapacityDoesNotRequireFullCorpusEnumeration ()

record AliceBrownRecursiveParetoBoundary : Set where
  constructor alice-brown-recursive-pareto-boundary
  field
    voiceAgencyMayDriveNextRound : Bool
    unrelatedParentObserverMayStayRetained : Bool
    authorityStillRequiresIndependentProducer : Bool
    semanticDimensionRemainsConsumerDeclared : Bool
    recursiveCapacityMayRemainSymbolic : Bool
    recursiveLiftCreatesStudentAuthority : Bool

canonicalAliceBrownRecursiveParetoBoundary : AliceBrownRecursiveParetoBoundary
canonicalAliceBrownRecursiveParetoBoundary =
  alice-brown-recursive-pareto-boundary true true true true true false
