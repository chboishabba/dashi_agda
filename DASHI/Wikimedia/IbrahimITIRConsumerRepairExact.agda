module DASHI.Wikimedia.IbrahimITIRConsumerRepairExact where

open import DASHI.Core.Prelude

import DASHI.Wikimedia.WikipediaFirstLinkNetworkExact as FLN
import DASHI.Wikimedia.IbrahimMultilingualHyperfabricWeldExact as Weld
import DASHI.Cognition.PNF.ITIRRelationalInterlinguaConsumerFibreExact as ITIR
import DASHI.Core.ConsumerDescentMinimalObserverExact as Descent
import DASHI.Core.ConsumerFibreRepairExact as Repair
import DASHI.Core.ConsumerFamilyRefinementKernelExact as Family
import DASHI.Core.ObserverRefinementLatticeExact as Observer
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Core.ContextIndexedPNFComparisonTransportExact as Transport

------------------------------------------------------------------------
-- IBRAHIM / ITIR FIRST-LINK CONSUMER-RELATIVE REPAIR
--
-- Method and original empirical ownership:
-- Mark Ibrahim, Christopher M. Danforth, Peter Sheridan Dodds,
-- "Connecting every bit of knowledge: The structure of Wikipedia's
-- First Link Network", Journal of Computational Science 19 (2017),
-- 21-30. DOI 10.1016/j.jocs.2016.12.001.
--
-- The finite three-observation fixture below is NEW DASHI mathematics.
-- It is NOT a sampled Wikipedia translation pair or an assertion about
-- an actual enwiki/dewiki edit. A common abstract QID coordinate is
-- insufficient for the declared first-link query. A local refinement
-- repairs exactly that query, not arbitrary queries or source claims.
--
-- Reuse all consumer/non-descent, repair and family factorisation owners.
------------------------------------------------------------------------

methodSource : FLN.FirstLinkStudySource
methodSource = FLN.ibrahimDanforthDodds2017

data FixtureObservation : Set where
  enVersionOne otherEditionOne enVersionTwo : FixtureObservation

data CandidateEntityCoordinate : Set where
  sharedQidCoordinate : CandidateEntityCoordinate

data FirstLinkTarget : Set where
  philosophyTarget scienceTarget : FirstLinkTarget

data RevisionCoordinate : Set where
  firstRevision otherRevision laterRevision : RevisionCoordinate

qidProjection : FixtureObservation → CandidateEntityCoordinate
qidProjection enVersionOne = sharedQidCoordinate
qidProjection otherEditionOne = sharedQidCoordinate
qidProjection enVersionTwo = sharedQidCoordinate

firstLinkObservation : FixtureObservation → FirstLinkTarget
firstLinkObservation enVersionOne = philosophyTarget
firstLinkObservation otherEditionOne = scienceTarget
firstLinkObservation enVersionTwo = philosophyTarget

revisionObservation : FixtureObservation → RevisionCoordinate
revisionObservation enVersionOne = firstRevision
revisionObservation otherEditionOne = otherRevision
revisionObservation enVersionTwo = laterRevision

------------------------------------------------------------------------
-- Same candidate QID, different first-link consumer outcomes.
-- Distinct constructors are an executable finite negative witness.
------------------------------------------------------------------------

firstLinkCollisionIsConsumerNonDescent :
  Descent.ConsumerNonDescentWitness qidProjection firstLinkObservation
firstLinkCollisionIsConsumerNonDescent =
  Descent.consumerNonDescentWitness
    enVersionOne otherEditionOne refl (λ ())

sharedQidCannotPayFirstLinkConsumer :
  Descent.ConsumerSufficient qidProjection firstLinkObservation → ⊥
sharedQidCannotPayFirstLinkConsumer =
  Descent.nonDescentWitnessBlocksSufficiency
    firstLinkCollisionIsConsumerNonDescent

firstLinkRefinedObserver :
  FixtureObservation → (CandidateEntityCoordinate × FirstLinkTarget)
firstLinkRefinedObserver =
  Observer.pairObserver qidProjection firstLinkObservation

firstLinkRepairIsConsumerSufficient :
  Repair.RefinementRepairs qidProjection firstLinkObservation
    firstLinkObservation
firstLinkRepairIsConsumerSufficient =
  Observer.pairRefinesRight qidProjection firstLinkObservation

firstLinkRepairSeparatesConsumerCollision :
  ∀ {Refinement : Set} {extra : FixtureObservation → Refinement} →
  Repair.RefinementRepairs qidProjection extra firstLinkObservation →
  extra enVersionOne ≡ extra otherEditionOne → ⊥
firstLinkRepairSeparatesConsumerCollision sufficient sameExtra =
  Repair.refinementRepairSeparatesWitness
    firstLinkCollisionIsConsumerNonDescent sufficient sameExtra

------------------------------------------------------------------------
-- Exact consumer-family repair: the canonical FactorsThrough carrier
-- records retention of the old QID view and payment of the chosen query.
------------------------------------------------------------------------

data FirstLinkConsumer : Set where
  firstLinkQuery revisionQuery : FirstLinkConsumer

QueryOutcome : FirstLinkConsumer → Set
QueryOutcome firstLinkQuery = FirstLinkTarget
QueryOutcome revisionQuery = RevisionCoordinate

queryObservation :
  (query : FirstLinkConsumer) → FixtureObservation → QueryOutcome query
queryObservation firstLinkQuery = firstLinkObservation
queryObservation revisionQuery = revisionObservation

firstLinkFamily : Family.ConsumerFamily FixtureObservation FirstLinkConsumer
firstLinkFamily = Family.consumer-family QueryOutcome queryObservation

firstLinkFamilyCollision :
  Family.FamilyCollision qidProjection firstLinkFamily
firstLinkFamilyCollision =
  Family.family-collision firstLinkQuery
    (NF.nonFactorabilityWitness enVersionOne otherEditionOne
      refl (λ ()))

firstLinkRepair :
  Family.ConsumerFamilyRepair qidProjection
    firstLinkFamily firstLinkFamilyCollision
firstLinkRepair =
  Family.consumer-family-repair
    (CandidateEntityCoordinate × FirstLinkTarget)
    firstLinkRefinedObserver
    (NF.factorsThrough proj₁ (λ state → refl))
    (NF.factorsThrough proj₂ (λ state → refl))

firstLinkRepairRetainsOriginalView :
  NF.FactorsThrough (Family.refine firstLinkRepair) qidProjection
firstLinkRepairRetainsOriginalView =
  Family.repairRetainsCoarseObserver firstLinkRepair

firstLinkRepairPaysSelectedConsumer :
  NF.FactorsThrough
    (Family.refine firstLinkRepair)
    (Family.observe firstLinkFamily firstLinkQuery)
firstLinkRepairPaysSelectedConsumer =
  Family.repairPaysFailedConsumer firstLinkRepair

------------------------------------------------------------------------
-- Negative control: the local repair loses the edition-revision
-- distinction. Thus it cannot be advertised as all-consumer parity.
------------------------------------------------------------------------

revisionStillCollides :
  NF.NonFactorabilityWitness firstLinkRefinedObserver
    revisionObservation
revisionStillCollides =
  NF.nonFactorabilityWitness enVersionOne enVersionTwo
    refl (λ ())

revisionQueryStillCollides :
  Family.FamilyCollision firstLinkRefinedObserver firstLinkFamily
revisionQueryStillCollides =
  Family.family-collision revisionQuery revisionStillCollides

firstLinkRepairDoesNotPayAllConsumers :
  Family.FamilyFactorsThrough firstLinkRefinedObserver
    firstLinkFamily → ⊥
firstLinkRepairDoesNotPayAllConsumers =
  Family.collisionRulesOutFamilyFactorisation
    revisionQueryStillCollides

------------------------------------------------------------------------
-- Existing ITIR source comparison + bounded repair stay separate from
-- source mutation. The caller must provide a revision-pinned comparison
-- and a reviewed repair with a preservation witness for the selected
-- consumer. This contract never manufactures a Wikipedia edit.
------------------------------------------------------------------------

record ReviewedSourceBoundRepair
  {State Outcome : Set}
  (query : State → Outcome)
  (left right : ITIR.SourceObservation)
  (consumer : ITIR.ConsumerLicence) : Set where
  constructor reviewedSourceBoundRepair
  field
    sourceComparison : Weld.RevisionBoundComparison left right consumer
    boundedRepair : Transport.ConsumerBoundedRepair State Outcome query
    reviewReceipt : String
    recheckReceipt : String
    createsWikipediaEdit : Bool
    createsWikipediaEditFalse : createsWikipediaEdit ≡ false

open ReviewedSourceBoundRepair public

reviewedRepairRerunSound :
  ∀ {State Outcome : Set}
    {query : State → Outcome}
    {left right : ITIR.SourceObservation}
    {consumer : ITIR.ConsumerLicence} →
  (caseReceipt : ReviewedSourceBoundRepair query left right consumer) →
  (state : State) →
  query (Transport.repair (boundedRepair caseReceipt) state)
    ≡ query state
reviewedRepairRerunSound caseReceipt state =
  Transport.consumerPreservation (boundedRepair caseReceipt) state

reviewedRepairDoesNotPromoteSourceTruth :
  ∀ {State Outcome : Set}
    {query : State → Outcome}
    {left right : ITIR.SourceObservation}
    {consumer : ITIR.ConsumerLicence} →
  (caseReceipt : ReviewedSourceBoundRepair query left right consumer) →
  ITIR.createsPropositionTruth
    (Weld.compared (sourceComparison caseReceipt)) ≡ false
reviewedRepairDoesNotPromoteSourceTruth caseReceipt =
  ITIR.comparisonNeverPaysTruth
    (Weld.compared (sourceComparison caseReceipt))
