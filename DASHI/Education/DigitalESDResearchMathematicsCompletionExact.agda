{-# OPTIONS --safe #-}
module DASHI.Education.DigitalESDResearchMathematicsCompletionExact where

------------------------------------------------------------------------
-- Mathematical ESD research-world completion, WITHOUT a second ontology.
-- Reuses the Golden open-axis, source review, reconstruction, typed
-- higher-order hyperfabric and question-relative gap owners.
--
-- This module does not assert a completed empirical ESD corpus, a
-- source-verified cross-study transport, or a numeric MP law.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_; _^_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Membership.Propositional using (_∈_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Core.IntersectionalNonFactorability as Factor
import DASHI.Education.DigitalESDOpenAxisStudyPartWorldExact as World
import DASHI.Education.DigitalESDIntersectionalRecompositionExact as Recomp
import DASHI.Education.DigitalESDHigherOrderFabricIncidenceExact as Higher
import DASHI.Education.DigitalESDOpenAxisGapTransportExact as Gap

------------------------------------------------------------------------
-- RM00. The 15 x 7 pilot is 105 ADDRESSES, not 105 entire possible
-- worlds.  Eight independent anonymous labels yield 8^105 functions.
-- Typed evidence data have richer, dependent inhabitants than labels.
------------------------------------------------------------------------

pilotAddressCount : Nat
pilotAddressCount = 15 * 7

pilotAddressCountIs105 : pilotAddressCount ≡ 105
pilotAddressCountIs105 = refl

eightLabelConfigurationCount : Nat
eightLabelConfigurationCount = 8 ^ pilotAddressCount

------------------------------------------------------------------------
-- RM01. Lossless source decomposition is not just an indexed 7-axis
-- table.  The actual study must be recoverable from its decomposition.
------------------------------------------------------------------------

record LosslessStudyDecomposition
  (scope : World.StudyWorldScope) : Set₁ where
  constructor lossless-study-decomposition
  field
    Packet : Set
    decompose : World.Study scope → Packet
    reconstruct : Packet → World.Study scope
    originalStudyRecovered :
      (s : World.Study scope) →
      reconstruct (decompose s) ≡ s

open LosslessStudyDecomposition public

asExistingLosslessRecomposition :
  {scope : World.StudyWorldScope} →
  (decomp : LosslessStudyDecomposition scope) →
  Recomp.LosslessRecomposition (decompose decomp)
asExistingLosslessRecomposition decomp =
  Recomp.lossless-recomposition
    (reconstruct decomp)
    (originalStudyRecovered decomp)

sourceIdentityRecovered :
  {scope : World.StudyWorldScope} →
  (decomp : LosslessStudyDecomposition scope) →
  (s : World.Study scope) →
  World.studySource scope
    (reconstruct decomp (decompose decomp s)) ≡
  World.studySource scope s
sourceIdentityRecovered {scope} decomp s =
  cong (World.studySource scope) (originalStudyRecovered decomp s)

everyStudyConsumerFactors :
  {scope : World.StudyWorldScope} →
  (decomp : LosslessStudyDecomposition scope) →
  {Answer : Set} →
  (question : World.Study scope → Answer) →
  Factor.FactorsThrough (decompose decomp) question
everyStudyConsumerFactors decomp question =
  Recomp.losslessSufficesForConsumer
    (decompose decomp) question
    (asExistingLosslessRecomposition decomp)

------------------------------------------------------------------------
-- RM02. Crosswalks are RESEARCH-QUESTION VIEWS into a single
-- AccountedStudyWorld, never a proof that two studies describe identical
-- participants, outcomes or governance contexts.
------------------------------------------------------------------------

data CrosswalkRelation : Set where
  complementarity : CrosswalkRelation
  productiveTension : CrosswalkRelation
  scopeDifference : CrosswalkRelation
  methodologicalChallenge : CrosswalkRelation
  candidateConflict : CrosswalkRelation
  notYetComparable : CrosswalkRelation

record SameWorldResearchCrosswalk
  (scope : World.StudyWorldScope)
  (world : World.AccountedStudyWorld scope) : Set₁ where
  constructor same-world-research-crosswalk
  field
    donor recipient : World.StudyPart scope
    donorAxis recipientAxis : World.Axis scope
    consumerQuestion : String
    relation : CrosswalkRelation
    contextAndPopulationTransportDebt : String
    sourceProvenanceReference : String

    originalDonorAssessment :
      World.PartAxisAccounting scope
        (World.study donor) (World.part donor) donorAxis
    originalRecipientAssessment :
      World.PartAxisAccounting scope
        (World.study recipient) (World.part recipient) recipientAxis

    donorIsSameWorld :
      originalDonorAssessment ≡
      World.accounting world
        (World.study donor) (World.part donor) donorAxis
    recipientIsSameWorld :
      originalRecipientAssessment ≡
      World.accounting world
        (World.study recipient) (World.part recipient) recipientAxis

open SameWorldResearchCrosswalk public

-- A real, directly reviewed pair needs two INDEPENDENT source-specific
-- evidence objects.  This record is not inhabited by mere topic overlap.
record DirectReviewedCrosswalk
  {scope : World.StudyWorldScope}
  {world : World.AccountedStudyWorld scope}
  (crosswalk : SameWorldResearchCrosswalk scope world) : Set₁ where
  constructor direct-reviewed-crosswalk
  field
    donorReview :
      World.ReviewedPartAxisEvidence scope
        (World.study (donor crosswalk))
        (World.part (donor crosswalk))
        (donorAxis crosswalk)
    recipientReview :
      World.ReviewedPartAxisEvidence scope
        (World.study (recipient crosswalk))
        (World.part (recipient crosswalk))
        (recipientAxis crosswalk)

    donorAccountIsReviewed :
      World.accounting world
        (World.study (donor crosswalk))
        (World.part (donor crosswalk))
        (donorAxis crosswalk) ≡
      World.directReviewed donorReview
    recipientAccountIsReviewed :
      World.accounting world
        (World.study (recipient crosswalk))
        (World.part (recipient crosswalk))
        (recipientAxis crosswalk) ≡
      World.directReviewed recipientReview

------------------------------------------------------------------------
-- RM03. N-ary hyperedge incidence must retain exact same-world identity
-- and actual part/axis memberships.  The existing HigherOrderFabric-
-- Incidence owner has the anchored nonempty conditions.
------------------------------------------------------------------------

record SameWorldHigherOrderConsumer
  (scope : World.StudyWorldScope)
  (world : World.AccountedStudyWorld scope)
  (Vertex Edge Scalar : Set) : Set₂ where
  constructor same-world-higher-order-consumer
  field
    incidence :
      Higher.HigherOrderFabricIncidence scope Vertex Edge Scalar
    fabricIsSameWorld :
      World.ResearchFabricProjection.world
        (Higher.HigherOrderFabricIncidence.projection incidence) ≡
      world

------------------------------------------------------------------------
-- RM04. Axis refinement cannot remove an old axis address.  This
-- theorem reuses the exact existing open-axis retraction rather than
-- equating an unreviewed new axis with an original source observation.
------------------------------------------------------------------------

oldAxisSurvivesRefinement :
  {Old New : Set} →
  (extension : Gap.OpenAxisExtension Old New) →
  (axis : Old) →
  Gap.leftInverse extension (Gap.embed extension axis) ≡ axis
oldAxisSurvivesRefinement extension axis =
  Gap.originalAxisIsRecovered extension axis

------------------------------------------------------------------------
-- RM05. The research crosswalk cannot create a new recipient
-- observation by its own existence; new source-specific review must
-- inhabit the donor and recipient evidence constructors separately.
------------------------------------------------------------------------

crosswalkDoesNotCreateRecipientObservation :
  Gap.CrossStudyGapCreatesRecipientObservation → ⊥
crosswalkDoesNotCreateRecipientObservation =
  Gap.crossStudyGapDoesNotCreateObservation
