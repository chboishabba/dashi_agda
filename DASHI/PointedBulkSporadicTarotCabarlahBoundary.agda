module DASHI.PointedBulkSporadicTarotCabarlahBoundary where

open import DASHI.Core.Prelude

import DASHI.Biology.PointedTernaryBulkExact as Bulk
import DASHI.Biology.ReducedFiftyThreeOrbitCandidateExact as Orbit
import DASHI.Biology.SporadicTarotDependencyExact as Tarot
import DASHI.Biology.PointedBulkReducedMoonshineBoundary as Moonshine
import DASHI.Biology.PointedBulkSporadicTarotSourceAtlas as Sources
import DASHI.Governance.CabarlahTraumaProjectionBridgeExact as Cabarlah

record PointedBulkSporadicTarotCabarlahBoundary : Set where
  field
    pointedBulkBoundary : Bulk.PointedTernaryBulkBoundary
    residualOrbitBoundary : Orbit.ReducedFiftyThreeOrbitBoundary
    sporadicTarotBoundary : Tarot.SporadicTarotBoundary
    moonshineBoundary : Moonshine.PointedBulkReducedMoonshineBoundary
    cabarlahProjectionBoundary : Cabarlah.CabarlahTraumaProjectionBoundary

    markerCountIsTen : Bulk.markerCount ≡ 10
    bulkCountIs196830 : Bulk.pointedBulkDimension ≡ 196830
    bulkIsUnpointedPlusPointed :
      Bulk.pointedBulkDimension ≡ Bulk.unpointedPlusPointedDimension
    pointedD4DimensionIsTen : Bulk.pointedRepresentationDimension ≡ 10
    pointedA2RemainsAbsent :
      Bulk.pointedMultiplicity
        DASHI.Biology.TernaryMonsterSymmetryCandidateExact.A2
      ≡ 0

    candidateResidualCountIs53 : Orbit.candidateR53Dimension ≡ 53
    candidateInvolutionSquaresToIdentity :
      (state : Orbit.CandidateR53) →
      Orbit.candidateInvolution (Orbit.candidateInvolution state) ≡ state

    fullCoefficientIs196884 : Moonshine.fullCoefficientDimension ≡ 196884
    nontrivialCoefficientIs196883 :
      Moonshine.nontrivialCoefficientDimension ≡ 196883

    sporadicInventoryIsTwentySix : Tarot.sporadicInventoryCount ≡ 26
    arcanaDeficitIsFour : Tarot.inventoryMinusArcanaCount ≡ 4
    syntheticCo4HasNoReferent :
      Tarot.conwayCardReferent Tarot.Co4SyntheticCard ≡ Tarot.none
    dependencyGraphHasSixteenTypedEdges :
      Tarot.canonicalDependencyEdgeCount ≡ 16

    reflectingPoolMotiveBlocked :
      DASHI.Governance.TraumaMemorySublationBoundary.motiveInferredAsFact
        DASHI.Governance.TraumaMemorySublationBoundary.reflectingPoolObservation
      ≡ false
    pineGapSpecificStrikePromotionBlocked :
      DASHI.Physics.Foundations.IndigenousMilitaryIntelligenceCircuitExact.openSourceOperationalStatus
      ≡
      DASHI.Physics.Foundations.IndigenousMilitaryIntelligenceCircuitExact.publiclyVerifiedSpecificStrikeLink
      → ⊥

    sourceCountIsFour : Sources.canonicalSourceCount ≡ 4

open PointedBulkSporadicTarotCabarlahBoundary public

canonicalPointedBulkSporadicTarotCabarlahBoundary :
  PointedBulkSporadicTarotCabarlahBoundary
canonicalPointedBulkSporadicTarotCabarlahBoundary =
  record
    { pointedBulkBoundary = Bulk.canonicalPointedTernaryBulkBoundary
    ; residualOrbitBoundary = Orbit.canonicalReducedFiftyThreeOrbitBoundary
    ; sporadicTarotBoundary = Tarot.canonicalSporadicTarotBoundary
    ; moonshineBoundary = Moonshine.canonicalPointedBulkReducedMoonshineBoundary
    ; cabarlahProjectionBoundary =
        Cabarlah.canonicalCabarlahTraumaProjectionBoundary
    ; markerCountIsTen = Bulk.markerCountIsTen
    ; bulkCountIs196830 = Bulk.pointedBulkDimensionIs196830
    ; bulkIsUnpointedPlusPointed =
        Bulk.pointedBulkEqualsUnpointedPlusPointed
    ; pointedD4DimensionIsTen = Bulk.pointedRepresentationDimensionIsTen
    ; pointedA2RemainsAbsent = Bulk.pointedA2MultiplicityIsZero
    ; candidateResidualCountIs53 = Orbit.candidateR53DimensionIsFiftyThree
    ; candidateInvolutionSquaresToIdentity =
        Orbit.candidateInvolutionIsInvolutive
    ; fullCoefficientIs196884 =
        Moonshine.fullCoefficientDimensionIs196884
    ; nontrivialCoefficientIs196883 =
        Moonshine.nontrivialCoefficientDimensionIs196883
    ; sporadicInventoryIsTwentySix =
        Tarot.sporadicInventoryCountIsTwentySix
    ; arcanaDeficitIsFour = Tarot.inventoryMinusArcanaCountIsFour
    ; syntheticCo4HasNoReferent = Tarot.co4HasNoConwaySporadicReferent
    ; dependencyGraphHasSixteenTypedEdges =
        Tarot.canonicalDependencyEdgeCountIsSixteen
    ; reflectingPoolMotiveBlocked =
        Cabarlah.reflectingPoolReadingDoesNotInferMotive
    ; pineGapSpecificStrikePromotionBlocked =
        Cabarlah.pineGapConcernDoesNotVerifySpecificStrike
    ; sourceCountIsFour = Sources.canonicalSourceCountIsFour
    }
