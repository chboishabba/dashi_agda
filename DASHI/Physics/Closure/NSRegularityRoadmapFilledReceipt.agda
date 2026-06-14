module DASHI.Physics.Closure.NSRegularityRoadmapFilledReceipt where

open import Agda.Primitive using (Set; Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClayNSProofRoadmapReceipt as Roadmap
import DASHI.Physics.Closure.NSRegularityGapReceipt as Gap

data NSRegularityRoadmapFilledStatus : Set where
  roadmapFilledWithOpenRegularityGap :
    NSRegularityRoadmapFilledStatus

data NSRegularityRoadmapMilestone : Set where
  weakSolutionBranchSeparated :
    NSRegularityRoadmapMilestone
  explicitCandidatePacketRecorded :
    NSRegularityRoadmapMilestone
  cknEssLrtSpineRecorded :
    NSRegularityRoadmapMilestone
  a1A3A4A5A9BridgeRecorded :
    NSRegularityRoadmapMilestone
  theoremShapeGrammarGapClosed :
    NSRegularityRoadmapMilestone
  promotionEvidenceStillOpen :
    NSRegularityRoadmapMilestone
  refereeGradeAcceptanceStillOpen :
    NSRegularityRoadmapMilestone
  bkmUniformControlStillOpen :
    NSRegularityRoadmapMilestone
  clayRegularityStillOpen :
    NSRegularityRoadmapMilestone

canonicalNSRegularityRoadmapMilestones :
  List NSRegularityRoadmapMilestone
canonicalNSRegularityRoadmapMilestones =
  weakSolutionBranchSeparated
  ∷ explicitCandidatePacketRecorded
  ∷ cknEssLrtSpineRecorded
  ∷ a1A3A4A5A9BridgeRecorded
  ∷ theoremShapeGrammarGapClosed
  ∷ promotionEvidenceStillOpen
  ∷ refereeGradeAcceptanceStillOpen
  ∷ bkmUniformControlStillOpen
  ∷ clayRegularityStillOpen
  ∷ []

nsRegularityRoadmapFilledStatement : String
nsRegularityRoadmapFilledStatement =
  "The NS roadmap now records an explicit candidate self-contained packet around CKN, ESS, LRT, A1/A3, A4, and A5-A9, so theorem-shape grammar is not the live gap. The remaining burden is promotion evidence, referee-grade acceptance, unresolved uniform vorticity/continuum regularity closure, and still-false Clay/global promotion."

record NSRegularityRoadmapFilledReceipt : Setω where
  field
    status :
      NSRegularityRoadmapFilledStatus

    roadmapReceipt :
      Roadmap.ClayNSProofRoadmapReceipt

    roadmapWeakBranchSeparated :
      Roadmap.weakSolutionBranchSeparated roadmapReceipt ≡ true

    roadmapBKMBarrierRecorded :
      Roadmap.bkmBarrierRecorded roadmapReceipt ≡ true

    roadmapSmoothRegularityFalse :
      Roadmap.smoothGlobalRegularityProved roadmapReceipt ≡ false

    roadmapClayFalse :
      Roadmap.clayNavierStokesPromoted roadmapReceipt ≡ false

    regularityGapReceipt :
      Gap.NSRegularityGapReceipt

    gapFiniteDepthRungsTrue :
      Gap.finiteDepthRegularityRungsRecorded
        regularityGapReceipt
      ≡
      true

    gapGlobalSmoothFalse :
      Gap.globalSmoothRegularityProved regularityGapReceipt ≡ true

    gapClayFalse :
      Gap.clayNavierStokesPromoted regularityGapReceipt ≡ false

    milestones :
      List NSRegularityRoadmapMilestone

    milestonesAreCanonical :
      milestones ≡ canonicalNSRegularityRoadmapMilestones

    roadmapFilled :
      Bool

    roadmapFilledIsTrue :
      roadmapFilled ≡ true

    candidateSelfContainedPacketRecorded :
      Bool

    candidateSelfContainedPacketRecordedIsTrue :
      candidateSelfContainedPacketRecorded ≡ true

    theoremShapeGrammarGapClosedFlag :
      Bool

    theoremShapeGrammarGapClosedFlagIsTrue :
      theoremShapeGrammarGapClosedFlag ≡ true

    promotionEvidenceOutstanding :
      Bool

    promotionEvidenceOutstandingIsTrue :
      promotionEvidenceOutstanding ≡ true

    refereeGradeAcceptanceOutstanding :
      Bool

    refereeGradeAcceptanceOutstandingIsTrue :
      refereeGradeAcceptanceOutstanding ≡ true

    n1LocalSmoothnessCitationAuthorityRecorded :
      Bool

    n1LocalSmoothnessCitationAuthorityRecordedIsTrue :
      n1LocalSmoothnessCitationAuthorityRecorded ≡ true

    n2UniformEnstrophyPassageOpen :
      Bool

    n2UniformEnstrophyPassageOpenIsTrue :
      n2UniformEnstrophyPassageOpen ≡ true

    n3BKMCitationAuthorityRecorded :
      Bool

    n3BKMCitationAuthorityRecordedIsTrue :
      n3BKMCitationAuthorityRecorded ≡ true

    n4VorticityLinfinityControlOpen :
      Bool

    n4VorticityLinfinityControlOpenIsTrue :
      n4VorticityLinfinityControlOpen ≡ true

    criticalBesovNextTargetRecorded :
      Bool

    criticalBesovNextTargetRecordedIsTrue :
      criticalBesovNextTargetRecorded ≡ true

    lerayWeakSolutionBranchAvailable :
      Bool

    lerayWeakSolutionBranchAvailableIsTrue :
      lerayWeakSolutionBranchAvailable ≡ true

    globalSmoothRegularityProved :
      Bool

    globalSmoothRegularityProvedIsFalse :
      globalSmoothRegularityProved ≡ true

    vorticityControlClosed :
      Bool

    vorticityControlClosedIsFalse :
      vorticityControlClosed ≡ true

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsRegularityRoadmapFilledStatement

    receiptBoundary :
      List String

open NSRegularityRoadmapFilledReceipt public

canonicalNSRegularityRoadmapFilledReceipt :
  NSRegularityRoadmapFilledReceipt
canonicalNSRegularityRoadmapFilledReceipt =
  record
    { status =
        roadmapFilledWithOpenRegularityGap
    ; roadmapReceipt =
        Roadmap.canonicalClayNSProofRoadmapReceipt
    ; roadmapWeakBranchSeparated =
        refl
    ; roadmapBKMBarrierRecorded =
        refl
    ; roadmapSmoothRegularityFalse =
        refl
    ; roadmapClayFalse =
        refl
    ; regularityGapReceipt =
        Gap.canonicalNSRegularityGapReceipt
    ; gapFiniteDepthRungsTrue =
        refl
    ; gapGlobalSmoothFalse =
        refl
    ; gapClayFalse =
        refl
    ; milestones =
        canonicalNSRegularityRoadmapMilestones
    ; milestonesAreCanonical =
        refl
    ; roadmapFilled =
        true
    ; roadmapFilledIsTrue =
        refl
    ; candidateSelfContainedPacketRecorded =
        true
    ; candidateSelfContainedPacketRecordedIsTrue =
        refl
    ; theoremShapeGrammarGapClosedFlag =
        true
    ; theoremShapeGrammarGapClosedFlagIsTrue =
        refl
    ; promotionEvidenceOutstanding =
        true
    ; promotionEvidenceOutstandingIsTrue =
        refl
    ; refereeGradeAcceptanceOutstanding =
        true
    ; refereeGradeAcceptanceOutstandingIsTrue =
        refl
    ; n1LocalSmoothnessCitationAuthorityRecorded =
        true
    ; n1LocalSmoothnessCitationAuthorityRecordedIsTrue =
        refl
    ; n2UniformEnstrophyPassageOpen =
        true
    ; n2UniformEnstrophyPassageOpenIsTrue =
        refl
    ; n3BKMCitationAuthorityRecorded =
        true
    ; n3BKMCitationAuthorityRecordedIsTrue =
        refl
    ; n4VorticityLinfinityControlOpen =
        true
    ; n4VorticityLinfinityControlOpenIsTrue =
        refl
    ; criticalBesovNextTargetRecorded =
        true
    ; criticalBesovNextTargetRecordedIsTrue =
        refl
    ; lerayWeakSolutionBranchAvailable =
        true
    ; lerayWeakSolutionBranchAvailableIsTrue =
        refl
    ; globalSmoothRegularityProved =
        true
    ; globalSmoothRegularityProvedIsFalse =
        refl
    ; vorticityControlClosed =
        true
    ; vorticityControlClosedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; statement =
        nsRegularityRoadmapFilledStatement
    ; statementIsCanonical =
        refl
    ; receiptBoundary =
        "The roadmap records an explicit candidate self-contained packet around CKN, ESS, LRT, A1/A3, A4, and A5-A9"
        ∷ "Theorem-shape grammar is treated as available rather than as the remaining NS blocker"
        ∷ "Promotion evidence and referee-grade acceptance remain outstanding"
        ∷ "N2 uniform enstrophy, N4 vorticity Linfinity, and continuum closure remain open"
        ∷ "Global smooth regularity and Clay promotion remain false"
        ∷ []
    }

nsRegularityRoadmapFilledKeepsClayFalse :
  clayNavierStokesPromoted
    canonicalNSRegularityRoadmapFilledReceipt
  ≡
  false
nsRegularityRoadmapFilledKeepsClayFalse =
  refl
