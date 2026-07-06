module DASHI.Physics.Closure.NSClaySubmissionEligibilityRoadmapReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClayMillenniumClosureTargetReceipt as Clay
import DASHI.Physics.Closure.NSCarrierToAllDataReceipt as AllData
import DASHI.Physics.Closure.NSCarrierVsClayGapReceipt as CarrierGap
import DASHI.Physics.Closure.ClayNSProofRoadmapReceipt as Roadmap
import DASHI.Physics.Closure.NSFullClayGatewayTheoremBoundaryReceipt as Gateway
import DASHI.Physics.Closure.NSTriadKNGate1SignedDominationReceipt as Gate1
import DASHI.Physics.Closure.NSTriadKNGate2SeamToLeakageTransferReceipt as Gate2
import DASHI.Physics.Closure.NSTriadKNExactOperatorFrontierReceipt as Frontier
import DASHI.Physics.Closure.NSThetaTailToBKMBridgeReceipt as BKM

------------------------------------------------------------------------
-- End-to-end NS roadmap from current proof state to submission and
-- external Clay eligibility.
--
-- This is a roadmap receipt only. It records the minimal honest dependency
-- ladder and the exact repo surfaces that must flip before the route reaches
-- theorem closure, submission readiness, and then external Clay eligibility.

data NSClayRoadmapStage : Set where
  gate1UniformSeamTheorem :
    NSClayRoadmapStage
  gate2ExactOperatorTransfer :
    NSClayRoadmapStage
  exactOperatorFrontierToBKM :
    NSClayRoadmapStage
  continuumBKMPassage :
    NSClayRoadmapStage
  carrierToAllDataBridge :
    NSClayRoadmapStage
  fullClayGatewayTheorem :
    NSClayRoadmapStage
  submissionPacketReadiness :
    NSClayRoadmapStage
  externalClayEligibility :
    NSClayRoadmapStage

canonicalNSClayRoadmapStages : List NSClayRoadmapStage
canonicalNSClayRoadmapStages =
  gate1UniformSeamTheorem
  ∷ gate2ExactOperatorTransfer
  ∷ exactOperatorFrontierToBKM
  ∷ continuumBKMPassage
  ∷ carrierToAllDataBridge
  ∷ fullClayGatewayTheorem
  ∷ submissionPacketReadiness
  ∷ externalClayEligibility
  ∷ []

data NSClayRoadmapBlocker : Set where
  exactOperatorCNResidueBKMFrontierStillOpen :
    NSClayRoadmapBlocker
  continuumBKMPassageStillOpen :
    NSClayRoadmapBlocker
  allDataBridgeStillOpen :
    NSClayRoadmapBlocker
  fullGatewaySignOrBackwardsUniquenessStillOpen :
    NSClayRoadmapBlocker
  submissionPublicationAuthorityStillExternal :
    NSClayRoadmapBlocker

data NSClayRoadmapImmediateTarget : Set where
  pairIncidenceCNTheoremFirst :
    NSClayRoadmapImmediateTarget

canonicalNSClayRoadmapBlockers : List NSClayRoadmapBlocker
canonicalNSClayRoadmapBlockers =
  exactOperatorCNResidueBKMFrontierStillOpen
  ∷ continuumBKMPassageStillOpen
  ∷ allDataBridgeStillOpen
  ∷ fullGatewaySignOrBackwardsUniquenessStillOpen
  ∷ submissionPublicationAuthorityStillExternal
  ∷ []

roadmapDocPath : String
roadmapDocPath =
  "docs/ns_clay_submission_eligibility_roadmap.md"

roadmapStatement : String
roadmapStatement =
  "NS Clay route: Gate 1 uniform theorem -> exact Gate 2 K_N(A) transfer -> exact-operator frontier -> continuum BKM/global-regularity passage -> all-data bridge -> full Clay gateway theorem -> submission packet -> external publication/two-year/community-acceptance path."

roadmapImmediateTargetStatement : String
roadmapImmediateTargetStatement =
  "Immediate live NS target: prove PairIncidenceCNTheorem, namely ||L_FT,script^N||_op <= C / N, as the first exact-operator frontier theorem after the closed Gate 2 transfer."

record NSClaySubmissionEligibilityRoadmapReceipt : Setω where
  field
    gate1Receipt :
      Gate1.NSTriadKNGate1SignedDominationReceipt
    gate1Closed :
      Gate1.gate1ConditionalTheoremProved gate1Receipt ≡ true

    gate2Receipt :
      Gate2.NSTriadKNGate2SeamToLeakageTransferReceipt
    gate2ExactTransferClosed :
      Gate2.gate2ExactTransferConditionalTheoremProved gate2Receipt ≡ true

    exactOperatorFrontierReceipt :
      Frontier.NSTriadKNExactOperatorFrontierReceipt
    exactOperatorFrontierStillOpen :
      Frontier.bkmResidenceBridgeClosed exactOperatorFrontierReceipt ≡ false

    thetaTailToBKMReceipt :
      BKM.NSThetaTailToBKMBridgeReceipt zero
    continuumBKMPassageReceiptStillOpen :
      BKM.bkmCriterionDischarged thetaTailToBKMReceipt ≡ false

    carrierGapReceipt :
      CarrierGap.NSCarrierVsClayGapReceipt
    carrierGapStillOpen :
      CarrierGap.densityClosedHere carrierGapReceipt ≡ false

    allDataReceipt :
      AllData.NSCarrierToAllDataReceipt
    allDataStillConditional :
      AllData.clayNavierStokesPromoted allDataReceipt ≡ false

    clayTargetReceipt :
      Clay.CarrierBKMControlTargetReceipt
    clayTargetStillOpen :
      Clay.clayNavierStokesClosed clayTargetReceipt ≡ false

    gatewayReceipt :
      Gateway.NSFullClayGatewayTheoremBoundaryReceipt
    fullGatewayStillOpen :
      Gateway.fullClayNSPromoted ≡ false

    roadmapReceipt :
      Roadmap.ClayNSProofRoadmapReceipt
    roadmapClayStillFalse :
      Roadmap.clayNavierStokesPromoted roadmapReceipt ≡ false

    docPath :
      String
    docPathIsCanonical :
      docPath ≡ roadmapDocPath

    statement :
      String
    statementIsCanonical :
      statement ≡ roadmapStatement

    stages :
      List NSClayRoadmapStage
    stagesAreCanonical :
      stages ≡ canonicalNSClayRoadmapStages

    blockers :
      List NSClayRoadmapBlocker
    blockersAreCanonical :
      blockers ≡ canonicalNSClayRoadmapBlockers

    immediateTarget :
      NSClayRoadmapImmediateTarget
    immediateTargetIsCanonical :
      immediateTarget ≡ pairIncidenceCNTheoremFirst

    immediateTargetStatement :
      String
    immediateTargetStatementIsCanonical :
      immediateTargetStatement ≡ roadmapImmediateTargetStatement

    seamLocalGate2ModelClosed :
      Bool
    seamLocalGate2ModelClosedIsTrue :
      seamLocalGate2ModelClosed ≡ true

    exactGate2Closed :
      Bool
    exactGate2ClosedIsTrue :
      exactGate2Closed ≡ true

    continuumBKMPassageConstructed :
      Bool
    continuumBKMPassageConstructedIsFalse :
      continuumBKMPassageConstructed ≡ false

    allDataBridgeConstructed :
      Bool
    allDataBridgeConstructedIsFalse :
      allDataBridgeConstructed ≡ false

    submissionPacketReady :
      Bool
    submissionPacketReadyIsFalse :
      submissionPacketReady ≡ false

    qualifyingPublicationAvailable :
      Bool
    qualifyingPublicationAvailableIsFalse :
      qualifyingPublicationAvailable ≡ false

    twoYearWaitingPeriodElapsed :
      Bool
    twoYearWaitingPeriodElapsedIsFalse :
      twoYearWaitingPeriodElapsed ≡ false

    broadCommunityAcceptance :
      Bool
    broadCommunityAcceptanceIsFalse :
      broadCommunityAcceptance ≡ false

    clayEligible :
      Bool
    clayEligibleIsFalse :
      clayEligible ≡ false

open NSClaySubmissionEligibilityRoadmapReceipt public

canonicalNSClaySubmissionEligibilityRoadmapReceipt :
  NSClaySubmissionEligibilityRoadmapReceipt
canonicalNSClaySubmissionEligibilityRoadmapReceipt =
  record
    { gate1Receipt =
        Gate1.canonicalNSTriadKNGate1SignedDominationReceipt
    ; gate1Closed =
        refl
    ; gate2Receipt =
        Gate2.canonicalNSTriadKNGate2SeamToLeakageTransferReceipt
    ; gate2ExactTransferClosed =
        refl
    ; exactOperatorFrontierReceipt =
        Frontier.canonicalNSTriadKNExactOperatorFrontierReceipt
    ; exactOperatorFrontierStillOpen =
        refl
    ; thetaTailToBKMReceipt =
        BKM.canonicalNSThetaTailToBKMBridgeReceipt
    ; continuumBKMPassageReceiptStillOpen =
        refl
    ; carrierGapReceipt =
        CarrierGap.canonicalNSCarrierVsClayGapReceipt
    ; carrierGapStillOpen =
        refl
    ; allDataReceipt =
        AllData.canonicalNSCarrierToAllDataReceipt
    ; allDataStillConditional =
        refl
    ; clayTargetReceipt =
        Clay.canonicalCarrierBKMControlTargetReceipt
    ; clayTargetStillOpen =
        refl
    ; gatewayReceipt =
        Gateway.canonicalNSFullClayGatewayTheoremBoundaryReceipt
    ; fullGatewayStillOpen =
        refl
    ; roadmapReceipt =
        Roadmap.canonicalClayNSProofRoadmapReceipt
    ; roadmapClayStillFalse =
        refl
    ; docPath =
        roadmapDocPath
    ; docPathIsCanonical =
        refl
    ; statement =
        roadmapStatement
    ; statementIsCanonical =
        refl
    ; stages =
        canonicalNSClayRoadmapStages
    ; stagesAreCanonical =
        refl
    ; blockers =
        canonicalNSClayRoadmapBlockers
    ; blockersAreCanonical =
        refl
    ; immediateTarget =
        pairIncidenceCNTheoremFirst
    ; immediateTargetIsCanonical =
        refl
    ; immediateTargetStatement =
        roadmapImmediateTargetStatement
    ; immediateTargetStatementIsCanonical =
        refl
    ; seamLocalGate2ModelClosed =
        true
    ; seamLocalGate2ModelClosedIsTrue =
        refl
    ; exactGate2Closed =
        true
    ; exactGate2ClosedIsTrue =
        refl
    ; continuumBKMPassageConstructed =
        false
    ; continuumBKMPassageConstructedIsFalse =
        refl
    ; allDataBridgeConstructed =
        false
    ; allDataBridgeConstructedIsFalse =
        refl
    ; submissionPacketReady =
        false
    ; submissionPacketReadyIsFalse =
        refl
    ; qualifyingPublicationAvailable =
        false
    ; qualifyingPublicationAvailableIsFalse =
        refl
    ; twoYearWaitingPeriodElapsed =
        false
    ; twoYearWaitingPeriodElapsedIsFalse =
        refl
    ; broadCommunityAcceptance =
        false
    ; broadCommunityAcceptanceIsFalse =
        refl
    ; clayEligible =
        false
    ; clayEligibleIsFalse =
        refl
    }
