module DASHI.Physics.Closure.NSClayHardWallCompletionRoadmapReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Hard-wall completion roadmap receipt for the Clay packet.
--
-- This module is a fail-closed receipt only.  It lists the remaining
-- dependency ladder from the current NS/Clay state to a submittable Clay
-- packet, but it does not claim that any hard analytic gate is already
-- discharged.  The current projection is intentionally conservative:
-- claySubmittable remains false until every hard analytic gate is true.

listLength : ∀ {A : Set} → List A → Nat
listLength [] = zero
listLength (_ ∷ xs) = suc (listLength xs)

andBool : Bool → Bool → Bool
andBool true true = true
andBool _ _ = false

------------------------------------------------------------------------
-- Dependency ladder.

data NSClayHardWallRoadmapStep : Set where
  RepoHygieneStagedChangeIsolation :
    NSClayHardWallRoadmapStep
  CloseablePackageChecksCompleteAt3ce9beb5 :
    NSClayHardWallRoadmapStep
  ConditionalKornLevelSetPacket :
    NSClayHardWallRoadmapStep
  HOmegaCtrlFromNSAlone :
    NSClayHardWallRoadmapStep
  CollapseRatioDerivativeComputation :
    NSClayHardWallRoadmapStep
  QTGronwallClosure :
    NSClayHardWallRoadmapStep
  BoundarySobolevLift :
    NSClayHardWallRoadmapStep
  CollapseImpossibleTheorem :
    NSClayHardWallRoadmapStep
  IntegrateHardWallsIntoNSClayPostCalc11StateAggregation :
    NSClayHardWallRoadmapStep
  IntegrateHardWallsIntoNSFullClayGateway :
    NSClayHardWallRoadmapStep
  StandardLanguageWriteup :
    NSClayHardWallRoadmapStep
  ExternalReviewPacket :
    NSClayHardWallRoadmapStep
  TrackBCheck :
    NSClayHardWallRoadmapStep
  TrackAAuthoritativeCheck :
    NSClayHardWallRoadmapStep
  SubmissionPacket :
    NSClayHardWallRoadmapStep

canonicalNSClayHardWallRoadmapSteps : List NSClayHardWallRoadmapStep
canonicalNSClayHardWallRoadmapSteps =
  RepoHygieneStagedChangeIsolation
  ∷ CloseablePackageChecksCompleteAt3ce9beb5
  ∷ ConditionalKornLevelSetPacket
  ∷ HOmegaCtrlFromNSAlone
  ∷ CollapseRatioDerivativeComputation
  ∷ QTGronwallClosure
  ∷ BoundarySobolevLift
  ∷ CollapseImpossibleTheorem
  ∷ IntegrateHardWallsIntoNSClayPostCalc11StateAggregation
  ∷ IntegrateHardWallsIntoNSFullClayGateway
  ∷ StandardLanguageWriteup
  ∷ ExternalReviewPacket
  ∷ TrackBCheck
  ∷ TrackAAuthoritativeCheck
  ∷ SubmissionPacket
  ∷ []

stepLabel : NSClayHardWallRoadmapStep → String
stepLabel RepoHygieneStagedChangeIsolation =
  "repo hygiene and staged-change isolation"
stepLabel CloseablePackageChecksCompleteAt3ce9beb5 =
  "closeable package checks complete at 3ce9beb5"
stepLabel ConditionalKornLevelSetPacket =
  "conditional KornLevelSet packet"
stepLabel HOmegaCtrlFromNSAlone =
  "h_omega_ctrl from NS alone"
stepLabel CollapseRatioDerivativeComputation =
  "collapse ratio derivative computation"
stepLabel QTGronwallClosure =
  "Q(t) Gronwall closure"
stepLabel BoundarySobolevLift =
  "boundary Sobolev lift"
stepLabel CollapseImpossibleTheorem =
  "collapseImpossible theorem"
stepLabel IntegrateHardWallsIntoNSClayPostCalc11StateAggregation =
  "integrate hard walls into NSClayPostCalc11StateAggregation"
stepLabel IntegrateHardWallsIntoNSFullClayGateway =
  "integrate hard walls into NSFullClayGateway"
stepLabel StandardLanguageWriteup =
  "standard-language writeup"
stepLabel ExternalReviewPacket =
  "external review packet"
stepLabel TrackBCheck =
  "Track B check"
stepLabel TrackAAuthoritativeCheck =
  "Track A authoritative check"
stepLabel SubmissionPacket =
  "submission packet"

canonicalNSClayHardWallRoadmapStepLabels :
  List String
canonicalNSClayHardWallRoadmapStepLabels =
  "repo hygiene and staged-change isolation"
  ∷ "closeable package checks complete at 3ce9beb5"
  ∷ "conditional KornLevelSet packet"
  ∷ "h_omega_ctrl from NS alone"
  ∷ "collapse ratio derivative computation"
  ∷ "Q(t) Gronwall closure"
  ∷ "boundary Sobolev lift"
  ∷ "collapseImpossible theorem"
  ∷ "integrate hard walls into NSClayPostCalc11StateAggregation"
  ∷ "integrate hard walls into NSFullClayGateway"
  ∷ "standard-language writeup"
  ∷ "external review packet"
  ∷ "Track B check"
  ∷ "Track A authoritative check"
  ∷ "submission packet"
  ∷ []

canonicalNSClayHardWallRoadmapStepCount : Nat
canonicalNSClayHardWallRoadmapStepCount =
  listLength canonicalNSClayHardWallRoadmapSteps

------------------------------------------------------------------------
-- Hard analytic gates.

data NSClayHardAnalyticGate : Set where
  ConditionalKornLevelSetGate :
    NSClayHardAnalyticGate
  HOmegaCtrlFromNSAloneGate :
    NSClayHardAnalyticGate
  CollapseRatioDerivativeComputationGate :
    NSClayHardAnalyticGate
  QTGronwallClosureGate :
    NSClayHardAnalyticGate
  BoundarySobolevLiftGate :
    NSClayHardAnalyticGate
  CollapseImpossibleTheoremGate :
    NSClayHardAnalyticGate

canonicalNSClayHardAnalyticGates : List NSClayHardAnalyticGate
canonicalNSClayHardAnalyticGates =
  ConditionalKornLevelSetGate
  ∷ HOmegaCtrlFromNSAloneGate
  ∷ CollapseRatioDerivativeComputationGate
  ∷ QTGronwallClosureGate
  ∷ BoundarySobolevLiftGate
  ∷ CollapseImpossibleTheoremGate
  ∷ []

hardAnalyticGateLabel : NSClayHardAnalyticGate → String
hardAnalyticGateLabel ConditionalKornLevelSetGate =
  "conditional KornLevelSet packet"
hardAnalyticGateLabel HOmegaCtrlFromNSAloneGate =
  "h_omega_ctrl from NS alone"
hardAnalyticGateLabel CollapseRatioDerivativeComputationGate =
  "collapse ratio derivative computation"
hardAnalyticGateLabel QTGronwallClosureGate =
  "Q(t) Gronwall closure"
hardAnalyticGateLabel BoundarySobolevLiftGate =
  "boundary Sobolev lift"
hardAnalyticGateLabel CollapseImpossibleTheoremGate =
  "collapseImpossible theorem"

canonicalNSClayHardAnalyticGateLabels :
  List String
canonicalNSClayHardAnalyticGateLabels =
  "conditional KornLevelSet packet"
  ∷ "h_omega_ctrl from NS alone"
  ∷ "collapse ratio derivative computation"
  ∷ "Q(t) Gronwall closure"
  ∷ "boundary Sobolev lift"
  ∷ "collapseImpossible theorem"
  ∷ []

canonicalNSClayHardAnalyticGateCount : Nat
canonicalNSClayHardAnalyticGateCount =
  listLength canonicalNSClayHardAnalyticGates

------------------------------------------------------------------------
-- Progress state.  Every field is fail-closed here.

record NSClayHardWallCompletionRoadmapProgressState : Set where
  field
    repoHygieneStagedChangeIsolation :
      Bool
    repoHygieneStagedChangeIsolationIsFalse :
      repoHygieneStagedChangeIsolation ≡ false

    closeablePackageChecksCompleteAt3ce9beb5 :
      Bool
    closeablePackageChecksCompleteAt3ce9beb5IsFalse :
      closeablePackageChecksCompleteAt3ce9beb5 ≡ false

    conditionalKornLevelSetPacket :
      Bool
    conditionalKornLevelSetPacketIsFalse :
      conditionalKornLevelSetPacket ≡ false

    hOmegaCtrlFromNSAlone :
      Bool
    hOmegaCtrlFromNSAloneIsFalse :
      hOmegaCtrlFromNSAlone ≡ false

    collapseRatioDerivativeComputation :
      Bool
    collapseRatioDerivativeComputationIsFalse :
      collapseRatioDerivativeComputation ≡ false

    qtGronwallClosure :
      Bool
    qtGronwallClosureIsFalse :
      qtGronwallClosure ≡ false

    boundarySobolevLift :
      Bool
    boundarySobolevLiftIsFalse :
      boundarySobolevLift ≡ false

    collapseImpossibleTheorem :
      Bool
    collapseImpossibleTheoremIsFalse :
      collapseImpossibleTheorem ≡ false

    integrateHardWallsIntoNSClayPostCalc11StateAggregation :
      Bool
    integrateHardWallsIntoNSClayPostCalc11StateAggregationIsFalse :
      integrateHardWallsIntoNSClayPostCalc11StateAggregation ≡ false

    integrateHardWallsIntoNSFullClayGateway :
      Bool
    integrateHardWallsIntoNSFullClayGatewayIsFalse :
      integrateHardWallsIntoNSFullClayGateway ≡ false

    standardLanguageWriteup :
      Bool
    standardLanguageWriteupIsFalse :
      standardLanguageWriteup ≡ false

    externalReviewPacket :
      Bool
    externalReviewPacketIsFalse :
      externalReviewPacket ≡ false

    trackBCheck :
      Bool
    trackBCheckIsFalse :
      trackBCheck ≡ false

    trackAAuthoritativeCheck :
      Bool
    trackAAuthoritativeCheckIsFalse :
      trackAAuthoritativeCheck ≡ false

    submissionPacket :
      Bool
    submissionPacketIsFalse :
      submissionPacket ≡ false

    allHardAnalyticGatesTrue :
      Bool
    allHardAnalyticGatesTrueIsFalse :
      allHardAnalyticGatesTrue ≡ false

    claySubmittable :
      Bool
    claySubmittableIsFalse :
      claySubmittable ≡ false

open NSClayHardWallCompletionRoadmapProgressState public

canonicalNSClayHardWallCompletionRoadmapProgressState :
  NSClayHardWallCompletionRoadmapProgressState
canonicalNSClayHardWallCompletionRoadmapProgressState =
  record
    { repoHygieneStagedChangeIsolation = false
    ; repoHygieneStagedChangeIsolationIsFalse = refl
    ; closeablePackageChecksCompleteAt3ce9beb5 = false
    ; closeablePackageChecksCompleteAt3ce9beb5IsFalse = refl
    ; conditionalKornLevelSetPacket = false
    ; conditionalKornLevelSetPacketIsFalse = refl
    ; hOmegaCtrlFromNSAlone = false
    ; hOmegaCtrlFromNSAloneIsFalse = refl
    ; collapseRatioDerivativeComputation = false
    ; collapseRatioDerivativeComputationIsFalse = refl
    ; qtGronwallClosure = false
    ; qtGronwallClosureIsFalse = refl
    ; boundarySobolevLift = false
    ; boundarySobolevLiftIsFalse = refl
    ; collapseImpossibleTheorem = false
    ; collapseImpossibleTheoremIsFalse = refl
    ; integrateHardWallsIntoNSClayPostCalc11StateAggregation = false
    ; integrateHardWallsIntoNSClayPostCalc11StateAggregationIsFalse = refl
    ; integrateHardWallsIntoNSFullClayGateway = false
    ; integrateHardWallsIntoNSFullClayGatewayIsFalse = refl
    ; standardLanguageWriteup = false
    ; standardLanguageWriteupIsFalse = refl
    ; externalReviewPacket = false
    ; externalReviewPacketIsFalse = refl
    ; trackBCheck = false
    ; trackBCheckIsFalse = refl
    ; trackAAuthoritativeCheck = false
    ; trackAAuthoritativeCheckIsFalse = refl
    ; submissionPacket = false
    ; submissionPacketIsFalse = refl
    ; allHardAnalyticGatesTrue = false
    ; allHardAnalyticGatesTrueIsFalse = refl
    ; claySubmittable = false
    ; claySubmittableIsFalse = refl
    }

------------------------------------------------------------------------
-- Receipt record.

record NSClayHardWallCompletionRoadmapReceipt : Setω where
  field
    referenceCommit :
      String
    referenceCommitIsCanonical :
      referenceCommit ≡ "3ce9beb5"

    progressState :
      NSClayHardWallCompletionRoadmapProgressState
    progressStateIsCanonical :
      progressState ≡ canonicalNSClayHardWallCompletionRoadmapProgressState

    dependencyLadder :
      List NSClayHardWallRoadmapStep
    dependencyLadderIsCanonical :
      dependencyLadder ≡ canonicalNSClayHardWallRoadmapSteps

    dependencyLadderLabels :
      List String
    dependencyLadderLabelsIsCanonical :
      dependencyLadderLabels ≡ canonicalNSClayHardWallRoadmapStepLabels

    hardAnalyticGates :
      List NSClayHardAnalyticGate
    hardAnalyticGatesIsCanonical :
      hardAnalyticGates ≡ canonicalNSClayHardAnalyticGates

    hardAnalyticGateLabels :
      List String
    hardAnalyticGateLabelsIsCanonical :
      hardAnalyticGateLabels ≡ canonicalNSClayHardAnalyticGateLabels

    dependencyLadderCount :
      Nat
    dependencyLadderCountIsCanonical :
      dependencyLadderCount ≡ canonicalNSClayHardWallRoadmapStepCount

    hardAnalyticGateCount :
      Nat
    hardAnalyticGateCountIsCanonical :
      hardAnalyticGateCount ≡ canonicalNSClayHardAnalyticGateCount

    projectRepoHygieneStagedChangeIsolationFalse :
      repoHygieneStagedChangeIsolation progressState ≡ false

    projectCloseablePackageChecksCompleteAt3ce9beb5False :
      closeablePackageChecksCompleteAt3ce9beb5 progressState ≡ false

    projectConditionalKornLevelSetPacketFalse :
      conditionalKornLevelSetPacket progressState ≡ false

    projectHOmegaCtrlFromNSAloneFalse :
      hOmegaCtrlFromNSAlone progressState ≡ false

    projectCollapseRatioDerivativeComputationFalse :
      collapseRatioDerivativeComputation progressState ≡ false

    projectQTGronwallClosureFalse :
      qtGronwallClosure progressState ≡ false

    projectBoundarySobolevLiftFalse :
      boundarySobolevLift progressState ≡ false

    projectCollapseImpossibleTheoremFalse :
      collapseImpossibleTheorem progressState ≡ false

    projectIntegrateHardWallsIntoNSClayPostCalc11StateAggregationFalse :
      integrateHardWallsIntoNSClayPostCalc11StateAggregation progressState ≡ false

    projectIntegrateHardWallsIntoNSFullClayGatewayFalse :
      integrateHardWallsIntoNSFullClayGateway progressState ≡ false

    projectStandardLanguageWriteupFalse :
      standardLanguageWriteup progressState ≡ false

    projectExternalReviewPacketFalse :
      externalReviewPacket progressState ≡ false

    projectTrackBCheckFalse :
      trackBCheck progressState ≡ false

    projectTrackAAuthoritativeCheckFalse :
      trackAAuthoritativeCheck progressState ≡ false

    projectSubmissionPacketFalse :
      submissionPacket progressState ≡ false

    projectAllHardAnalyticGatesTrueFalse :
      allHardAnalyticGatesTrue progressState ≡ false

    projectClaySubmittableFalse :
      claySubmittable progressState ≡ false

    receiptText :
      String
    receiptTextIsCanonical :
      receiptText ≡
      "Fail-closed Clay packet roadmap receipt: repo hygiene and the 3ce9beb5 closeable-package checkpoint are recorded as required dependencies, but the hard analytic gates remain open; claySubmittable stays false until the conditional KornLevelSet packet, h_omega_ctrl from NS alone, collapse ratio derivative computation, Q(t) Gronwall closure, boundary Sobolev lift, and collapseImpossible theorem are all true, and the integration, writeup, review, Track B, Track A, and submission steps are still downstream."

    statusText :
      String
    statusTextIsCanonical :
      statusText ≡
      "Tracking only: no completion claim, no Clay submission claim, and no authoritative Track A discharge are made here."

open NSClayHardWallCompletionRoadmapReceipt public

canonicalNSClayHardWallCompletionRoadmapReceipt :
  NSClayHardWallCompletionRoadmapReceipt
canonicalNSClayHardWallCompletionRoadmapReceipt =
  record
    { referenceCommit = "3ce9beb5"
    ; referenceCommitIsCanonical = refl
    ; progressState = canonicalNSClayHardWallCompletionRoadmapProgressState
    ; progressStateIsCanonical = refl
    ; dependencyLadder = canonicalNSClayHardWallRoadmapSteps
    ; dependencyLadderIsCanonical = refl
    ; dependencyLadderLabels = canonicalNSClayHardWallRoadmapStepLabels
    ; dependencyLadderLabelsIsCanonical = refl
    ; hardAnalyticGates = canonicalNSClayHardAnalyticGates
    ; hardAnalyticGatesIsCanonical = refl
    ; hardAnalyticGateLabels = canonicalNSClayHardAnalyticGateLabels
    ; hardAnalyticGateLabelsIsCanonical = refl
    ; dependencyLadderCount = canonicalNSClayHardWallRoadmapStepCount
    ; dependencyLadderCountIsCanonical = refl
    ; hardAnalyticGateCount = canonicalNSClayHardAnalyticGateCount
    ; hardAnalyticGateCountIsCanonical = refl
    ; projectRepoHygieneStagedChangeIsolationFalse = refl
    ; projectCloseablePackageChecksCompleteAt3ce9beb5False = refl
    ; projectConditionalKornLevelSetPacketFalse = refl
    ; projectHOmegaCtrlFromNSAloneFalse = refl
    ; projectCollapseRatioDerivativeComputationFalse = refl
    ; projectQTGronwallClosureFalse = refl
    ; projectBoundarySobolevLiftFalse = refl
    ; projectCollapseImpossibleTheoremFalse = refl
    ; projectIntegrateHardWallsIntoNSClayPostCalc11StateAggregationFalse = refl
    ; projectIntegrateHardWallsIntoNSFullClayGatewayFalse = refl
    ; projectStandardLanguageWriteupFalse = refl
    ; projectExternalReviewPacketFalse = refl
    ; projectTrackBCheckFalse = refl
    ; projectTrackAAuthoritativeCheckFalse = refl
    ; projectSubmissionPacketFalse = refl
    ; projectAllHardAnalyticGatesTrueFalse = refl
    ; projectClaySubmittableFalse = refl
    ; receiptText =
        "Fail-closed Clay packet roadmap receipt: repo hygiene and the 3ce9beb5 closeable-package checkpoint are recorded as required dependencies, but the hard analytic gates remain open; claySubmittable stays false until the conditional KornLevelSet packet, h_omega_ctrl from NS alone, collapse ratio derivative computation, Q(t) Gronwall closure, boundary Sobolev lift, and collapseImpossible theorem are all true, and the integration, writeup, review, Track B, Track A, and submission steps are still downstream."
    ; receiptTextIsCanonical = refl
    ; statusText =
        "Tracking only: no completion claim, no Clay submission claim, and no authoritative Track A discharge are made here."
    ; statusTextIsCanonical = refl
    }

------------------------------------------------------------------------
-- Projection lemmas for the current canonical receipt surface.

claySubmittableFalseUntilAllHardAnalyticGatesAreTrue :
  claySubmittable canonicalNSClayHardWallCompletionRoadmapProgressState ≡ false
claySubmittableFalseUntilAllHardAnalyticGatesAreTrue = refl

hardAnalyticGatesRemainOpen :
  allHardAnalyticGatesTrue canonicalNSClayHardWallCompletionRoadmapProgressState ≡ false
hardAnalyticGatesRemainOpen = refl

repoHygieneRemainsFalse :
  repoHygieneStagedChangeIsolation canonicalNSClayHardWallCompletionRoadmapProgressState ≡ false
repoHygieneRemainsFalse = refl

closeablePackageCheckRemainsFalse :
  closeablePackageChecksCompleteAt3ce9beb5 canonicalNSClayHardWallCompletionRoadmapProgressState ≡ false
closeablePackageCheckRemainsFalse = refl

conditionalKornLevelSetRemainsFalse :
  conditionalKornLevelSetPacket canonicalNSClayHardWallCompletionRoadmapProgressState ≡ false
conditionalKornLevelSetRemainsFalse = refl

hOmegaCtrlRemainsFalse :
  hOmegaCtrlFromNSAlone canonicalNSClayHardWallCompletionRoadmapProgressState ≡ false
hOmegaCtrlRemainsFalse = refl

collapseRatioDerivativeRemainsFalse :
  collapseRatioDerivativeComputation canonicalNSClayHardWallCompletionRoadmapProgressState ≡ false
collapseRatioDerivativeRemainsFalse = refl

qtGronwallRemainsFalse :
  qtGronwallClosure canonicalNSClayHardWallCompletionRoadmapProgressState ≡ false
qtGronwallRemainsFalse = refl

boundarySobolevRemainsFalse :
  boundarySobolevLift canonicalNSClayHardWallCompletionRoadmapProgressState ≡ false
boundarySobolevRemainsFalse = refl

collapseImpossibleRemainsFalse :
  collapseImpossibleTheorem canonicalNSClayHardWallCompletionRoadmapProgressState ≡ false
collapseImpossibleRemainsFalse = refl

integrationIntoStateAggregationRemainsFalse :
  integrateHardWallsIntoNSClayPostCalc11StateAggregation canonicalNSClayHardWallCompletionRoadmapProgressState ≡ false
integrationIntoStateAggregationRemainsFalse = refl

integrationIntoGatewayRemainsFalse :
  integrateHardWallsIntoNSFullClayGateway canonicalNSClayHardWallCompletionRoadmapProgressState ≡ false
integrationIntoGatewayRemainsFalse = refl

standardLanguageWriteupRemainsFalse :
  standardLanguageWriteup canonicalNSClayHardWallCompletionRoadmapProgressState ≡ false
standardLanguageWriteupRemainsFalse = refl

externalReviewRemainsFalse :
  externalReviewPacket canonicalNSClayHardWallCompletionRoadmapProgressState ≡ false
externalReviewRemainsFalse = refl

trackBRemainsFalse :
  trackBCheck canonicalNSClayHardWallCompletionRoadmapProgressState ≡ false
trackBRemainsFalse = refl

trackARemainsFalse :
  trackAAuthoritativeCheck canonicalNSClayHardWallCompletionRoadmapProgressState ≡ false
trackARemainsFalse = refl

submissionRemainsFalse :
  submissionPacket canonicalNSClayHardWallCompletionRoadmapProgressState ≡ false
submissionRemainsFalse = refl
