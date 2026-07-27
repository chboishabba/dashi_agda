module DASHI.Biology.LongitudinalEngagementTrajectory where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)

import DASHI.Biology.OEFMultiFibreFeedbackHyperfabric as OEF

------------------------------------------------------------------------
-- Longitudinal OEF trajectory surface.
--
-- The source paper trains on one semester and tests on a later semester.
-- This is retained as a weak temporal transfer surface.  Repeated course or
-- cohort snapshots may support trajectory candidates, but observed change
-- does not promote itself to a causal redesign effect.

data Never : Set where

data EngagementTimePoint : Set where
  trainingSemester : EngagementTimePoint
  laterTestingSemester : EngagementTimePoint
  repeatedOffering : Nat → EngagementTimePoint

data TrajectoryScope : Set where
  courseTrajectoryScope : TrajectoryScope
  programmeTrajectoryScope : TrajectoryScope
  schoolTrajectoryScope : TrajectoryScope
  facultyTrajectoryScope : TrajectoryScope

record EngagementVectorSurface : Set where
  constructor mkEngagementVectorSurface
  field
    socialSignal : String
    cognitiveSignal : String
    behaviouralSignal : String
    collaborativeSignal : String
    emotionalSignal : String
    vectorReportedAsMatchedLongitudinalMeasure : Bool
    vectorReportedAsMatchedLongitudinalMeasureIsFalse :
      vectorReportedAsMatchedLongitudinalMeasure ≡ false
    vectorProxyOnly : Bool
    vectorProxyOnlyIsTrue : vectorProxyOnly ≡ true

open EngagementVectorSurface public

record EngagementSnapshot : Set where
  constructor mkEngagementSnapshot
  field
    snapshotLabel : String
    snapshotTime : EngagementTimePoint
    snapshotScope : TrajectoryScope
    snapshotFeedbackSentimentCount : Nat
    snapshotVector : EngagementVectorSurface
    snapshotConditionalOnResponse : Bool
    snapshotConditionalOnResponseIsTrue : snapshotConditionalOnResponse ≡ true
    snapshotAggregateOnly : Bool
    snapshotAggregateOnlyIsTrue : snapshotAggregateOnly ≡ true
    snapshotNotIndividualMeaning : Bool
    snapshotNotIndividualMeaningIsTrue : snapshotNotIndividualMeaning ≡ true

open EngagementSnapshot public

unreportedMatchedLongitudinalVector : EngagementVectorSurface
unreportedMatchedLongitudinalVector =
  mkEngagementVectorSurface
    "not reported as a matched longitudinal social measure"
    "not reported as a matched longitudinal cognitive measure"
    "not reported as a matched longitudinal behavioural measure"
    "not reported as a matched longitudinal collaborative measure"
    "not reported as a matched longitudinal emotional measure"
    false refl
    true refl

canonicalTrainingSnapshot : EngagementSnapshot
canonicalTrainingSnapshot =
  mkEngagementSnapshot
    "manually labelled training-semester feedback surface"
    trainingSemester
    courseTrajectoryScope
    383
    unreportedMatchedLongitudinalVector
    true refl
    true refl
    true refl

canonicalLaterTestingSnapshot : EngagementSnapshot
canonicalLaterTestingSnapshot =
  mkEngagementSnapshot
    "later-semester model-testing feedback surface"
    laterTestingSemester
    courseTrajectoryScope
    311
    unreportedMatchedLongitudinalVector
    true refl
    true refl
    true refl

record CausalDesignGate : Set where
  constructor mkCausalDesignGate
  field
    beforeAfterComparisonRequired : Bool
    beforeAfterComparisonRequiredIsTrue : beforeAfterComparisonRequired ≡ true
    cohortComparabilityRequired : Bool
    cohortComparabilityRequiredIsTrue : cohortComparabilityRequired ≡ true
    implementationReceiptRequired : Bool
    implementationReceiptRequiredIsTrue : implementationReceiptRequired ≡ true
    studentInterpretationRequired : Bool
    studentInterpretationRequiredIsTrue : studentInterpretationRequired ≡ true
    confoundAuditRequired : Bool
    confoundAuditRequiredIsTrue : confoundAuditRequired ≡ true
    replicationRequired : Bool
    replicationRequiredIsTrue : replicationRequired ≡ true

open CausalDesignGate public

canonicalCausalDesignGate : CausalDesignGate
canonicalCausalDesignGate =
  mkCausalDesignGate
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl

record EngagementTrajectoryCandidate : Set where
  constructor mkEngagementTrajectoryCandidate
  field
    trajectoryLabel : String
    baselineSnapshot : EngagementSnapshot
    followUpSnapshot : EngagementSnapshot
    trajectorySourceTransfer : Bool
    trajectorySourceTransferIsTrue : trajectorySourceTransfer ≡ true
    trajectoryProxyOnly : Bool
    trajectoryProxyOnlyIsTrue : trajectoryProxyOnly ≡ true
    trajectoryNotCausalEffect : Bool
    trajectoryNotCausalEffectIsTrue : trajectoryNotCausalEffect ≡ true
    trajectoryCausalGate : CausalDesignGate
    trajectoryNotes : List String

open EngagementTrajectoryCandidate public

canonicalEngagementTrajectoryCandidate : EngagementTrajectoryCandidate
canonicalEngagementTrajectoryCandidate =
  mkEngagementTrajectoryCandidate
    "OEF training-to-later-semester trajectory candidate"
    canonicalTrainingSnapshot
    canonicalLaterTestingSnapshot
    true refl
    true refl
    true refl
    canonicalCausalDesignGate
    ( "The model was trained on manually labelled feedback sentiments and evaluated on later feedback sentiments."
    ∷ "This supports transfer and trajectory investigation, not a causal effect of course redesign."
    ∷ "Exact OEF vectors are not invented where the source does not report them as longitudinal matched measures."
    ∷ [] )

data TrajectoryPromotionRoute : Set where
  candidateTrajectoryRoute : TrajectoryPromotionRoute
  longitudinalChangeEqualsCausationRoute : TrajectoryPromotionRoute
  laterSemesterEqualsMatchedPanelRoute : TrajectoryPromotionRoute
  aggregateTrajectoryEqualsIndividualRoute : TrajectoryPromotionRoute
  redesignEqualsImprovementRoute : TrajectoryPromotionRoute

AdmissibleTrajectoryPromotionRoute : TrajectoryPromotionRoute → Set
AdmissibleTrajectoryPromotionRoute candidateTrajectoryRoute = ⊤
AdmissibleTrajectoryPromotionRoute longitudinalChangeEqualsCausationRoute = Never
AdmissibleTrajectoryPromotionRoute laterSemesterEqualsMatchedPanelRoute = Never
AdmissibleTrajectoryPromotionRoute aggregateTrajectoryEqualsIndividualRoute = Never
AdmissibleTrajectoryPromotionRoute redesignEqualsImprovementRoute = Never

candidateTrajectoryRouteAdmissible :
  AdmissibleTrajectoryPromotionRoute candidateTrajectoryRoute
candidateTrajectoryRouteAdmissible = tt

longitudinalChangeEqualsCausationBlocked :
  AdmissibleTrajectoryPromotionRoute longitudinalChangeEqualsCausationRoute → Never
longitudinalChangeEqualsCausationBlocked ()

laterSemesterEqualsMatchedPanelBlocked :
  AdmissibleTrajectoryPromotionRoute laterSemesterEqualsMatchedPanelRoute → Never
laterSemesterEqualsMatchedPanelBlocked ()

aggregateTrajectoryEqualsIndividualBlocked :
  AdmissibleTrajectoryPromotionRoute aggregateTrajectoryEqualsIndividualRoute → Never
aggregateTrajectoryEqualsIndividualBlocked ()

redesignEqualsImprovementBlocked :
  AdmissibleTrajectoryPromotionRoute redesignEqualsImprovementRoute → Never
redesignEqualsImprovementBlocked ()

record LongitudinalEngagementTrajectory : Set where
  constructor mkLongitudinalEngagementTrajectory
  field
    sourceSystem : OEF.OEFMultiFibreFeedbackHyperfabric
    sourceSystemIsCanonical : sourceSystem ≡ OEF.canonicalOEFMultiFibreFeedbackHyperfabric
    trajectoryCandidate : EngagementTrajectoryCandidate
    trajectoryCandidateIsCanonical : trajectoryCandidate ≡ canonicalEngagementTrajectoryCandidate
    route : TrajectoryPromotionRoute
    routeIsCandidate : route ≡ candidateTrajectoryRoute
    routeAdmissible : AdmissibleTrajectoryPromotionRoute route
    endpointNotTrajectory : Bool
    endpointNotTrajectoryIsTrue : endpointNotTrajectory ≡ true
    laterSemesterNotMatchedPanel : Bool
    laterSemesterNotMatchedPanelIsTrue : laterSemesterNotMatchedPanel ≡ true
    longitudinalChangeNotCausation : Bool
    longitudinalChangeNotCausationIsTrue : longitudinalChangeNotCausation ≡ true
    replicationRequiredForProgrammePractice : Bool
    replicationRequiredForProgrammePracticeIsTrue : replicationRequiredForProgrammePractice ≡ true
    reading : String

open LongitudinalEngagementTrajectory public

canonicalLongitudinalEngagementTrajectory : LongitudinalEngagementTrajectory
canonicalLongitudinalEngagementTrajectory =
  mkLongitudinalEngagementTrajectory
    OEF.canonicalOEFMultiFibreFeedbackHyperfabric refl
    canonicalEngagementTrajectoryCandidate refl
    candidateTrajectoryRoute refl tt
    true refl
    true refl
    true refl
    true refl
    "The source establishes a training-to-later-semester classification transfer surface. Strong longitudinal research should use repeated measurements, cohort comparability, implementation receipts, student interpretation, confound audit, and replication before causal or programme-level promotion."

LongitudinalChangeNotCausation : Set
LongitudinalChangeNotCausation =
  longitudinalChangeNotCausation canonicalLongitudinalEngagementTrajectory ≡ true

longitudinalChangeNotCausationProof : LongitudinalChangeNotCausation
longitudinalChangeNotCausationProof =
  longitudinalChangeNotCausationIsTrue canonicalLongitudinalEngagementTrajectory
