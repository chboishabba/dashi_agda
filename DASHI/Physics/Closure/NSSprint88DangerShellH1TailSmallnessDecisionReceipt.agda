module DASHI.Physics.Closure.NSSprint88DangerShellH1TailSmallnessDecisionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.NSDangerShellMaximumPrincipleReceipt
  as DangerShell
import DASHI.Physics.Closure.NSLeraySobolevSharpnessReceipt
  as Leray
import DASHI.Physics.Closure.NSSprint86KStarHHalfTailObstructionReceipt
  as Sprint86
import DASHI.Physics.Closure.NSSprint87DangerShellSupFactorizationReceipt
  as Sprint87

------------------------------------------------------------------------
-- Sprint 88 NS danger-shell H^1-tail smallness decision receipt.
--
-- Sprint 87 closed the dyadic factorization surface that rewrites the
-- high-high danger-shell contribution as a shell supremum factor times an
-- H^1-tail factor.  Sprint 88 records the exact scalar target left behind:
-- prove strict smallness of that H^1 tail at K*(t), with no circular import of
-- H^1 continuation, Serrin/BKM continuation, or Clay regularity.

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

dyadicFactorizationInheritedClosed : Bool
dyadicFactorizationInheritedClosed = true

sprint87FactorizationInheritedClosed : Bool
sprint87FactorizationInheritedClosed = true

kstarAloneInsufficient : Bool
kstarAloneInsufficient = true

kStarAdmissibilityAloneInsufficient : Bool
kStarAdmissibilityAloneInsufficient = true

lerayAloneInsufficient : Bool
lerayAloneInsufficient = true

lerayEnergyAloneInsufficient : Bool
lerayEnergyAloneInsufficient = true

timeIntegratedDissipationPointwiseInsufficient : Bool
timeIntegratedDissipationPointwiseInsufficient = true

nonCircularDangerShellH1TailSmallnessClosed : Bool
nonCircularDangerShellH1TailSmallnessClosed = false

dangerShellAbsorptionConditionClosed : Bool
dangerShellAbsorptionConditionClosed = false

data DangerShellH1TailSmallnessScalarTarget : Set where
  strictH1TailSmallnessAtKStar :
    DangerShellH1TailSmallnessScalarTarget

canonicalDangerShellH1TailSmallnessScalarTarget :
  DangerShellH1TailSmallnessScalarTarget
canonicalDangerShellH1TailSmallnessScalarTarget =
  strictH1TailSmallnessAtKStar

dangerShellH1TailSmallnessTargetStatement : String
dangerShellH1TailSmallnessTargetStatement =
  "DangerShellH1TailSmallness: at K*(t), prove the dyadically factored H^1 tail scalar is strictly below the danger-shell absorption margin, without importing H^1 continuation, Serrin/BKM continuation, or Clay regularity."

data CandidateSource : Set where
  kstarAdmissibilityAlone :
    CandidateSource
  lerayEnergyInequality :
    CandidateSource
  timeIntegratedDissipation :
    CandidateSource
  pointwiseDangerShellMechanism :
    CandidateSource

canonicalCandidateSources : List CandidateSource
canonicalCandidateSources =
  kstarAdmissibilityAlone
  ∷ lerayEnergyInequality
  ∷ timeIntegratedDissipation
  ∷ pointwiseDangerShellMechanism
  ∷ []

data CandidateSourceDecision : Set where
  insufficientForPointwiseH1TailSmallness :
    CandidateSourceDecision
  candidateOnlyNoPointwiseConversion :
    CandidateSourceDecision
  requiredLiveMechanismOpen :
    CandidateSourceDecision

record CandidateSourceClassification : Set where
  constructor classify
  field
    source :
      CandidateSource
    decision :
      CandidateSourceDecision
    note :
      String

open CandidateSourceClassification public

kstarAdmissibilityClassification :
  CandidateSourceClassification
kstarAdmissibilityClassification =
  classify
    kstarAdmissibilityAlone
    insufficientForPointwiseH1TailSmallness
    "KStar admissibility alone supplies cutoff/L2-tail bookkeeping, but Sprint 86 records that it does not derive the needed H^{1/2} or H^1 danger-shell tail smallness without hidden regularity."

lerayEnergyClassification :
  CandidateSourceClassification
lerayEnergyClassification =
  classify
    lerayEnergyInequality
    insufficientForPointwiseH1TailSmallness
    "The Leray energy inequality is global-in-time L2 plus integrated H1 dissipation control; by the Leray/Sobolev sharpness obstruction it does not give a pointwise danger-shell H^1-tail scalar below the absorption margin."

timeIntegratedDissipationClassification :
  CandidateSourceClassification
timeIntegratedDissipationClassification =
  classify
    timeIntegratedDissipation
    candidateOnlyNoPointwiseConversion
    "Time-integrated dissipation may bound the integral of the H^1 tail, but no in-repo non-circular lemma converts that integral budget into pointwise strict smallness at K*(t)."

pointwiseDangerShellClassification :
  CandidateSourceClassification
pointwiseDangerShellClassification =
  classify
    pointwiseDangerShellMechanism
    requiredLiveMechanismOpen
    "The only viable source class is a pointwise danger-shell mechanism proving strict H^1-tail smallness at K*(t); the maximum-principle and edge-leakage receipts record this as open."

canonicalCandidateSourceClassifications :
  List CandidateSourceClassification
canonicalCandidateSourceClassifications =
  kstarAdmissibilityClassification
  ∷ lerayEnergyClassification
  ∷ timeIntegratedDissipationClassification
  ∷ pointwiseDangerShellClassification
  ∷ []

data Sprint88ClosedInheritance : Set where
  sprint87DyadicSupFactorizationInherited :
    Sprint88ClosedInheritance

canonicalClosedInheritance :
  List Sprint88ClosedInheritance
canonicalClosedInheritance =
  sprint87DyadicSupFactorizationInherited
  ∷ []

data Sprint88OpenBoundary : Set where
  nonCircularPointwiseH1TailSmallnessAtKStar :
    Sprint88OpenBoundary
  noKStarAloneConversion :
    Sprint88OpenBoundary
  noLerayAlonePointwiseConversion :
    Sprint88OpenBoundary
  noIntegratedDissipationToPointwiseDangerShellConversion :
    Sprint88OpenBoundary
  dangerShellAbsorptionStillOpen :
    Sprint88OpenBoundary
  clayNavierStokesPromotionStillFalse :
    Sprint88OpenBoundary

canonicalOpenBoundaries : List Sprint88OpenBoundary
canonicalOpenBoundaries =
  nonCircularPointwiseH1TailSmallnessAtKStar
  ∷ noKStarAloneConversion
  ∷ noLerayAlonePointwiseConversion
  ∷ noIntegratedDissipationToPointwiseDangerShellConversion
  ∷ dangerShellAbsorptionStillOpen
  ∷ clayNavierStokesPromotionStillFalse
  ∷ []

candidateClassificationSummary : String
candidateClassificationSummary =
  "Candidate sources classified: KStar admissibility alone is insufficient; Leray energy inequality alone is insufficient; time-integrated dissipation is candidate-only without pointwise conversion; a pointwise danger-shell mechanism is the required open source."

sprint88BoundaryStatement : String
sprint88BoundaryStatement =
  "Sprint 88 inherits Sprint 87 dyadic factorization as closed, but the scalar DangerShellH1TailSmallness target remains open. Therefore nonCircularDangerShellH1TailSmallnessClosed=false, dangerShellAbsorptionConditionClosed=false, and clayNavierStokesPromoted=false."

record NSSprint88DangerShellH1TailSmallnessDecisionReceipt : Setω where
  field
    sprint87Receipt :
      Sprint87.NSSprint87DangerShellSupFactorizationReceipt
    sprint87DyadicFactorizationClosed :
      Sprint87.dyadicSupFactorizationClosed ≡ true
    sprint87ShellSupControlledByH1TailClosed :
      Sprint87.shellSupControlledByH1TailClosed ≡ true
    sprint87AbsorptionStillOpen :
      Sprint87.dangerShellAbsorptionConditionClosed ≡ false
    sprint87NoClay :
      Sprint87.clayNavierStokesPromoted ≡ false

    sprint86Receipt :
      Sprint86.NSSprint86KStarHHalfTailObstructionReceipt
    sprint86KStarAloneStillInsufficient :
      Sprint86.kstarAdmissibilityAloneControlsHHalfTailDerivedInRepo
      ≡ false
    sprint86AbsorptionCoefficientStillOpen :
      Sprint86.epsilonBelowOneCoefficientDerivedInRepo ≡ false
    sprint86NoClay :
      Sprint86.clayNavierStokesPromoted ≡ false

    leraySharpnessReceipt :
      Leray.NSLeraySobolevSharpnessReceipt
    lerayOnlyRouteKilled :
      Leray.subcriticalAbsorptionImpossibleFromLerayOnlyProved
        leraySharpnessReceipt
      ≡ true
    lerayNoClay :
      Leray.clayNavierStokesPromoted leraySharpnessReceipt ≡ false

    dangerShellReceipt :
      DangerShell.NSDangerShellMaximumPrincipleReceipt
    dangerShellPointwiseMechanismStillOpen :
      DangerShell.dangerShellMaxPrincipleProved dangerShellReceipt ≡ false
    dangerShellNoClay :
      DangerShell.clayNavierStokesPromoted dangerShellReceipt ≡ false

    scalarTarget :
      DangerShellH1TailSmallnessScalarTarget
    scalarTargetIsCanonical :
      scalarTarget ≡ canonicalDangerShellH1TailSmallnessScalarTarget
    scalarTargetStatement :
      String
    scalarTargetStatementIsCanonical :
      scalarTargetStatement ≡ dangerShellH1TailSmallnessTargetStatement

    candidateSources :
      List CandidateSource
    candidateSourcesAreCanonical :
      candidateSources ≡ canonicalCandidateSources
    candidateClassifications :
      List CandidateSourceClassification
    candidateClassificationsAreCanonical :
      candidateClassifications ≡ canonicalCandidateSourceClassifications
    classificationSummary :
      String
    classificationSummaryIsCanonical :
      classificationSummary ≡ candidateClassificationSummary

    closedInheritance :
      List Sprint88ClosedInheritance
    closedInheritanceIsCanonical :
      closedInheritance ≡ canonicalClosedInheritance
    openBoundaries :
      List Sprint88OpenBoundary
    openBoundariesAreCanonical :
      openBoundaries ≡ canonicalOpenBoundaries

    dyadicFactorizationInheritedClosedIsTrue :
      dyadicFactorizationInheritedClosed ≡ true
    sprint87FactorizationInheritedClosedIsTrue :
      sprint87FactorizationInheritedClosed ≡ true
    kstarAloneInsufficientIsTrue :
      kstarAloneInsufficient ≡ true
    kStarAdmissibilityAloneInsufficientIsTrue :
      kStarAdmissibilityAloneInsufficient ≡ true
    lerayAloneInsufficientIsTrue :
      lerayAloneInsufficient ≡ true
    lerayEnergyAloneInsufficientIsTrue :
      lerayEnergyAloneInsufficient ≡ true
    timeIntegratedDissipationPointwiseInsufficientIsTrue :
      timeIntegratedDissipationPointwiseInsufficient ≡ true
    nonCircularDangerShellH1TailSmallnessClosedIsFalse :
      nonCircularDangerShellH1TailSmallnessClosed ≡ false
    dangerShellAbsorptionConditionClosedIsFalse :
      dangerShellAbsorptionConditionClosed ≡ false
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    boundary :
      String
    boundaryIsCanonical :
      boundary ≡ sprint88BoundaryStatement

open NSSprint88DangerShellH1TailSmallnessDecisionReceipt public

canonicalNSSprint88DangerShellH1TailSmallnessDecisionReceipt :
  NSSprint88DangerShellH1TailSmallnessDecisionReceipt
canonicalNSSprint88DangerShellH1TailSmallnessDecisionReceipt =
  record
    { sprint87Receipt =
        Sprint87.canonicalNSSprint87DangerShellSupFactorizationReceipt
    ; sprint87DyadicFactorizationClosed =
        refl
    ; sprint87ShellSupControlledByH1TailClosed =
        refl
    ; sprint87AbsorptionStillOpen =
        refl
    ; sprint87NoClay =
        refl
    ; sprint86Receipt =
        Sprint86.canonicalNSSprint86KStarHHalfTailObstructionReceipt
    ; sprint86KStarAloneStillInsufficient =
        refl
    ; sprint86AbsorptionCoefficientStillOpen =
        refl
    ; sprint86NoClay =
        refl
    ; leraySharpnessReceipt =
        Leray.canonicalNSLeraySobolevSharpnessReceipt
    ; lerayOnlyRouteKilled =
        refl
    ; lerayNoClay =
        refl
    ; dangerShellReceipt =
        DangerShell.canonicalNSDangerShellMaximumPrincipleReceipt
    ; dangerShellPointwiseMechanismStillOpen =
        refl
    ; dangerShellNoClay =
        refl
    ; scalarTarget =
        canonicalDangerShellH1TailSmallnessScalarTarget
    ; scalarTargetIsCanonical =
        refl
    ; scalarTargetStatement =
        dangerShellH1TailSmallnessTargetStatement
    ; scalarTargetStatementIsCanonical =
        refl
    ; candidateSources =
        canonicalCandidateSources
    ; candidateSourcesAreCanonical =
        refl
    ; candidateClassifications =
        canonicalCandidateSourceClassifications
    ; candidateClassificationsAreCanonical =
        refl
    ; classificationSummary =
        candidateClassificationSummary
    ; classificationSummaryIsCanonical =
        refl
    ; closedInheritance =
        canonicalClosedInheritance
    ; closedInheritanceIsCanonical =
        refl
    ; openBoundaries =
        canonicalOpenBoundaries
    ; openBoundariesAreCanonical =
        refl
    ; dyadicFactorizationInheritedClosedIsTrue =
        refl
    ; sprint87FactorizationInheritedClosedIsTrue =
        refl
    ; kstarAloneInsufficientIsTrue =
        refl
    ; kStarAdmissibilityAloneInsufficientIsTrue =
        refl
    ; lerayAloneInsufficientIsTrue =
        refl
    ; lerayEnergyAloneInsufficientIsTrue =
        refl
    ; timeIntegratedDissipationPointwiseInsufficientIsTrue =
        refl
    ; nonCircularDangerShellH1TailSmallnessClosedIsFalse =
        refl
    ; dangerShellAbsorptionConditionClosedIsFalse =
        refl
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; boundary =
        sprint88BoundaryStatement
    ; boundaryIsCanonical =
        refl
    }

canonicalSprint88Flags :
  (sprint87FactorizationInheritedClosed ≡ true)
  × (kStarAdmissibilityAloneInsufficient ≡ true)
  × (lerayEnergyAloneInsufficient ≡ true)
  × (timeIntegratedDissipationPointwiseInsufficient ≡ true)
  × (nonCircularDangerShellH1TailSmallnessClosed ≡ false)
  × (dangerShellAbsorptionConditionClosed ≡ false)
  × (clayNavierStokesPromoted ≡ false)
canonicalSprint88Flags =
  refl , refl , refl , refl , refl , refl , refl

canonicalNSSprint88H1TailSmallnessDecisionReceipt :
  NSSprint88DangerShellH1TailSmallnessDecisionReceipt
canonicalNSSprint88H1TailSmallnessDecisionReceipt =
  canonicalNSSprint88DangerShellH1TailSmallnessDecisionReceipt
