module DASHI.Physics.Closure.NSSprint89PointwiseH1TailCandidateMechanismReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])
open import Data.Product using (_×_; _,_)

import DASHI.Physics.Closure.NSSprint88DangerShellH1TailSmallnessDecisionReceipt
  as Sprint88

------------------------------------------------------------------------
-- Sprint 89 NS pointwise H^1-tail candidate-mechanism receipt.
--
-- Sprint 88 left the live scalar target as strict pointwise H^1-tail
-- smallness at K*(t).  Sprint 89 records the sharper current gate:
-- PointwiseH1TailWithIndependentEpsilonCoefficient.  This module classifies
-- the candidate sub-mechanisms and keeps the global status fail-closed.  It
-- does not promote Navier-Stokes/Clay regularity and does not use absorption
-- to prove the coefficient required for absorption.

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

pointwiseH1TailWithIndependentEpsilonCoefficientClosed : Bool
pointwiseH1TailWithIndependentEpsilonCoefficientClosed = false

localEnstrophyDangerShellDissipationMechanismClassified : Bool
localEnstrophyDangerShellDissipationMechanismClassified = true

timeIntegratedToPointwiseConversionClassified : Bool
timeIntegratedToPointwiseConversionClassified = true

coefficientIndependenceClassified : Bool
coefficientIndependenceClassified = true

noSelfUseOfAbsorptionClassified : Bool
noSelfUseOfAbsorptionClassified = true

localEnstrophyDangerShellDissipationClosed : Bool
localEnstrophyDangerShellDissipationClosed = false

timeIntegratedToPointwiseConversionClosed : Bool
timeIntegratedToPointwiseConversionClosed = false

independentEpsilonCoefficientClosed : Bool
independentEpsilonCoefficientClosed = false

noSelfUseOfAbsorptionClosed : Bool
noSelfUseOfAbsorptionClosed = true

data Sprint89Gate : Set where
  PointwiseH1TailWithIndependentEpsilonCoefficient :
    Sprint89Gate

canonicalSprint89Gate : Sprint89Gate
canonicalSprint89Gate =
  PointwiseH1TailWithIndependentEpsilonCoefficient

sprint89GateStatement : String
sprint89GateStatement =
  "PointwiseH1TailWithIndependentEpsilonCoefficient: prove a pointwise H^1 danger-shell tail bound at K*(t) with an epsilon coefficient chosen independently of the absorption step and without importing H^1/Serrin/BKM/Clay regularity."

data CandidateSubMechanism : Set where
  localEnstrophyDangerShellDissipation :
    CandidateSubMechanism
  timeIntegratedDissipationToPointwiseTail :
    CandidateSubMechanism
  epsilonCoefficientIndependence :
    CandidateSubMechanism
  noSelfUseOfAbsorption :
    CandidateSubMechanism

canonicalCandidateSubMechanisms : List CandidateSubMechanism
canonicalCandidateSubMechanisms =
  localEnstrophyDangerShellDissipation
  ∷ timeIntegratedDissipationToPointwiseTail
  ∷ epsilonCoefficientIndependence
  ∷ noSelfUseOfAbsorption
  ∷ []

data CandidateMechanismDecision : Set where
  classifiedOpenNeedsPointwiseDissipation :
    CandidateMechanismDecision
  classifiedOpenNeedsTimeLocalization :
    CandidateMechanismDecision
  classifiedOpenNeedsIndependentCoefficient :
    CandidateMechanismDecision
  classifiedClosedAsGovernanceConstraint :
    CandidateMechanismDecision

record CandidateMechanismClassification : Set where
  constructor classify
  field
    mechanism :
      CandidateSubMechanism
    decision :
      CandidateMechanismDecision
    closed :
      Bool
    note :
      String

open CandidateMechanismClassification public

localEnstrophyDangerShellDissipationClassification :
  CandidateMechanismClassification
localEnstrophyDangerShellDissipationClassification =
  classify
    localEnstrophyDangerShellDissipation
    classifiedOpenNeedsPointwiseDissipation
    false
    "Local enstrophy/danger-shell dissipation is the concrete PDE mechanism class that could produce the H^1 tail bound, but Sprint 88 only records it as the required live source; no in-repo pointwise dissipation lemma closes it."

timeIntegratedToPointwiseClassification :
  CandidateMechanismClassification
timeIntegratedToPointwiseClassification =
  classify
    timeIntegratedDissipationToPointwiseTail
    classifiedOpenNeedsTimeLocalization
    false
    "The Leray time-integrated dissipation budget is classified as relevant, but the missing step is a non-circular conversion from integrated H^1 dissipation to pointwise strict tail smallness at the danger shell."

coefficientIndependenceClassification :
  CandidateMechanismClassification
coefficientIndependenceClassification =
  classify
    epsilonCoefficientIndependence
    classifiedOpenNeedsIndependentCoefficient
    false
    "The epsilon coefficient must be selected before and independently of the absorption inequality; no Sprint 89 derivation supplies that independent coefficient."

noSelfUseOfAbsorptionClassification :
  CandidateMechanismClassification
noSelfUseOfAbsorptionClassification =
  classify
    noSelfUseOfAbsorption
    classifiedClosedAsGovernanceConstraint
    true
    "The receipt enforces no self-use of absorption: absorption may not be assumed to prove the independent epsilon coefficient needed to invoke absorption."

canonicalCandidateMechanismClassifications :
  List CandidateMechanismClassification
canonicalCandidateMechanismClassifications =
  localEnstrophyDangerShellDissipationClassification
  ∷ timeIntegratedToPointwiseClassification
  ∷ coefficientIndependenceClassification
  ∷ noSelfUseOfAbsorptionClassification
  ∷ []

data Sprint89FailClosedBoundary : Set where
  sprint88PointwiseH1TailSmallnessInheritedOpen :
    Sprint89FailClosedBoundary
  localEnstrophyDangerShellDissipationNotDerived :
    Sprint89FailClosedBoundary
  timeIntegratedToPointwiseConversionNotDerived :
    Sprint89FailClosedBoundary
  independentEpsilonCoefficientNotDerived :
    Sprint89FailClosedBoundary
  absorptionNotUsedToProveItsOwnCoefficient :
    Sprint89FailClosedBoundary
  pointwiseH1TailWithIndependentEpsilonCoefficientStillFalse :
    Sprint89FailClosedBoundary
  clayNavierStokesPromotionStillFalse :
    Sprint89FailClosedBoundary

canonicalFailClosedBoundaries : List Sprint89FailClosedBoundary
canonicalFailClosedBoundaries =
  sprint88PointwiseH1TailSmallnessInheritedOpen
  ∷ localEnstrophyDangerShellDissipationNotDerived
  ∷ timeIntegratedToPointwiseConversionNotDerived
  ∷ independentEpsilonCoefficientNotDerived
  ∷ absorptionNotUsedToProveItsOwnCoefficient
  ∷ pointwiseH1TailWithIndependentEpsilonCoefficientStillFalse
  ∷ clayNavierStokesPromotionStillFalse
  ∷ []

sprint89ClassificationSummary : String
sprint89ClassificationSummary =
  "Sprint 89 classifies four sub-mechanisms: local enstrophy/danger-shell dissipation is open; time-integrated-to-pointwise conversion is open; independent epsilon coefficient construction is open; no self-use of absorption is enforced as a closed governance constraint."

sprint89BoundaryStatement : String
sprint89BoundaryStatement =
  "Sprint 89 records the exact current gate PointwiseH1TailWithIndependentEpsilonCoefficient and fails closed: pointwiseH1TailWithIndependentEpsilonCoefficientClosed=false and clayNavierStokesPromoted=false."

record NSSprint89PointwiseH1TailCandidateMechanismReceipt : Setω where
  field
    sprint88Receipt :
      Sprint88.NSSprint88DangerShellH1TailSmallnessDecisionReceipt
    sprint88NonCircularH1TailStillOpen :
      Sprint88.nonCircularDangerShellH1TailSmallnessClosed ≡ false
    sprint88DangerShellAbsorptionStillOpen :
      Sprint88.dangerShellAbsorptionConditionClosed ≡ false
    sprint88NoClay :
      Sprint88.clayNavierStokesPromoted ≡ false

    gate :
      Sprint89Gate
    gateIsCanonical :
      gate ≡ canonicalSprint89Gate
    gateStatement :
      String
    gateStatementIsCanonical :
      gateStatement ≡ sprint89GateStatement

    candidateSubMechanisms :
      List CandidateSubMechanism
    candidateSubMechanismsAreCanonical :
      candidateSubMechanisms ≡ canonicalCandidateSubMechanisms
    candidateClassifications :
      List CandidateMechanismClassification
    candidateClassificationsAreCanonical :
      candidateClassifications ≡ canonicalCandidateMechanismClassifications
    classificationSummary :
      String
    classificationSummaryIsCanonical :
      classificationSummary ≡ sprint89ClassificationSummary

    localEnstrophyDangerShellDissipationClassifiedIsTrue :
      localEnstrophyDangerShellDissipationMechanismClassified ≡ true
    timeIntegratedToPointwiseConversionClassifiedIsTrue :
      timeIntegratedToPointwiseConversionClassified ≡ true
    coefficientIndependenceClassifiedIsTrue :
      coefficientIndependenceClassified ≡ true
    noSelfUseOfAbsorptionClassifiedIsTrue :
      noSelfUseOfAbsorptionClassified ≡ true

    localEnstrophyDangerShellDissipationClosedIsFalse :
      localEnstrophyDangerShellDissipationClosed ≡ false
    timeIntegratedToPointwiseConversionClosedIsFalse :
      timeIntegratedToPointwiseConversionClosed ≡ false
    independentEpsilonCoefficientClosedIsFalse :
      independentEpsilonCoefficientClosed ≡ false
    noSelfUseOfAbsorptionClosedIsTrue :
      noSelfUseOfAbsorptionClosed ≡ true

    failClosedBoundaries :
      List Sprint89FailClosedBoundary
    failClosedBoundariesAreCanonical :
      failClosedBoundaries ≡ canonicalFailClosedBoundaries
    pointwiseH1TailWithIndependentEpsilonCoefficientClosedIsFalse :
      pointwiseH1TailWithIndependentEpsilonCoefficientClosed ≡ false
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    boundary :
      String
    boundaryIsCanonical :
      boundary ≡ sprint89BoundaryStatement

open NSSprint89PointwiseH1TailCandidateMechanismReceipt public

canonicalNSSprint89PointwiseH1TailCandidateMechanismReceipt :
  NSSprint89PointwiseH1TailCandidateMechanismReceipt
canonicalNSSprint89PointwiseH1TailCandidateMechanismReceipt =
  record
    { sprint88Receipt =
        Sprint88.canonicalNSSprint88DangerShellH1TailSmallnessDecisionReceipt
    ; sprint88NonCircularH1TailStillOpen =
        refl
    ; sprint88DangerShellAbsorptionStillOpen =
        refl
    ; sprint88NoClay =
        refl
    ; gate =
        canonicalSprint89Gate
    ; gateIsCanonical =
        refl
    ; gateStatement =
        sprint89GateStatement
    ; gateStatementIsCanonical =
        refl
    ; candidateSubMechanisms =
        canonicalCandidateSubMechanisms
    ; candidateSubMechanismsAreCanonical =
        refl
    ; candidateClassifications =
        canonicalCandidateMechanismClassifications
    ; candidateClassificationsAreCanonical =
        refl
    ; classificationSummary =
        sprint89ClassificationSummary
    ; classificationSummaryIsCanonical =
        refl
    ; localEnstrophyDangerShellDissipationClassifiedIsTrue =
        refl
    ; timeIntegratedToPointwiseConversionClassifiedIsTrue =
        refl
    ; coefficientIndependenceClassifiedIsTrue =
        refl
    ; noSelfUseOfAbsorptionClassifiedIsTrue =
        refl
    ; localEnstrophyDangerShellDissipationClosedIsFalse =
        refl
    ; timeIntegratedToPointwiseConversionClosedIsFalse =
        refl
    ; independentEpsilonCoefficientClosedIsFalse =
        refl
    ; noSelfUseOfAbsorptionClosedIsTrue =
        refl
    ; failClosedBoundaries =
        canonicalFailClosedBoundaries
    ; failClosedBoundariesAreCanonical =
        refl
    ; pointwiseH1TailWithIndependentEpsilonCoefficientClosedIsFalse =
        refl
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; boundary =
        sprint89BoundaryStatement
    ; boundaryIsCanonical =
        refl
    }

canonicalSprint89Flags :
  (localEnstrophyDangerShellDissipationMechanismClassified ≡ true)
  × (timeIntegratedToPointwiseConversionClassified ≡ true)
  × (coefficientIndependenceClassified ≡ true)
  × (noSelfUseOfAbsorptionClassified ≡ true)
  × (localEnstrophyDangerShellDissipationClosed ≡ false)
  × (timeIntegratedToPointwiseConversionClosed ≡ false)
  × (independentEpsilonCoefficientClosed ≡ false)
  × (noSelfUseOfAbsorptionClosed ≡ true)
  × (pointwiseH1TailWithIndependentEpsilonCoefficientClosed ≡ false)
  × (clayNavierStokesPromoted ≡ false)
canonicalSprint89Flags =
  refl , refl , refl , refl , refl , refl , refl , refl , refl , refl

canonicalNSSprint89H1TailCandidateMechanismReceipt :
  NSSprint89PointwiseH1TailCandidateMechanismReceipt
canonicalNSSprint89H1TailCandidateMechanismReceipt =
  canonicalNSSprint89PointwiseH1TailCandidateMechanismReceipt
