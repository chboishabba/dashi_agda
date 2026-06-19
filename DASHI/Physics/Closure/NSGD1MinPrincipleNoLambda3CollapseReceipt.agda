module DASHI.Physics.Closure.NSGD1MinPrincipleNoLambda3CollapseReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

------------------------------------------------------------------------
-- Fail-closed GD1 two-regime minimum-principle receipt.
--
-- This module records the conditional GD1 lane only:
--
--   D_t g12 >= g12^2(1-CCZ) - Cnu*g12
--
-- with the critical gap
--
--   gcrit = Cnu/(1-CCZ)
--
-- and the two regimes:
--   * supercritical: restoring,
--   * subcritical: exponential lower bound.
--
-- It also records the biaxial-carrier projection lambda3 = g12 and the
-- resulting h_delta1 candidate.  No Clay promotion is claimed unless the
-- exact constants, CZ term, and GD1 proof terms are discharged.  The
-- promotion surface here is deliberately empty.

listLength : {A : Set} → List A → Nat
listLength [] =
  zero
listLength (_ ∷ xs) =
  suc (listLength xs)

data NSGD1MinPrincipleNoLambda3CollapseStatus : Set where
  gd1MinimumPrincipleReceiptRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStatus

data NSGD1MinPrincipleNoLambda3CollapseStage : Set where
  gd1InequalityRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStage
  criticalGapRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStage
  supercriticalRestoringRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStage
  subcriticalExponentialLowerBoundRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStage
  lambda3EqualsG12OnBiaxialCarrierRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStage
  hDelta1CandidateRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStage
  exactConstantsAndCZAndGD1ProofTermsRequiredRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStage
  clayPromotionBlockedRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStage
  failClosedRouteRecorded :
    NSGD1MinPrincipleNoLambda3CollapseStage

canonicalNSGD1MinPrincipleNoLambda3CollapseStages :
  List NSGD1MinPrincipleNoLambda3CollapseStage
canonicalNSGD1MinPrincipleNoLambda3CollapseStages =
  gd1InequalityRecorded
  ∷ criticalGapRecorded
  ∷ supercriticalRestoringRecorded
  ∷ subcriticalExponentialLowerBoundRecorded
  ∷ lambda3EqualsG12OnBiaxialCarrierRecorded
  ∷ hDelta1CandidateRecorded
  ∷ exactConstantsAndCZAndGD1ProofTermsRequiredRecorded
  ∷ clayPromotionBlockedRecorded
  ∷ failClosedRouteRecorded
  ∷ []

data NSGD1MinPrincipleNoLambda3CollapseBlocker : Set where
  NoLambda3CollapseOnKatoCarrier :
    NSGD1MinPrincipleNoLambda3CollapseBlocker
  LayerKornInequality :
    NSGD1MinPrincipleNoLambda3CollapseBlocker
  RellichKatoCommutatorProofTerm :
    NSGD1MinPrincipleNoLambda3CollapseBlocker
  LayerCZ :
    NSGD1MinPrincipleNoLambda3CollapseBlocker
  exactConstantsStillOpen :
    NSGD1MinPrincipleNoLambda3CollapseBlocker
  GD1ProofTermsStillOpen :
    NSGD1MinPrincipleNoLambda3CollapseBlocker

canonicalNSGD1MinPrincipleNoLambda3CollapseBlockers :
  List NSGD1MinPrincipleNoLambda3CollapseBlocker
canonicalNSGD1MinPrincipleNoLambda3CollapseBlockers =
  NoLambda3CollapseOnKatoCarrier
  ∷ LayerKornInequality
  ∷ RellichKatoCommutatorProofTerm
  ∷ LayerCZ
  ∷ exactConstantsStillOpen
  ∷ GD1ProofTermsStillOpen
  ∷ []

canonicalNSGD1MinPrincipleNoLambda3CollapseDependencyNames :
  List String
canonicalNSGD1MinPrincipleNoLambda3CollapseDependencyNames =
  "D_t g12 >= g12^2(1-CCZ)-Cnu*g12"
  ∷ "gcrit=Cnu/(1-CCZ)"
  ∷ "supercritical restoring"
  ∷ "subcritical exponential lower bound"
  ∷ "lambda3=g12 on biaxial carrier"
  ∷ "h_delta1 candidate"
  ∷ "exact constants"
  ∷ "CZ proof term"
  ∷ "GD1 proof terms"
  ∷ []

gd1MinimumPrincipleTextValue : String
gd1MinimumPrincipleTextValue =
  "D_t g12 >= g12^2(1-CCZ) - Cnu*g12"

criticalGapTextValue : String
criticalGapTextValue =
  "gcrit = Cnu/(1-CCZ)"

supercriticalRestoringTextValue : String
supercriticalRestoringTextValue =
  "supercritical regime: restoring"

subcriticalExponentialLowerBoundTextValue : String
subcriticalExponentialLowerBoundTextValue =
  "subcritical regime: exponential lower bound"

lambda3OnBiaxialCarrierTextValue : String
lambda3OnBiaxialCarrierTextValue =
  "lambda3 = g12 on biaxial carrier"

hDelta1CandidateTextValue : String
hDelta1CandidateTextValue =
  "h_delta1 candidate is recorded, not discharged"

exactConstantsCZGD1RequiredTextValue : String
exactConstantsCZGD1RequiredTextValue =
  "exact constants, CZ, and GD1 proof terms remain required before any Clay promotion"

failClosedRouteTextValue : String
failClosedRouteTextValue =
  "fail-closed route only; no Clay promotion and no collapse promotion are claimed"

data NSGD1MinPrinciplePromotion : Set where

promotionEmptyTypeWitness : NSGD1MinPrinciplePromotion → ⊥
promotionEmptyTypeWitness ()

record NSGD1MinPrincipleNoLambda3CollapseReceipt : Setω where
  field
    status :
      NSGD1MinPrincipleNoLambda3CollapseStatus
    statusIsCanonical :
      status ≡ gd1MinimumPrincipleReceiptRecorded

    stageLedger :
      List NSGD1MinPrincipleNoLambda3CollapseStage
    stageLedgerIsCanonical :
      stageLedger ≡ canonicalNSGD1MinPrincipleNoLambda3CollapseStages

    stageCount :
      Nat
    stageCountIsCanonical :
      stageCount ≡
      listLength canonicalNSGD1MinPrincipleNoLambda3CollapseStages

    dependencyNames :
      List String
    dependencyNamesIsCanonical :
      dependencyNames
      ≡ canonicalNSGD1MinPrincipleNoLambda3CollapseDependencyNames

    dependencyNameCount :
      Nat
    dependencyNameCountIsCanonical :
      dependencyNameCount ≡
      listLength canonicalNSGD1MinPrincipleNoLambda3CollapseDependencyNames

    blockerLedger :
      List NSGD1MinPrincipleNoLambda3CollapseBlocker
    blockerLedgerIsCanonical :
      blockerLedger ≡ canonicalNSGD1MinPrincipleNoLambda3CollapseBlockers

    blockerCount :
      Nat
    blockerCountIsCanonical :
      blockerCount ≡
      listLength canonicalNSGD1MinPrincipleNoLambda3CollapseBlockers

    gd1MinimumPrincipleText :
      String
    gd1MinimumPrincipleTextIsCanonical :
      gd1MinimumPrincipleText ≡ gd1MinimumPrincipleTextValue

    criticalGapText :
      String
    criticalGapTextIsCanonical :
      criticalGapText ≡ criticalGapTextValue

    supercriticalRestoringText :
      String
    supercriticalRestoringTextIsCanonical :
      supercriticalRestoringText ≡ supercriticalRestoringTextValue

    subcriticalExponentialLowerBoundText :
      String
    subcriticalExponentialLowerBoundTextIsCanonical :
      subcriticalExponentialLowerBoundText
      ≡ subcriticalExponentialLowerBoundTextValue

    lambda3OnBiaxialCarrierText :
      String
    lambda3OnBiaxialCarrierTextIsCanonical :
      lambda3OnBiaxialCarrierText ≡ lambda3OnBiaxialCarrierTextValue

    hDelta1CandidateText :
      String
    hDelta1CandidateTextIsCanonical :
      hDelta1CandidateText ≡ hDelta1CandidateTextValue

    hDelta1Candidate :
      Bool
    hDelta1CandidateIsTrue :
      hDelta1Candidate ≡ true

    exactConstantsDischarged :
      Bool
    exactConstantsDischargedIsFalse :
      exactConstantsDischarged ≡ false

    layerCZDischarged :
      Bool
    layerCZDischargedIsFalse :
      layerCZDischarged ≡ false

    gd1ProofTermsDischarged :
      Bool
    gd1ProofTermsDischargedIsFalse :
      gd1ProofTermsDischarged ≡ false

    exactConstantsCZGD1RequiredText :
      String
    exactConstantsCZGD1RequiredTextIsCanonical :
      exactConstantsCZGD1RequiredText ≡ exactConstantsCZGD1RequiredTextValue

    collapseImpossible :
      Bool
    collapseImpossibleIsFalse :
      collapseImpossible ≡ false

    hDelta1Discharged :
      Bool
    hDelta1DischargedIsFalse :
      hDelta1Discharged ≡ false

    clayNavierStokesPromoted :
      Bool
    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    promotionType :
      NSGD1MinPrinciplePromotion → ⊥
    promotionTypeIsCanonical :
      promotionType ≡ promotionEmptyTypeWitness

    failClosedRouteText :
      String
    failClosedRouteTextIsCanonical :
      failClosedRouteText ≡ failClosedRouteTextValue

open NSGD1MinPrincipleNoLambda3CollapseReceipt public

canonicalNSGD1MinPrincipleNoLambda3CollapseReceipt :
  NSGD1MinPrincipleNoLambda3CollapseReceipt
canonicalNSGD1MinPrincipleNoLambda3CollapseReceipt =
  record
    { status =
        gd1MinimumPrincipleReceiptRecorded
    ; statusIsCanonical =
        refl
    ; stageLedger =
        canonicalNSGD1MinPrincipleNoLambda3CollapseStages
    ; stageLedgerIsCanonical =
        refl
    ; stageCount =
        listLength canonicalNSGD1MinPrincipleNoLambda3CollapseStages
    ; stageCountIsCanonical =
        refl
    ; dependencyNames =
        canonicalNSGD1MinPrincipleNoLambda3CollapseDependencyNames
    ; dependencyNamesIsCanonical =
        refl
    ; dependencyNameCount =
        listLength canonicalNSGD1MinPrincipleNoLambda3CollapseDependencyNames
    ; dependencyNameCountIsCanonical =
        refl
    ; blockerLedger =
        canonicalNSGD1MinPrincipleNoLambda3CollapseBlockers
    ; blockerLedgerIsCanonical =
        refl
    ; blockerCount =
        listLength canonicalNSGD1MinPrincipleNoLambda3CollapseBlockers
    ; blockerCountIsCanonical =
        refl
    ; gd1MinimumPrincipleText =
        gd1MinimumPrincipleTextValue
    ; gd1MinimumPrincipleTextIsCanonical =
        refl
    ; criticalGapText =
        criticalGapTextValue
    ; criticalGapTextIsCanonical =
        refl
    ; supercriticalRestoringText =
        supercriticalRestoringTextValue
    ; supercriticalRestoringTextIsCanonical =
        refl
    ; subcriticalExponentialLowerBoundText =
        subcriticalExponentialLowerBoundTextValue
    ; subcriticalExponentialLowerBoundTextIsCanonical =
        refl
    ; lambda3OnBiaxialCarrierText =
        lambda3OnBiaxialCarrierTextValue
    ; lambda3OnBiaxialCarrierTextIsCanonical =
        refl
    ; hDelta1CandidateText =
        hDelta1CandidateTextValue
    ; hDelta1CandidateTextIsCanonical =
        refl
    ; hDelta1Candidate =
        true
    ; hDelta1CandidateIsTrue =
        refl
    ; exactConstantsDischarged =
        false
    ; exactConstantsDischargedIsFalse =
        refl
    ; layerCZDischarged =
        false
    ; layerCZDischargedIsFalse =
        refl
    ; gd1ProofTermsDischarged =
        false
    ; gd1ProofTermsDischargedIsFalse =
        refl
    ; exactConstantsCZGD1RequiredText =
        exactConstantsCZGD1RequiredTextValue
    ; exactConstantsCZGD1RequiredTextIsCanonical =
        refl
    ; collapseImpossible =
        false
    ; collapseImpossibleIsFalse =
        refl
    ; hDelta1Discharged =
        false
    ; hDelta1DischargedIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; promotionType =
        promotionEmptyTypeWitness
    ; promotionTypeIsCanonical =
        refl
    ; failClosedRouteText =
        failClosedRouteTextValue
    ; failClosedRouteTextIsCanonical =
        refl
    }

gd1RouteKeepsCollapseImpossibleFalse :
  collapseImpossible canonicalNSGD1MinPrincipleNoLambda3CollapseReceipt ≡ false
gd1RouteKeepsCollapseImpossibleFalse =
  refl

gd1RouteKeepsHDelta1DischargedFalse :
  hDelta1Discharged canonicalNSGD1MinPrincipleNoLambda3CollapseReceipt ≡ false
gd1RouteKeepsHDelta1DischargedFalse =
  refl

gd1RouteKeepsClayNavierStokesPromotedFalse :
  clayNavierStokesPromoted canonicalNSGD1MinPrincipleNoLambda3CollapseReceipt ≡ false
gd1RouteKeepsClayNavierStokesPromotedFalse =
  refl
