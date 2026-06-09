module DASHI.Physics.Closure.NSTailFluxIdentityAnalyticTargetReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSTailFluxAbsorptionMarginReceipt as Margin

------------------------------------------------------------------------
-- Navier-Stokes fixed-K tail-flux identity analytic target.
--
-- This receipt separates the analytic Littlewood-Paley obligation from the
-- already recorded NS tail-margin surface.
--
-- Target identity, for a fixed shell cutoff K selected before
-- differentiation:
--
--   d/dt E_{>K}(u(t))
--     = - Diss_{>K}(u(t)) + Flux_{>K}(u(t)).
--
-- The receipt records what the proof must discharge:
--
--   * a fixed Littlewood-Paley/shell decomposition;
--   * differentiation of the fixed cutoff tail energy;
--   * the viscous contribution with the correct negative sign;
--   * the projected nonlinear flux contribution;
--   * no hidden moving-cutoff boundary term;
--   * no promotion from runtime theta diagnostics to an analytic theorem.
--
-- It does not prove the PDE identity, does not prove the paraproduct flux
-- bound, does not prove theta < 1, and does not promote Navier-Stokes
-- regularity or Clay closure.

data NSSmoothFlowInput : Set where
  smoothDivergenceFreeVelocity :
    NSSmoothFlowInput

  fixedViscosityNuPositive :
    NSSmoothFlowInput

  fixedObservationInterval :
    NSSmoothFlowInput

canonicalNSSmoothFlowInputs :
  List NSSmoothFlowInput
canonicalNSSmoothFlowInputs =
  smoothDivergenceFreeVelocity
  ∷ fixedViscosityNuPositive
  ∷ fixedObservationInterval
  ∷ []

data FixedKLittlewoodPaleyIngredient : Set where
  shellProjectorsSelected :
    FixedKLittlewoodPaleyIngredient

  shellWeightsSelected :
    FixedKLittlewoodPaleyIngredient

  cutoffKSelectedBeforeDifferentiation :
    FixedKLittlewoodPaleyIngredient

  tailEnergyDefinedAsFixedCutoffSum :
    FixedKLittlewoodPaleyIngredient

  tailDissipationDefinedWithLaplacianWeights :
    FixedKLittlewoodPaleyIngredient

  nonlinearTailFluxDefinedWithProjectedNonlinearity :
    FixedKLittlewoodPaleyIngredient

canonicalFixedKLPIngredients :
  List FixedKLittlewoodPaleyIngredient
canonicalFixedKLPIngredients =
  shellProjectorsSelected
  ∷ shellWeightsSelected
  ∷ cutoffKSelectedBeforeDifferentiation
  ∷ tailEnergyDefinedAsFixedCutoffSum
  ∷ tailDissipationDefinedWithLaplacianWeights
  ∷ nonlinearTailFluxDefinedWithProjectedNonlinearity
  ∷ []

data FixedKTailFluxProofObligation : Set where
  differentiateTailEnergyTermwise :
    FixedKTailFluxProofObligation

  substituteProjectedNavierStokesEquation :
    FixedKTailFluxProofObligation

  useSelfAdjointnessOfShellProjectors :
    FixedKTailFluxProofObligation

  integrateByPartsForViscousSign :
    FixedKTailFluxProofObligation

  useDivergenceFreeProjectionForPressure :
    FixedKTailFluxProofObligation

  isolateNonlinearFluxWithAbsoluteValueLater :
    FixedKTailFluxProofObligation

  excludeMovingCutoffBoundaryTerms :
    FixedKTailFluxProofObligation

canonicalFixedKTailFluxProofObligations :
  List FixedKTailFluxProofObligation
canonicalFixedKTailFluxProofObligations =
  differentiateTailEnergyTermwise
  ∷ substituteProjectedNavierStokesEquation
  ∷ useSelfAdjointnessOfShellProjectors
  ∷ integrateByPartsForViscousSign
  ∷ useDivergenceFreeProjectionForPressure
  ∷ isolateNonlinearFluxWithAbsoluteValueLater
  ∷ excludeMovingCutoffBoundaryTerms
  ∷ []

data AnalyticIdentityStatus : Set where
  fixedKAnalyticTargetRecorded_proofStillOpen :
    AnalyticIdentityStatus

data RuntimeDiagnosticConsumptionBoundary : Set where
  thetaProfileEvidenceOnly :
    RuntimeDiagnosticConsumptionBoundary

  dangerShellComputedAfterFixedKProfile :
    RuntimeDiagnosticConsumptionBoundary

  runtimeThetaNotLittlewoodPaleyProof :
    RuntimeDiagnosticConsumptionBoundary

  observedThetaLessThanOneNotTheorem :
    RuntimeDiagnosticConsumptionBoundary

canonicalRuntimeDiagnosticConsumptionBoundaries :
  List RuntimeDiagnosticConsumptionBoundary
canonicalRuntimeDiagnosticConsumptionBoundaries =
  thetaProfileEvidenceOnly
  ∷ dangerShellComputedAfterFixedKProfile
  ∷ runtimeThetaNotLittlewoodPaleyProof
  ∷ observedThetaLessThanOneNotTheorem
  ∷ []

data NSTailFluxIdentityPromotion : Set where

tailFluxIdentityPromotionImpossibleHere :
  NSTailFluxIdentityPromotion →
  ⊥
tailFluxIdentityPromotionImpossibleHere ()

analyticTargetBoundaryStatement :
  String
analyticTargetBoundaryStatement =
  "This receipt records the fixed-K Littlewood-Paley tail-flux identity as an analytic target; the PDE proof is not inhabited here."

fixedKBoundaryStatement :
  String
fixedKBoundaryStatement =
  "K is fixed before differentiation. Moving cutoffs and danger-shell argmaxes are diagnostics computed after the fixed-K profile."

runtimeBoundaryStatement :
  String
runtimeBoundaryStatement =
  "dashiCFD theta profiles are evidence-only runtime diagnostics; they do not prove the LP identity, theta preservation, BKM continuation, or Clay regularity."

record NSTailFluxIdentityAnalyticTargetReceipt (K : Nat) : Set where
  field
    status :
      AnalyticIdentityStatus

    statusIsTargetOpen :
      status ≡ fixedKAnalyticTargetRecorded_proofStillOpen

    marginIdentitySurface :
      Margin.TailFluxIdentity_K K

    marginIdentitySurfaceIsCanonical :
      marginIdentitySurface ≡ Margin.canonicalTailFluxIdentity K

    fixedKSemantics :
      List Margin.FixedKSemantics

    fixedKSemanticsAreCanonical :
      fixedKSemantics ≡ Margin.canonicalFixedKSemantics

    smoothFlowInputs :
      List NSSmoothFlowInput

    smoothFlowInputsAreCanonical :
      smoothFlowInputs ≡ canonicalNSSmoothFlowInputs

    lpIngredients :
      List FixedKLittlewoodPaleyIngredient

    lpIngredientsAreCanonical :
      lpIngredients ≡ canonicalFixedKLPIngredients

    proofObligations :
      List FixedKTailFluxProofObligation

    proofObligationsAreCanonical :
      proofObligations ≡ canonicalFixedKTailFluxProofObligations

    runtimeConsumptionBoundaries :
      List RuntimeDiagnosticConsumptionBoundary

    runtimeConsumptionBoundariesAreCanonical :
      runtimeConsumptionBoundaries
        ≡ canonicalRuntimeDiagnosticConsumptionBoundaries

    analyticTargetStatement :
      String

    analyticTargetStatementIsCanonical :
      analyticTargetStatement ≡ analyticTargetBoundaryStatement

    fixedKStatement :
      String

    fixedKStatementIsCanonical :
      fixedKStatement ≡ fixedKBoundaryStatement

    runtimeStatement :
      String

    runtimeStatementIsCanonical :
      runtimeStatement ≡ runtimeBoundaryStatement

    lpIdentityProvedHere :
      Bool

    lpIdentityProvedHereIsFalse :
      lpIdentityProvedHere ≡ false

    paraproductFluxBoundProvedHere :
      Bool

    paraproductFluxBoundProvedHereIsFalse :
      paraproductFluxBoundProvedHere ≡ false

    thetaLessThanOneProvedHere :
      Bool

    thetaLessThanOneProvedHereIsFalse :
      thetaLessThanOneProvedHere ≡ false

    thetaPreservationProvedHere :
      Bool

    thetaPreservationProvedHereIsFalse :
      thetaPreservationProvedHere ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    promotions :
      List NSTailFluxIdentityPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      NSTailFluxIdentityPromotion →
      ⊥

open NSTailFluxIdentityAnalyticTargetReceipt public

canonicalNSTailFluxIdentityAnalyticTargetReceipt :
  NSTailFluxIdentityAnalyticTargetReceipt zero
canonicalNSTailFluxIdentityAnalyticTargetReceipt =
  record
    { status =
        fixedKAnalyticTargetRecorded_proofStillOpen
    ; statusIsTargetOpen =
        refl
    ; marginIdentitySurface =
        Margin.canonicalTailFluxIdentity zero
    ; marginIdentitySurfaceIsCanonical =
        refl
    ; fixedKSemantics =
        Margin.canonicalFixedKSemantics
    ; fixedKSemanticsAreCanonical =
        refl
    ; smoothFlowInputs =
        canonicalNSSmoothFlowInputs
    ; smoothFlowInputsAreCanonical =
        refl
    ; lpIngredients =
        canonicalFixedKLPIngredients
    ; lpIngredientsAreCanonical =
        refl
    ; proofObligations =
        canonicalFixedKTailFluxProofObligations
    ; proofObligationsAreCanonical =
        refl
    ; runtimeConsumptionBoundaries =
        canonicalRuntimeDiagnosticConsumptionBoundaries
    ; runtimeConsumptionBoundariesAreCanonical =
        refl
    ; analyticTargetStatement =
        analyticTargetBoundaryStatement
    ; analyticTargetStatementIsCanonical =
        refl
    ; fixedKStatement =
        fixedKBoundaryStatement
    ; fixedKStatementIsCanonical =
        refl
    ; runtimeStatement =
        runtimeBoundaryStatement
    ; runtimeStatementIsCanonical =
        refl
    ; lpIdentityProvedHere =
        false
    ; lpIdentityProvedHereIsFalse =
        refl
    ; paraproductFluxBoundProvedHere =
        false
    ; paraproductFluxBoundProvedHereIsFalse =
        refl
    ; thetaLessThanOneProvedHere =
        false
    ; thetaLessThanOneProvedHereIsFalse =
        refl
    ; thetaPreservationProvedHere =
        false
    ; thetaPreservationProvedHereIsFalse =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; promotions =
        []
    ; promotionsAreEmpty =
        refl
    ; noPromotionPossibleHere =
        tailFluxIdentityPromotionImpossibleHere
    }

canonicalNSTailFluxIdentityTargetOpen :
  lpIdentityProvedHere canonicalNSTailFluxIdentityAnalyticTargetReceipt ≡ false
canonicalNSTailFluxIdentityTargetOpen =
  refl

canonicalNSTailFluxIdentityNoThetaPromotion :
  thetaLessThanOneProvedHere canonicalNSTailFluxIdentityAnalyticTargetReceipt
    ≡ false
canonicalNSTailFluxIdentityNoThetaPromotion =
  refl

canonicalNSTailFluxIdentityNoClayPromotion :
  clayNavierStokesPromoted canonicalNSTailFluxIdentityAnalyticTargetReceipt
    ≡ false
canonicalNSTailFluxIdentityNoClayPromotion =
  refl
