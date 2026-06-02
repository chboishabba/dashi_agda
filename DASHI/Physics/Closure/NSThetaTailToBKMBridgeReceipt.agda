module DASHI.Physics.Closure.NSThetaTailToBKMBridgeReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.NSAdjacentShellLeakageBoundReceipt as Leak
import DASHI.Physics.Closure.NSDangerShellMaximumPrincipleReceipt as Danger
import DASHI.Physics.Closure.NSDangerShellMaxPrincipleConditionalProofReceipt as Cond
import DASHI.Physics.Closure.NSTailFluxLPIdentityFullDerivationReceipt as Full

------------------------------------------------------------------------
-- Conditional theta-tail to BKM/Serrin bridge receipt.
--
-- This is a bridge, not a regularity proof.  It records that a uniform K*
-- bound plus the conditional danger-shell theta control would give the
-- standard high-frequency tail control needed to route into BKM/Serrin
-- continuation criteria.  The uniform K* bound and continuum criterion
-- discharge are recorded as assumptions/open boundaries.

data TailToBKMBridgeHypothesis : Set where
  conditionalThetaKStarBoundAvailable :
    TailToBKMBridgeHypothesis

  KStarDriftBoundAvailable :
    TailToBKMBridgeHypothesis

  uniformKStarBoundOnInterval :
    TailToBKMBridgeHypothesis

  tailControlStrongEnoughForSobolevExponent :
    TailToBKMBridgeHypothesis

  dyadicTailControlsVorticityLinfinity :
    TailToBKMBridgeHypothesis

  lowShellsControlledByEnergyAndSmoothLocalTheory :
    TailToBKMBridgeHypothesis

  serrinExponentInterpolationAdmissible :
    TailToBKMBridgeHypothesis

canonicalTailToBKMBridgeHypotheses :
  List TailToBKMBridgeHypothesis
canonicalTailToBKMBridgeHypotheses =
  conditionalThetaKStarBoundAvailable
  ∷ KStarDriftBoundAvailable
  ∷ uniformKStarBoundOnInterval
  ∷ tailControlStrongEnoughForSobolevExponent
  ∷ dyadicTailControlsVorticityLinfinity
  ∷ lowShellsControlledByEnergyAndSmoothLocalTheory
  ∷ serrinExponentInterpolationAdmissible
  ∷ []

data TailToBKMBridgeStep : Set where
  importFullFixedKIdentity :
    TailToBKMBridgeStep

  importAdjacentLeakageBoundary :
    TailToBKMBridgeStep

  importDangerShellConditionalThetaControl :
    TailToBKMBridgeStep

  freezeKStarBelowUniformBound :
    TailToBKMBridgeStep

  splitLowShellsAndHighTail :
    TailToBKMBridgeStep

  convertHighTailDecayToVorticityControl :
    TailToBKMBridgeStep

  interpolateToSerrinNorm :
    TailToBKMBridgeStep

  routeToBKMOrSerrinContinuationCriterion :
    TailToBKMBridgeStep

canonicalTailToBKMBridgeSteps :
  List TailToBKMBridgeStep
canonicalTailToBKMBridgeSteps =
  importFullFixedKIdentity
  ∷ importAdjacentLeakageBoundary
  ∷ importDangerShellConditionalThetaControl
  ∷ freezeKStarBelowUniformBound
  ∷ splitLowShellsAndHighTail
  ∷ convertHighTailDecayToVorticityControl
  ∷ interpolateToSerrinNorm
  ∷ routeToBKMOrSerrinContinuationCriterion
  ∷ []

data TailToBKMBridgeConclusion : Set where
  conditionalTailControlFeedsBKMOrSerrin :
    TailToBKMBridgeConclusion

tailToBKMBridge :
  List TailToBKMBridgeHypothesis →
  List TailToBKMBridgeStep →
  TailToBKMBridgeConclusion
tailToBKMBridge hypotheses steps =
  conditionalTailControlFeedsBKMOrSerrin

data TailToBKMBridgeOpenBoundary : Set where
  KStarDriftBoundNotProvedHere :
    TailToBKMBridgeOpenBoundary

  uniformKStarBoundNotProvedHere :
    TailToBKMBridgeOpenBoundary

  tailControlAtSobolevExponentNotProvedHere :
    TailToBKMBridgeOpenBoundary

  tailToVorticityMultiplierBoundNotProvedHere :
    TailToBKMBridgeOpenBoundary

  continuumBKMCriterionNotDischargedHere :
    TailToBKMBridgeOpenBoundary

  serrinCriterionNotDischargedHere :
    TailToBKMBridgeOpenBoundary

  noClayNavierStokesPromotion :
    TailToBKMBridgeOpenBoundary

canonicalTailToBKMBridgeOpenBoundaries :
  List TailToBKMBridgeOpenBoundary
canonicalTailToBKMBridgeOpenBoundaries =
  KStarDriftBoundNotProvedHere
  ∷ uniformKStarBoundNotProvedHere
  ∷ tailControlAtSobolevExponentNotProvedHere
  ∷ tailToVorticityMultiplierBoundNotProvedHere
  ∷ continuumBKMCriterionNotDischargedHere
  ∷ serrinCriterionNotDischargedHere
  ∷ noClayNavierStokesPromotion
  ∷ []

data TailToBKMPromotion : Set where

tailToBKMPromotionImpossibleHere :
  TailToBKMPromotion →
  ⊥
tailToBKMPromotionImpossibleHere ()

tailToBKMFormula :
  String
tailToBKMFormula =
  "Conditionally: theta_K* < 1 plus KStarDriftBound, a uniform K* bound, and tail control strong enough for the Sobolev/Serrin exponent control the high-frequency tail; with tail-to-vorticity and interpolation estimates this routes to BKM/Serrin continuation."

tailToBKMBoundary :
  String
tailToBKMBoundary =
  "KStarDriftBound, the uniform K* bound, Sobolev-exponent tail control, tail-to-vorticity estimate, and BKM/Serrin criterion discharge are not proved here; no Clay promotion is made."

record NSThetaTailToBKMBridgeReceipt (K : Nat) : Setω where
  field
    fullIdentityReceipt :
      Full.NSTailFluxLPIdentityFullDerivationReceipt K

    fullIdentityNoClay :
      Full.clayNavierStokesPromoted fullIdentityReceipt ≡ false

    adjacentLeakageReceipt :
      Leak.NSAdjacentShellLeakageBoundReceipt K

    adjacentLeakageNoClay :
      Leak.clayNavierStokesPromoted adjacentLeakageReceipt ≡ false

    dangerShellReceipt :
      Danger.NSDangerShellMaximumPrincipleReceipt

    dangerShellStillOpen :
      Danger.dangerShellMaxPrincipleProved dangerShellReceipt ≡ false

    conditionalMaxReceipt :
      Cond.NSDangerShellMaxPrincipleConditionalProofReceipt K

    conditionalMaxRecorded :
      Cond.conditionalMaxPrincipleProofRecorded conditionalMaxReceipt
      ≡
      true

    conditionalMaxNoClay :
      Cond.clayNavierStokesPromoted conditionalMaxReceipt ≡ false

    hypotheses :
      List TailToBKMBridgeHypothesis

    hypothesesAreCanonical :
      hypotheses ≡ canonicalTailToBKMBridgeHypotheses

    bridgeSteps :
      List TailToBKMBridgeStep

    bridgeStepsAreCanonical :
      bridgeSteps ≡ canonicalTailToBKMBridgeSteps

    conclusion :
      TailToBKMBridgeConclusion

    conclusionIsDerived :
      conclusion ≡ tailToBKMBridge hypotheses bridgeSteps

    openBoundaries :
      List TailToBKMBridgeOpenBoundary

    openBoundariesAreCanonical :
      openBoundaries ≡ canonicalTailToBKMBridgeOpenBoundaries

    formula :
      String

    formulaIsCanonical :
      formula ≡ tailToBKMFormula

    boundary :
      String

    boundaryIsCanonical :
      boundary ≡ tailToBKMBoundary

    kStarBoundAssumed :
      Bool

    kStarBoundAssumedIsTrue :
      kStarBoundAssumed ≡ true

    kStarDriftBoundAssumed :
      Bool

    kStarDriftBoundAssumedIsTrue :
      kStarDriftBoundAssumed ≡ true

    tailControlEnoughForSobolevExponentAssumed :
      Bool

    tailControlEnoughForSobolevExponentAssumedIsTrue :
      tailControlEnoughForSobolevExponentAssumed ≡ true

    tailToBKMBridgeConditionallyRecorded :
      Bool

    tailToBKMBridgeConditionallyRecordedIsTrue :
      tailToBKMBridgeConditionallyRecorded ≡ true

    bkmCriterionDischarged :
      Bool

    bkmCriterionDischargedIsFalse :
      bkmCriterionDischarged ≡ false

    serrinCriterionDischarged :
      Bool

    serrinCriterionDischargedIsFalse :
      serrinCriterionDischarged ≡ false

    KStarDriftBoundProvedHere :
      Bool

    KStarDriftBoundProvedHereIsFalse :
      KStarDriftBoundProvedHere ≡ false

    sobolevExponentTailControlProvedHere :
      Bool

    sobolevExponentTailControlProvedHereIsFalse :
      sobolevExponentTailControlProvedHere ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    promotions :
      List TailToBKMPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      TailToBKMPromotion →
      ⊥

open NSThetaTailToBKMBridgeReceipt public

canonicalNSThetaTailToBKMBridgeReceipt :
  NSThetaTailToBKMBridgeReceipt zero
canonicalNSThetaTailToBKMBridgeReceipt =
  record
    { fullIdentityReceipt =
        Full.canonicalNSTailFluxLPIdentityFullDerivationReceipt
    ; fullIdentityNoClay =
        refl
    ; adjacentLeakageReceipt =
        Leak.canonicalNSAdjacentShellLeakageBoundReceipt
    ; adjacentLeakageNoClay =
        refl
    ; dangerShellReceipt =
        Danger.canonicalNSDangerShellMaximumPrincipleReceipt
    ; dangerShellStillOpen =
        refl
    ; conditionalMaxReceipt =
        Cond.canonicalNSDangerShellMaxPrincipleConditionalProofReceipt
    ; conditionalMaxRecorded =
        refl
    ; conditionalMaxNoClay =
        refl
    ; hypotheses =
        canonicalTailToBKMBridgeHypotheses
    ; hypothesesAreCanonical =
        refl
    ; bridgeSteps =
        canonicalTailToBKMBridgeSteps
    ; bridgeStepsAreCanonical =
        refl
    ; conclusion =
        conditionalTailControlFeedsBKMOrSerrin
    ; conclusionIsDerived =
        refl
    ; openBoundaries =
        canonicalTailToBKMBridgeOpenBoundaries
    ; openBoundariesAreCanonical =
        refl
    ; formula =
        tailToBKMFormula
    ; formulaIsCanonical =
        refl
    ; boundary =
        tailToBKMBoundary
    ; boundaryIsCanonical =
        refl
    ; kStarBoundAssumed =
        true
    ; kStarBoundAssumedIsTrue =
        refl
    ; kStarDriftBoundAssumed =
        true
    ; kStarDriftBoundAssumedIsTrue =
        refl
    ; tailControlEnoughForSobolevExponentAssumed =
        true
    ; tailControlEnoughForSobolevExponentAssumedIsTrue =
        refl
    ; tailToBKMBridgeConditionallyRecorded =
        true
    ; tailToBKMBridgeConditionallyRecordedIsTrue =
        refl
    ; bkmCriterionDischarged =
        false
    ; bkmCriterionDischargedIsFalse =
        refl
    ; serrinCriterionDischarged =
        false
    ; serrinCriterionDischargedIsFalse =
        refl
    ; KStarDriftBoundProvedHere =
        false
    ; KStarDriftBoundProvedHereIsFalse =
        refl
    ; sobolevExponentTailControlProvedHere =
        false
    ; sobolevExponentTailControlProvedHereIsFalse =
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
        tailToBKMPromotionImpossibleHere
    }

canonicalTailToBKMBridgeHasKStarBoundAssumption :
  kStarBoundAssumed canonicalNSThetaTailToBKMBridgeReceipt ≡ true
canonicalTailToBKMBridgeHasKStarBoundAssumption =
  refl

canonicalTailToBKMBridgeNoClayPromotion :
  clayNavierStokesPromoted canonicalNSThetaTailToBKMBridgeReceipt ≡ false
canonicalTailToBKMBridgeNoClayPromotion =
  refl
