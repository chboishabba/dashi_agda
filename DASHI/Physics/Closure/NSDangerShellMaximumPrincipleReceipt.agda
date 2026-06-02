module DASHI.Physics.Closure.NSDangerShellMaximumPrincipleReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.DangerScaleEdgeConservationReceipt as Edge
import DASHI.Physics.Closure.NSTailFluxAbsorptionMarginReceipt as Margin
import DASHI.Physics.Closure.NSTailFluxLPIdentityAnalyticReceipt as LP
import DASHI.Physics.Closure.ScaleGraphBarrierTargetReceipt as Barrier

------------------------------------------------------------------------
-- NS danger-shell maximum principle target.
--
-- The danger shell is the profile argmax of theta(K,t), computed after the
-- fixed-K LP identity is available.  This receipt proves only the formal
-- implication from the maximum-principle hypothesis to preservation of
-- theta<1; the analytic inequality at the danger shell remains open.

data DangerShellSelection : Set where
  argmaxMayBeNonUniqueChooseMeasurableSelector :
    DangerShellSelection

  computedAfterFixedKThetaProfile :
    DangerShellSelection

canonicalDangerShellSelections :
  List DangerShellSelection
canonicalDangerShellSelections =
  argmaxMayBeNonUniqueChooseMeasurableSelector
  ∷ computedAfterFixedKThetaProfile
  ∷ []

data NSDangerShellIngredient : Set where
  thetaKIsFluxOverDissWithPositiveDiss :
    NSDangerShellIngredient

  dangerShellRealizesThetaSupremum :
    NSDangerShellIngredient

  edgeLeakageIsAdjacentShellFluxTransfer :
    NSDangerShellIngredient

  noHiddenHighHighSourceAtDangerShell :
    NSDangerShellIngredient

  cMinusEpsilonStrictlyPositive :
    NSDangerShellIngredient

canonicalNSDangerShellIngredients :
  List NSDangerShellIngredient
canonicalNSDangerShellIngredients =
  thetaKIsFluxOverDissWithPositiveDiss
  ∷ dangerShellRealizesThetaSupremum
  ∷ edgeLeakageIsAdjacentShellFluxTransfer
  ∷ noHiddenHighHighSourceAtDangerShell
  ∷ cMinusEpsilonStrictlyPositive
  ∷ []

data DangerShellMaximumPrincipleHypothesis : Set where
  dangerShellDerivativeBoundedByNegativeMargin :
    DangerShellMaximumPrincipleHypothesis

data ThetaBelowOneInitialCondition : Set where
  thetaDangerShellInitiallyStrictlyBelowOne :
    ThetaBelowOneInitialCondition

data ThetaBelowOnePreservationConclusion : Set where
  thetaDangerShellRemainsStrictlyBelowOne :
    ThetaBelowOnePreservationConclusion

dangerShellMaximumPrincipleImplication :
  DangerShellMaximumPrincipleHypothesis →
  ThetaBelowOneInitialCondition →
  ThetaBelowOnePreservationConclusion
dangerShellMaximumPrincipleImplication
  dangerShellDerivativeBoundedByNegativeMargin
  thetaDangerShellInitiallyStrictlyBelowOne =
  thetaDangerShellRemainsStrictlyBelowOne

data NSDangerShellOpenObligation : Set where
  proveLittlewoodPaleyDangerShellCommutatorEstimate :
    NSDangerShellOpenObligation

  proveAdjacentShellEdgeLeakageBound :
    NSDangerShellOpenObligation

  proveNoHiddenProductionAtDangerShell :
    NSDangerShellOpenObligation

  proveThetaPreservationFromRealNSEvolution :
    NSDangerShellOpenObligation

canonicalNSDangerShellOpenObligations :
  List NSDangerShellOpenObligation
canonicalNSDangerShellOpenObligations =
  proveLittlewoodPaleyDangerShellCommutatorEstimate
  ∷ proveAdjacentShellEdgeLeakageBound
  ∷ proveNoHiddenProductionAtDangerShell
  ∷ proveThetaPreservationFromRealNSEvolution
  ∷ []

data DangerShellPromotion : Set where

dangerShellPromotionImpossibleHere :
  DangerShellPromotion →
  ⊥
dangerShellPromotionImpossibleHere ()

dangerShellFormula :
  String
dangerShellFormula =
  "At K*=argmax_K theta(K,t), prove d/dt theta_K* <= -(c-epsilon) M_K* with epsilon<c; this is the NS5 analytic target."

edgeLeakageFormula :
  String
edgeLeakageFormula =
  "The epsilon term is adjacent-shell cascade leakage. The proof must exclude hidden high-high production at the danger shell."

record NSDangerShellMaximumPrincipleReceipt : Setω where
  field
    lpIdentityReceipt :
      LP.NSTailFluxLPIdentityAnalyticReceipt zero

    lpIdentityReceiptIsCanonical :
      lpIdentityReceipt ≡ LP.canonicalNSTailFluxLPIdentityAnalyticReceipt

    barrierTarget :
      Barrier.ScaleGraphBarrierTargetReceipt

    barrierTargetNoClay :
      Barrier.clayPromotion barrierTarget ≡ false

    edgeConservation :
      Edge.DangerScaleEdgeConservationReceipt

    edgeConservationNoClay :
      Edge.clayPromotion edgeConservation ≡ false

    selection :
      List DangerShellSelection

    selectionIsCanonical :
      selection ≡ canonicalDangerShellSelections

    ingredients :
      List NSDangerShellIngredient

    ingredientsAreCanonical :
      ingredients ≡ canonicalNSDangerShellIngredients

    hypothesis :
      DangerShellMaximumPrincipleHypothesis

    initialThetaBelowOne :
      ThetaBelowOneInitialCondition

    formalImplication :
      ThetaBelowOnePreservationConclusion

    formalImplicationIsCanonical :
      formalImplication
      ≡
      dangerShellMaximumPrincipleImplication hypothesis initialThetaBelowOne

    openObligations :
      List NSDangerShellOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalNSDangerShellOpenObligations

    formula :
      String

    formulaIsCanonical :
      formula ≡ dangerShellFormula

    edgeLeakageStatement :
      String

    edgeLeakageStatementIsCanonical :
      edgeLeakageStatement ≡ edgeLeakageFormula

    dangerShellMaxPrinciplePreciselyStated :
      Bool

    dangerShellMaxPrinciplePreciselyStatedIsTrue :
      dangerShellMaxPrinciplePreciselyStated ≡ true

    dangerShellMaxPrincipleProved :
      Bool

    dangerShellMaxPrincipleProvedIsFalse :
      dangerShellMaxPrincipleProved ≡ false

    edgeLeakageBoundOpen :
      Bool

    edgeLeakageBoundOpenIsTrue :
      edgeLeakageBoundOpen ≡ true

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    promotions :
      List DangerShellPromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      DangerShellPromotion →
      ⊥

open NSDangerShellMaximumPrincipleReceipt public

canonicalNSDangerShellMaximumPrincipleReceipt :
  NSDangerShellMaximumPrincipleReceipt
canonicalNSDangerShellMaximumPrincipleReceipt =
  record
    { lpIdentityReceipt =
        LP.canonicalNSTailFluxLPIdentityAnalyticReceipt
    ; lpIdentityReceiptIsCanonical =
        refl
    ; barrierTarget =
        Barrier.canonicalScaleGraphBarrierTargetReceipt
    ; barrierTargetNoClay =
        refl
    ; edgeConservation =
        Edge.canonicalDangerScaleEdgeConservationReceipt
    ; edgeConservationNoClay =
        refl
    ; selection =
        canonicalDangerShellSelections
    ; selectionIsCanonical =
        refl
    ; ingredients =
        canonicalNSDangerShellIngredients
    ; ingredientsAreCanonical =
        refl
    ; hypothesis =
        dangerShellDerivativeBoundedByNegativeMargin
    ; initialThetaBelowOne =
        thetaDangerShellInitiallyStrictlyBelowOne
    ; formalImplication =
        thetaDangerShellRemainsStrictlyBelowOne
    ; formalImplicationIsCanonical =
        refl
    ; openObligations =
        canonicalNSDangerShellOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; formula =
        dangerShellFormula
    ; formulaIsCanonical =
        refl
    ; edgeLeakageStatement =
        edgeLeakageFormula
    ; edgeLeakageStatementIsCanonical =
        refl
    ; dangerShellMaxPrinciplePreciselyStated =
        true
    ; dangerShellMaxPrinciplePreciselyStatedIsTrue =
        refl
    ; dangerShellMaxPrincipleProved =
        false
    ; dangerShellMaxPrincipleProvedIsFalse =
        refl
    ; edgeLeakageBoundOpen =
        true
    ; edgeLeakageBoundOpenIsTrue =
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
        dangerShellPromotionImpossibleHere
    }

canonicalDangerShellMaxPrincipleStillOpen :
  dangerShellMaxPrincipleProved canonicalNSDangerShellMaximumPrincipleReceipt
  ≡ false
canonicalDangerShellMaxPrincipleStillOpen =
  refl
