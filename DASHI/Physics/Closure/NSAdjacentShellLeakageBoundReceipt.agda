module DASHI.Physics.Closure.NSAdjacentShellLeakageBoundReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.AdjacentOnlyVortexStretchingReceipt as Adjacent
import DASHI.Physics.Closure.NSDangerShellMaximumPrincipleReceipt as Danger
import DASHI.Physics.Closure.NSTailFluxAbsorptionMarginReceipt as Margin
import DASHI.Physics.Closure.NSTailFluxLPIdentityFullDerivationReceipt as Full

------------------------------------------------------------------------
-- Adjacent-shell leakage bound receipt.
--
-- This is the analytic receipt adjacent to the full fixed-K identity.  It
-- states the shell-local leakage estimate conditionally: only j = K-1,K,K+1
-- transport contributes to the danger-shell leakage term, and that leakage is
-- absorbable by epsilon times the fixed-K dissipation under the listed
-- paraproduct/localisation hypotheses.  It does not prove theta preservation
-- or any Clay Navier-Stokes statement.

data AdjacentShellLeakageHypothesis : Set where
  dyadicParaproductLocalisation :
    AdjacentShellLeakageHypothesis

  sameLaneAdjacentShellSupportOnly :
    AdjacentShellLeakageHypothesis

  highHighRemainderExcludedAtDangerShell :
    AdjacentShellLeakageHypothesis

  commutatorConstantsUniformAtFixedK :
    AdjacentShellLeakageHypothesis

  shellEnvelopeFiniteOnObservationInterval :
    AdjacentShellLeakageHypothesis

  epsilonStrictlyBelowDangerMargin :
    AdjacentShellLeakageHypothesis

canonicalAdjacentShellLeakageHypotheses :
  List AdjacentShellLeakageHypothesis
canonicalAdjacentShellLeakageHypotheses =
  dyadicParaproductLocalisation
  ∷ sameLaneAdjacentShellSupportOnly
  ∷ highHighRemainderExcludedAtDangerShell
  ∷ commutatorConstantsUniformAtFixedK
  ∷ shellEnvelopeFiniteOnObservationInterval
  ∷ epsilonStrictlyBelowDangerMargin
  ∷ []

data AdjacentShellLeakageSignFact : Set where
  outgoingLeakageHasNegativeSignForSourceShell :
    AdjacentShellLeakageSignFact

  incomingLeakageHasPositiveSignForTargetShell :
    AdjacentShellLeakageSignFact

  pairedAdjacentLeakageCancelsInInteriorSum :
    AdjacentShellLeakageSignFact

  boundaryLeakageIsAbsorbedAsEpsilonDissipation :
    AdjacentShellLeakageSignFact

  hiddenHighHighSourceSignIsUnavailableAndExcluded :
    AdjacentShellLeakageSignFact

canonicalAdjacentShellLeakageSignFacts :
  List AdjacentShellLeakageSignFact
canonicalAdjacentShellLeakageSignFacts =
  outgoingLeakageHasNegativeSignForSourceShell
  ∷ incomingLeakageHasPositiveSignForTargetShell
  ∷ pairedAdjacentLeakageCancelsInInteriorSum
  ∷ boundaryLeakageIsAbsorbedAsEpsilonDissipation
  ∷ hiddenHighHighSourceSignIsUnavailableAndExcluded
  ∷ []

data AdjacentShellComputedDiagnostic : Set where
  lowHighParaproductRatioBelowThetaBarrier :
    AdjacentShellComputedDiagnostic

  highHighParaproductCrossesThetaBarrierInDangerRegimes :
    AdjacentShellComputedDiagnostic

  highHighBarrierCrossingOccursForSmallNuLargeShell :
    AdjacentShellComputedDiagnostic

  adjacentLeakageIsNotTheComputedBarrierCrossing :
    AdjacentShellComputedDiagnostic

canonicalAdjacentShellComputedDiagnostics :
  List AdjacentShellComputedDiagnostic
canonicalAdjacentShellComputedDiagnostics =
  lowHighParaproductRatioBelowThetaBarrier
  ∷ highHighParaproductCrossesThetaBarrierInDangerRegimes
  ∷ highHighBarrierCrossingOccursForSmallNuLargeShell
  ∷ adjacentLeakageIsNotTheComputedBarrierCrossing
  ∷ []

data AdjacentShellLeakageBound : Nat → Set where
  adjacentShellLeakageAbsorbedByEpsilonDissipation :
    (K : Nat) →
    Margin.Diss_K K →
    AdjacentShellLeakageBound K

data AdjacentShellAbsorptionBudget : Nat → Set where
  fixedKAbsorptionBudgetFromDissipation :
    (K : Nat) →
    Margin.Diss_K K →
    AdjacentShellAbsorptionBudget K

data AdjacentShellEdgeInfluxBound : Nat → Set where
  adjacentShellEdgeInfluxAbsorbedByEpsilonAbsorption :
    (K : Nat) →
    AdjacentShellAbsorptionBudget K →
    AdjacentShellEdgeInfluxBound K

canonicalAdjacentShellLeakageBound :
  (K : Nat) →
  AdjacentShellLeakageBound K
canonicalAdjacentShellLeakageBound K =
  adjacentShellLeakageAbsorbedByEpsilonDissipation
    K
    (Margin.viscousDissipation K)

canonicalAdjacentShellEdgeInfluxBound :
  (K : Nat) →
  AdjacentShellEdgeInfluxBound K
canonicalAdjacentShellEdgeInfluxBound K =
  adjacentShellEdgeInfluxAbsorbedByEpsilonAbsorption
    K
    (fixedKAbsorptionBudgetFromDissipation K (Margin.viscousDissipation K))

data AdjacentShellLeakageBoundary : Set where
  conditionalAnalyticEstimateOnly :
    AdjacentShellLeakageBoundary

  dependsOnFullFixedKIdentity :
    AdjacentShellLeakageBoundary

  noMovingCutoffEstimate :
    AdjacentShellLeakageBoundary

  noThetaPreservationTheorem :
    AdjacentShellLeakageBoundary

  noHiddenHighHighProductionAllowed :
    AdjacentShellLeakageBoundary

  noClayNavierStokesPromotion :
    AdjacentShellLeakageBoundary

canonicalAdjacentShellLeakageBoundaries :
  List AdjacentShellLeakageBoundary
canonicalAdjacentShellLeakageBoundaries =
  conditionalAnalyticEstimateOnly
  ∷ dependsOnFullFixedKIdentity
  ∷ noMovingCutoffEstimate
  ∷ noThetaPreservationTheorem
  ∷ noHiddenHighHighProductionAllowed
  ∷ noClayNavierStokesPromotion
  ∷ []

data AdjacentShellLeakagePromotion : Set where

adjacentShellLeakagePromotionImpossibleHere :
  AdjacentShellLeakagePromotion →
  ⊥
adjacentShellLeakagePromotionImpossibleHere ()

adjacentShellLeakageFormula :
  String
adjacentShellLeakageFormula =
  "Conditionally at fixed K: |Leak_{K-1,K,K+1}| <= epsilon Diss_{>K}, with epsilon below the danger-shell margin."

adjacentShellEdgeInfluxFormula :
  String
adjacentShellEdgeInfluxFormula =
  "Target edge-influx bound: I_{K-1 -> K} <= epsilon A_{>K}, where A is the fixed-K absorption/dissipation budget and epsilon is below the danger-shell margin."

adjacentShellLeakageSignFormula :
  String
adjacentShellLeakageSignFormula =
  "Adjacent transfers have opposite signs on neighbouring shells; only the boundary leakage remains and is booked as epsilon Diss, while hidden high-high production is excluded as a hypothesis."

adjacentShellComputedDiagnosticFormula :
  String
adjacentShellComputedDiagnosticFormula =
  "Computed diagnostic split: the low-high paraproduct ratio stays below theta=1, while the high-high term crosses/exceeds the barrier in small-nu, large-shell danger regimes; adjacent leakage is not the observed barrier-crossing mechanism."

record NSAdjacentShellLeakageBoundReceipt (K : Nat) : Setω where
  field
    fullIdentityReceipt :
      Full.NSTailFluxLPIdentityFullDerivationReceipt K

    fullIdentityDerived :
      Full.lpIdentityDerivedHere fullIdentityReceipt ≡ true

    fullIdentityNoClay :
      Full.clayNavierStokesPromoted fullIdentityReceipt ≡ false

    dangerShellReceipt :
      Danger.NSDangerShellMaximumPrincipleReceipt

    dangerShellStillOpen :
      Danger.dangerShellMaxPrincipleProved dangerShellReceipt ≡ false

    adjacentOnlyDiagnostic :
      Adjacent.AdjacentOnlyVortexStretchingReceipt

    adjacentOnlyNoClay :
      Adjacent.clayNavierStokesPromoted adjacentOnlyDiagnostic ≡ false

    leakageBound :
      AdjacentShellLeakageBound K

    leakageBoundIsCanonical :
      leakageBound ≡ canonicalAdjacentShellLeakageBound K

    edgeInfluxBoundTarget :
      AdjacentShellEdgeInfluxBound K

    edgeInfluxBoundTargetIsCanonical :
      edgeInfluxBoundTarget ≡ canonicalAdjacentShellEdgeInfluxBound K

    hypotheses :
      List AdjacentShellLeakageHypothesis

    hypothesesAreCanonical :
      hypotheses ≡ canonicalAdjacentShellLeakageHypotheses

    signFacts :
      List AdjacentShellLeakageSignFact

    signFactsAreCanonical :
      signFacts ≡ canonicalAdjacentShellLeakageSignFacts

    boundaries :
      List AdjacentShellLeakageBoundary

    boundariesAreCanonical :
      boundaries ≡ canonicalAdjacentShellLeakageBoundaries

    computedDiagnostics :
      List AdjacentShellComputedDiagnostic

    computedDiagnosticsAreCanonical :
      computedDiagnostics ≡ canonicalAdjacentShellComputedDiagnostics

    formula :
      String

    formulaIsCanonical :
      formula ≡ adjacentShellLeakageFormula

    edgeInfluxFormula :
      String

    edgeInfluxFormulaIsCanonical :
      edgeInfluxFormula ≡ adjacentShellEdgeInfluxFormula

    signFormula :
      String

    signFormulaIsCanonical :
      signFormula ≡ adjacentShellLeakageSignFormula

    computedDiagnosticFormula :
      String

    computedDiagnosticFormulaIsCanonical :
      computedDiagnosticFormula ≡ adjacentShellComputedDiagnosticFormula

    adjacentOnlySupportLocked :
      Bool

    adjacentOnlySupportLockedIsTrue :
      adjacentOnlySupportLocked ≡ true

    leakageBoundConditionallyStated :
      Bool

    leakageBoundConditionallyStatedIsTrue :
      leakageBoundConditionallyStated ≡ true

    edgeInfluxBoundConditionallyStated :
      Bool

    edgeInfluxBoundConditionallyStatedIsTrue :
      edgeInfluxBoundConditionallyStated ≡ true

    leakageBoundUnconditionallyProved :
      Bool

    leakageBoundUnconditionallyProvedIsFalse :
      leakageBoundUnconditionallyProved ≡ false

    hiddenHighHighProductionExcludedByHypothesis :
      Bool

    hiddenHighHighProductionExcludedByHypothesisIsTrue :
      hiddenHighHighProductionExcludedByHypothesis ≡ true

    lowHighThetaRatioBelowOneInDiagnostics :
      Bool

    lowHighThetaRatioBelowOneInDiagnosticsIsTrue :
      lowHighThetaRatioBelowOneInDiagnostics ≡ true

    highHighThetaBarrierCrossedInDiagnostics :
      Bool

    highHighThetaBarrierCrossedInDiagnosticsIsTrue :
      highHighThetaBarrierCrossedInDiagnostics ≡ true

    thetaPreservationProvedHere :
      Bool

    thetaPreservationProvedHereIsFalse :
      thetaPreservationProvedHere ≡ false

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    promotions :
      List AdjacentShellLeakagePromotion

    promotionsAreEmpty :
      promotions ≡ []

    noPromotionPossibleHere :
      AdjacentShellLeakagePromotion →
      ⊥

open NSAdjacentShellLeakageBoundReceipt public

canonicalNSAdjacentShellLeakageBoundReceipt :
  NSAdjacentShellLeakageBoundReceipt zero
canonicalNSAdjacentShellLeakageBoundReceipt =
  record
    { fullIdentityReceipt =
        Full.canonicalNSTailFluxLPIdentityFullDerivationReceipt
    ; fullIdentityDerived =
        refl
    ; fullIdentityNoClay =
        refl
    ; dangerShellReceipt =
        Danger.canonicalNSDangerShellMaximumPrincipleReceipt
    ; dangerShellStillOpen =
        refl
    ; adjacentOnlyDiagnostic =
        Adjacent.canonicalAdjacentOnlyVortexStretchingReceipt
    ; adjacentOnlyNoClay =
        refl
    ; leakageBound =
        canonicalAdjacentShellLeakageBound zero
    ; leakageBoundIsCanonical =
        refl
    ; edgeInfluxBoundTarget =
        canonicalAdjacentShellEdgeInfluxBound zero
    ; edgeInfluxBoundTargetIsCanonical =
        refl
    ; hypotheses =
        canonicalAdjacentShellLeakageHypotheses
    ; hypothesesAreCanonical =
        refl
    ; signFacts =
        canonicalAdjacentShellLeakageSignFacts
    ; signFactsAreCanonical =
        refl
    ; boundaries =
        canonicalAdjacentShellLeakageBoundaries
    ; boundariesAreCanonical =
        refl
    ; computedDiagnostics =
        canonicalAdjacentShellComputedDiagnostics
    ; computedDiagnosticsAreCanonical =
        refl
    ; formula =
        adjacentShellLeakageFormula
    ; formulaIsCanonical =
        refl
    ; edgeInfluxFormula =
        adjacentShellEdgeInfluxFormula
    ; edgeInfluxFormulaIsCanonical =
        refl
    ; signFormula =
        adjacentShellLeakageSignFormula
    ; signFormulaIsCanonical =
        refl
    ; computedDiagnosticFormula =
        adjacentShellComputedDiagnosticFormula
    ; computedDiagnosticFormulaIsCanonical =
        refl
    ; adjacentOnlySupportLocked =
        true
    ; adjacentOnlySupportLockedIsTrue =
        refl
    ; leakageBoundConditionallyStated =
        true
    ; leakageBoundConditionallyStatedIsTrue =
        refl
    ; edgeInfluxBoundConditionallyStated =
        true
    ; edgeInfluxBoundConditionallyStatedIsTrue =
        refl
    ; leakageBoundUnconditionallyProved =
        false
    ; leakageBoundUnconditionallyProvedIsFalse =
        refl
    ; hiddenHighHighProductionExcludedByHypothesis =
        true
    ; hiddenHighHighProductionExcludedByHypothesisIsTrue =
        refl
    ; lowHighThetaRatioBelowOneInDiagnostics =
        true
    ; lowHighThetaRatioBelowOneInDiagnosticsIsTrue =
        refl
    ; highHighThetaBarrierCrossedInDiagnostics =
        true
    ; highHighThetaBarrierCrossedInDiagnosticsIsTrue =
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
        adjacentShellLeakagePromotionImpossibleHere
    }

canonicalAdjacentLeakageNoThetaPromotion :
  thetaPreservationProvedHere canonicalNSAdjacentShellLeakageBoundReceipt
  ≡ false
canonicalAdjacentLeakageNoThetaPromotion =
  refl

canonicalAdjacentLeakageNoClayPromotion :
  clayNavierStokesPromoted canonicalNSAdjacentShellLeakageBoundReceipt
  ≡ false
canonicalAdjacentLeakageNoClayPromotion =
  refl
