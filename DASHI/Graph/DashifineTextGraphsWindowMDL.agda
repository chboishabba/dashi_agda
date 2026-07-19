module DASHI.Graph.DashifineTextGraphsWindowMDL where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Data.Empty using (⊥)

open import DASHI.Graph.DashifineTextGraphsBridge

------------------------------------------------------------------------
-- Candidate non-local graph rules from the current bridge sweep.

data GraphVariant : Set where
  baseline
  ternaryL1Le1
  ternaryL1Le2
  stateRecurrence
  rzL1Le1
  hybridL1Recurrence : GraphVariant

------------------------------------------------------------------------
-- Window-local comparison carrier.
--
-- Transported values and graph-derived values remain separate fields.  A
-- window certificate may compare them, but cannot silently identify them.

record WindowObservation : Set where
  constructor window
  field
    windowIndex : Nat

    transportedRVariation : Nat
    transportedZVariation : Nat
    transportedPhaseVariation : Nat

    graphDensityVariation : Nat
    graphCentralityVariation : Nat
    graphRecurrenceVariation : Nat

open WindowObservation public

record WindowSemanticCost : Set where
  constructor semanticCost
  field
    resonanceMismatch : Nat
    selfNormMismatch : Nat
    phaseMismatch : Nat

open WindowSemanticCost public

semanticTotal : WindowSemanticCost → Nat
semanticTotal c =
  resonanceMismatch c
  + selfNormMismatch c
  + phaseMismatch c

------------------------------------------------------------------------
-- MDL decomposition.

record MDLCost : Set where
  constructor mdl
  field
    encoderLength : Nat
    edgeRuleLength : Nat
    observationResidualLength : Nat

open MDLCost public

mdlTotal : MDLCost → Nat
mdlTotal c =
  encoderLength c
  + edgeRuleLength c
  + observationResidualLength c

record BridgeGap : Set where
  constructor gap
  field
    reconstructionLoss : Nat
    orderLoss : Nat
    semanticLoss : WindowSemanticCost
    complexityLoss : MDLCost

open BridgeGap public

bridgeGapTotal : BridgeGap → Nat
bridgeGapTotal g =
  reconstructionLoss g
  + orderLoss g
  + semanticTotal (semanticLoss g)
  + mdlTotal (complexityLoss g)

------------------------------------------------------------------------
-- Window-aware rule-selection certificate.
--
-- The ordering is supplied by the concrete scoring implementation.  DASHI
-- requires the winner to come with a proof that it is no worse than every
-- candidate, rather than promoting whichever rule happened to increase global
-- density or centrality most.

record WindowAwareSelection : Set₁ where
  field
    score : GraphVariant → BridgeGap
    _noWorseThan_ : BridgeGap → BridgeGap → Set
    winner : GraphVariant
    winnerMinimal :
      (candidate : GraphVariant) →
      (score winner) noWorseThan (score candidate)

open WindowAwareSelection public

------------------------------------------------------------------------
-- Current empirical state.

currentGlobalLiftCandidate : GraphVariant
currentGlobalLiftCandidate = ternaryL1Le2

currentCandidateIsTernaryL1Le2 :
  currentGlobalLiftCandidate ≡ ternaryL1Le2
currentCandidateIsTernaryL1Le2 = refl

-- No window-aware/MDL selection certificate has been supplied by the current
-- global graph-lift sweep.  Therefore the candidate is not promoted here.
data WindowAwareWinnerPromotion : Set where

windowAwareWinnerPromotionImpossibleHere :
  WindowAwareWinnerPromotion → ⊥
windowAwareWinnerPromotionImpossibleHere ()

record WindowAwareBridgeClosure : Set₁ where
  constructor closeWindowAwareBridge
  field
    selection : WindowAwareSelection
    independentGraphEvidence : GraphDerivedEvidence
    promotedWinner : GraphVariant
    promotedWinnerMatchesCertificate :
      promotedWinner ≡ winner selection

------------------------------------------------------------------------
-- The actual remaining theorem target.

WindowAwareMDLClosureTarget : Set₁
WindowAwareMDLClosureTarget = WindowAwareBridgeClosure
