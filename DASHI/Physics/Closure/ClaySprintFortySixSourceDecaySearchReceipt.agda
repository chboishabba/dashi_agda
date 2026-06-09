module DASHI.Physics.Closure.ClaySprintFortySixSourceDecaySearchReceipt where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.Closure.ClaySprintFortyFiveBudgetComponentAuditReceipt
  as Sprint45

------------------------------------------------------------------------
-- Sprint 46 source-decay search.
--
-- This receipt records the post-Sprint-45 fork: either an independent DASHI
-- source-decay observable is found, or the current source-budget route is
-- falsified under the present 3D diagnostics.  It records diagnostics only.

Scalar : Set
Scalar = String

clayNavierStokesPromoted : Bool
clayNavierStokesPromoted = false

data SourceDecayCandidate : Set where
  redLineagePersistence :
    SourceDecayCandidate
  angularDecorrelationExponent :
    SourceDecayCandidate
  pressureSurvivalExponent :
    SourceDecayCandidate
  btLaneDecayObservable :
    SourceDecayCandidate

canonicalSourceDecayCandidates :
  List SourceDecayCandidate
canonicalSourceDecayCandidates =
  redLineagePersistence
  ∷ angularDecorrelationExponent
  ∷ pressureSurvivalExponent
  ∷ btLaneDecayObservable
  ∷ []

data Sprint46EstablishedInput : Set where
  strictRedFalsified :
    Sprint46EstablishedInput
  pressureRelaxedRedFalsified :
    Sprint46EstablishedInput
  stretchSignBridgePlausible :
    Sprint46EstablishedInput
  measuredGammaZero :
    Sprint46EstablishedInput
  measuredEtaZero :
    Sprint46EstablishedInput
  budgetBelowHalf :
    Sprint46EstablishedInput

canonicalSprint46EstablishedInputs :
  List Sprint46EstablishedInput
canonicalSprint46EstablishedInputs =
  strictRedFalsified
  ∷ pressureRelaxedRedFalsified
  ∷ stretchSignBridgePlausible
  ∷ measuredGammaZero
  ∷ measuredEtaZero
  ∷ budgetBelowHalf
  ∷ []

data SourceDecayGovernanceGuard : Set where
  noDoubleCountingGammaEta :
    SourceDecayGovernanceGuard
  noBudgetCreditWithoutIndependentObservable :
    SourceDecayGovernanceGuard
  btEtaUnavailableWithoutLaneLabels :
    SourceDecayGovernanceGuard
  rhoIsAdjacentShellProxyNotLineage :
    SourceDecayGovernanceGuard
  noClayPromotionFromDiagnostics :
    SourceDecayGovernanceGuard

canonicalSourceDecayGovernanceGuards :
  List SourceDecayGovernanceGuard
canonicalSourceDecayGovernanceGuards =
  noDoubleCountingGammaEta
  ∷ noBudgetCreditWithoutIndependentObservable
  ∷ btEtaUnavailableWithoutLaneLabels
  ∷ rhoIsAdjacentShellProxyNotLineage
  ∷ noClayPromotionFromDiagnostics
  ∷ []

data SourceDecayRouteDecision : Set where
  sourceBudgetRouteStillOpen :
    SourceDecayRouteDecision
  sourceBudgetRouteFalsifiedUnderCurrentDiagnostics :
    SourceDecayRouteDecision
  candidateDecayObservedNeedsIndependenceProof :
    SourceDecayRouteDecision

data Sprint46Promotion : Set where

sprint46PromotionImpossibleHere :
  Sprint46Promotion →
  ⊥
sprint46PromotionImpossibleHere ()

candidateCount : Nat
candidateCount = 4

establishedInputCount : Nat
establishedInputCount = 6

guardCount : Nat
guardCount = 5

rhoFormula : String
rhoFormula =
  "rho_K = Rplus_(K+1)/(Rplus_K + epsilon); pass requires rho_K < 1/sqrt(2)"

angularSigmaFormula : String
angularSigmaFormula =
  "angular_coherence_K ~ 2^(-sigma*K); need sigma > 1/2 before concentration penalties"

pressureSigmaFormula : String
pressureSigmaFormula =
  "pressure_survival_K = 1 - PressureDecorrelationScore_K; fit pressure_survival_K ~ 2^(-sigma_p*K)"

btLaneBoundary : String
btLaneBoundary =
  "eta_unavailable_no_BT_lane_observable"

sprint46OutputContract : String
sprint46OutputContract =
  "ns_source_decay_search.csv and ns_source_decay_summary.json emit rho_K, angular_sigma_fit, pressure_sigma_fit, candidate_budget, double_count_warning, and route_status"

record ClaySprintFortySixSourceDecaySearchReceipt : Set₁ where
  field
    observedStrictRedFalsified :
      Set

    observedStretchSignBridgePlausible :
      Set

    observedMeasuredGammaZero :
      Set

    observedMeasuredEtaZero :
      Set

    observedBudgetBelowHalf :
      Set

    observedAngularDecorrelationExponent :
      Set

    observedPressureSurvivalExponent :
      Set

    observedRedLineagePersistence :
      Set

    observedBtLaneDecayObservable :
      Set

    observedNoDoubleCountingGammaEta :
      Set

    observedNoBudgetCreditWithoutIndependentObservable :
      Set

    observedSourceBudgetRouteStillOpen :
      Set

    observedSourceBudgetRouteFalsifiedUnderCurrentDiagnostics :
      Set

    sprint45Receipt :
      Sprint45.ClaySprintFortyFiveBudgetComponentAuditReceipt

    sprint45NoPromotion :
      Sprint45.clayNavierStokesPromoted ≡ false

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

candidateCountCheck : candidateCount ≡ 4
candidateCountCheck = refl

establishedInputCountCheck : establishedInputCount ≡ 6
establishedInputCountCheck = refl

guardCountCheck : guardCount ≡ 5
guardCountCheck = refl
