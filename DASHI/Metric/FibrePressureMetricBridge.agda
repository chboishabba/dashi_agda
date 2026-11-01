module DASHI.Metric.FibrePressureMetricBridge where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Nat using (_≤_; _⊔_)
open import Data.Vec using (Vec)

open import DASHI.Algebra.Trit using (Trit)
open import DASHI.Arithmetic.ArithmeticIntegerEmbedding using (Int)
open import DASHI.Arithmetic.GlobalPressure as Global using
  ( totalPressure
  ; wallPressure
  ; totalPressure≡wallPressure
  )
open import DASHI.Arithmetic.WeightedPressure as Weighted using
  ( weightedDeltaAt
  ; weightedSupportAt
  ; weightedPressure
  ; weightedSupport
  ; weightedLocalBound
  ; weightedPressure≤weightedSupport
  ; weight
  )
open import DASHI.Energy.TranslationInvariantMetric as TIMetric using (TI)
open import DASHI.Interop.ObservationTransportSpine as Spine using
  ( ObservationDomain
  ; PromotionBoundary
  ; candidateSurfaceOnly
  ; fibrePressureMetricDomain
  )
open import DASHI.Metric.AgreementUltrametric as Agreement using
  ( dNat
  ; ultraNat
  )
open import MonsterOntos using (SSP)

------------------------------------------------------------------------
-- Fibre pressure / metric bridge.
--
-- This is a theorem-thin bridge from prime-indexed pressure accounting into
-- observation-transport admissibility and promotion gating.  It deliberately
-- does not prove completeness of every metric domain, construct a global
-- optimizer, or calibrate pressure thresholds.

record FibrePressureMetricSurface : Set₁ where
  field
    Fibre :
      Set

    State :
      Set

    fibreWeight :
      Fibre →
      Nat

    fibrePressure :
      Fibre →
      State →
      State →
      Nat

    fibreResidual :
      Fibre →
      State →
      State →
      Nat

    residualMetric :
      State →
      State →
      Nat

    residualBudget :
      State →
      State →
      Nat

    pressureMetric :
      State →
      State →
      Nat

    wallPressureMetric :
      State →
      State →
      Nat

    localResidualBound :
      ∀ f x y →
      fibrePressure f x y ≤ fibreResidual f x y

    globalResidualBound :
      ∀ x y →
      residualMetric x y ≤ residualBudget x y

    wallPressureCompatibility :
      ∀ x y →
      pressureMetric x y ≡ wallPressureMetric x y

    bridgeReading :
      String

open FibrePressureMetricSurface public

record FibrePressureMetricSpineWitness : Set where
  field
    domain :
      ObservationDomain

    domainIsFibrePressureMetricDomain :
      domain ≡ fibrePressureMetricDomain

    promotionBoundary :
      PromotionBoundary

    promotionBoundaryIsCandidateOnly :
      promotionBoundary ≡ candidateSurfaceOnly

    witnessReading :
      String

open FibrePressureMetricSpineWitness public

canonicalFibrePressureMetricSpineWitness :
  FibrePressureMetricSpineWitness
canonicalFibrePressureMetricSpineWitness =
  record
    { domain =
        fibrePressureMetricDomain
    ; domainIsFibrePressureMetricDomain =
        refl
    ; promotionBoundary =
        candidateSurfaceOnly
    ; promotionBoundaryIsCandidateOnly =
        refl
    ; witnessReading =
        "Fibre pressure metrics are explicitly connected to the candidate-only fibre-pressure domain in the observation-transport spine."
    }

canonicalArithmeticFibrePressureMetricSurface :
  FibrePressureMetricSurface
canonicalArithmeticFibrePressureMetricSurface =
  record
    { Fibre =
        SSP
    ; State =
        Int
    ; fibreWeight =
        weight
    ; fibrePressure =
        weightedDeltaAt
    ; fibreResidual =
        weightedSupportAt
    ; residualMetric =
        weightedPressure
    ; residualBudget =
        weightedSupport
    ; pressureMetric =
        totalPressure
    ; wallPressureMetric =
        wallPressure
    ; localResidualBound =
        weightedLocalBound
    ; globalResidualBound =
        weightedPressure≤weightedSupport
    ; wallPressureCompatibility =
        totalPressure≡wallPressure
    ; bridgeReading =
        "Arithmetic fibre pressure is weighted prime-local pressure bounded by weighted support; total pressure remains wall-compatible."
    }

------------------------------------------------------------------------
-- Agreement-ultrametric hook.

record AgreementResidualMetricSurface : Set₁ where
  field
    profileLength :
      Nat

    profileDistance :
      Vec Trit profileLength →
      Vec Trit profileLength →
      Nat

    profileDistanceIsCanonical :
      profileDistance ≡ dNat

    profileUltrametricBound :
      ∀ x y z →
      profileDistance x z ≤
      (profileDistance x y ⊔ profileDistance y z)

    metricReading :
      String

open AgreementResidualMetricSurface public

canonicalAgreementResidualMetricSurface :
  ∀ n →
  AgreementResidualMetricSurface
canonicalAgreementResidualMetricSurface n =
  record
    { profileLength =
        n
    ; profileDistance =
        dNat
    ; profileDistanceIsCanonical =
        refl
    ; profileUltrametricBound =
        ultraNat
    ; metricReading =
        "Agreement residuals use the existing prefix ultrametric; no completeness or calibration theorem is asserted here."
    }

------------------------------------------------------------------------
-- Transport admissibility and promotion gate.

record TransportResidualGate
    (surface : FibrePressureMetricSurface) : Set₁ where
  field
    maxResidual :
      Nat

    admissible :
      State surface →
      State surface →
      Set

    admissibleMeansResidualBounded :
      ∀ x y →
      admissible x y →
      residualMetric surface x y ≤ maxResidual

    admissibleMeansBudgetBounded :
      ∀ x y →
      admissible x y →
      residualMetric surface x y ≤ residualBudget surface x y

    gateReading :
      String

open TransportResidualGate public

budgetGate :
  (surface : FibrePressureMetricSurface) →
  Nat →
  TransportResidualGate surface
budgetGate surface max =
  record
    { maxResidual =
        max
    ; admissible =
        λ x y → residualMetric surface x y ≤ max
    ; admissibleMeansResidualBounded =
        λ x y residual≤max → residual≤max
    ; admissibleMeansBudgetBounded =
        λ x y _ → globalResidualBound surface x y
    ; gateReading =
        "Transport is admissible only when the residual metric is below the selected local budget; the global support bound remains available independently."
    }

record FibrePressurePromotionGate
    (surface : FibrePressureMetricSurface)
    (gate : TransportResidualGate surface) : Set₁ where
  field
    promotionBoundary :
      PromotionBoundary

    admissiblePair :
      State surface →
      State surface →
      Set

    promotionRequiresAdmissibility :
      ∀ x y →
      admissiblePair x y →
      TransportResidualGate.admissible gate x y

    calibrationReceipt :
      Set

    metricCompletenessReceipt :
      Set

    optimizerReceipt :
      Set

    promoted :
      Bool

    promotedIsFalseWithoutReceipts :
      promoted ≡ false

    gateReading :
      String

open FibrePressurePromotionGate public

data MissingCalibrationReceipt : Set where

data MissingMetricCompletenessReceipt : Set where

data MissingOptimizerReceipt : Set where

candidateOnlyPromotionGate :
  (surface : FibrePressureMetricSurface) →
  (gate : TransportResidualGate surface) →
  FibrePressurePromotionGate surface gate
candidateOnlyPromotionGate surface gate =
  record
    { promotionBoundary =
        candidateSurfaceOnly
    ; admissiblePair =
        TransportResidualGate.admissible gate
    ; promotionRequiresAdmissibility =
        λ x y admissible → admissible
    ; calibrationReceipt =
        MissingCalibrationReceipt
    ; metricCompletenessReceipt =
        MissingMetricCompletenessReceipt
    ; optimizerReceipt =
        MissingOptimizerReceipt
    ; promoted =
        false
    ; promotedIsFalseWithoutReceipts =
        refl
    ; gateReading =
        "Pressure/residual bounds support candidate transport only; promotion waits for explicit calibration, completeness, and optimizer receipts."
    }

------------------------------------------------------------------------
-- Translation-invariant metric socket.

record TranslationInvariantMetricSocket : Set₁ where
  field
    Carrier :
      Set

    metric :
      TI Carrier Nat

    socketReading :
      String

open TranslationInvariantMetricSocket public
