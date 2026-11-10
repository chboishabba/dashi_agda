module DASHI.Information.PNFTimeIndexedRiskQualityLedgerExact where

-- Source-indexed held-out squared-risk-forecast error.
-- This is an exact finite *evaluation*, not an MP convergence theorem
-- or an empirical claim that clipping wins. All scores are Nat so that
-- finite arithmetic is executable in Agda without introducing a new
-- approximate real backend.

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_; _∸_)
open import Agda.Builtin.String using (String)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Nat.Base using (_≤_)

import DASHI.Finance.TemporalMarketFibreExact as Temporal
import DASHI.Information.PNFMPTradingInadequacyControlExact as Policy
import DASHI.Information.PNFSpectralGeometry as Spectral
import DASHI.Core.IntersectionalNonFactorability as NF
import Data.Empty

-- Absolute-error and squared-error functions compute from the actual
-- selected prediction and realised outcome; losses are not free fields.
absoluteNatError : Nat → Nat → Nat
absoluteNatError predicted realised =
  (predicted ∸ realised) + (realised ∸ predicted)

squaredNatError : Nat → Nat → Nat
squaredNatError predicted realised =
  absoluteNatError predicted realised
  * absoluteNatError predicted realised

natSum : {m : Nat} → (Fin m → Nat) → Nat
natSum {zero} f = 0
natSum {suc m} f = f zero + natSum (λ i → f (suc i))

record PointInTimeLossLedger (m : Nat) : Set where
  field
    historyReference : String
    sourceReference : String
    consumerVersionReference : String
    featureUniverseReference : String
    -- Predictions are retained as they stood at their original decision
    -- time; no revised or backfilled forecast is substituted.
    decisionTime : Fin m → Nat
    observationTime : Fin m → Nat
    observationAvailableAt : Fin m → Nat
    forwardEvaluation :
      (i : Fin m) →
      Temporal.ForwardPath (decisionTime i) (observationTime i)
    -- The forward evaluation path only constrains event chronology.
    -- A consumer must separately pay source availability/forecast freeze.
    realizedRisk : Fin m → Nat
    baselineRiskForecast : Fin m → Nat
    cleanedRiskForecast : Fin m → Nat
    forecastFrozenAtDecision : Fin m → String
    realizedObservationProvenance : Fin m → String

open PointInTimeLossLedger public

baselineSquaredRiskLoss :
  {m : Nat} → PointInTimeLossLedger m → Nat
baselineSquaredRiskLoss L =
  natSum (λ i →
    squaredNatError (baselineRiskForecast L i) (realizedRisk L i))

cleanedSquaredRiskLoss :
  {m : Nat} → PointInTimeLossLedger m → Nat
cleanedSquaredRiskLoss L =
  natSum (λ i →
    squaredNatError (cleanedRiskForecast L i) (realizedRisk L i))

-- This is evidence for a *selected evaluation policy*. It is not
-- constructible from nullBand/candidateSignal alone.
record QualifiedRiskEvidence {m : Nat}
  (L : PointInTimeLossLedger m) : Set where
  field
    minHeldoutFolds : Nat
    sufficientFolds : minHeldoutFolds ≤ m
    -- The source owner decides a nonvacuous threshold; requiring a
    -- concrete >=2 proof avoids a single-fold 'improvement' promotion.
    atLeastTwoFolds : suc (suc zero) ≤ minHeldoutFolds
    noBackdatedPrediction : (i : Fin m) →
      Temporal.ForwardPath (decisionTime L i) (observationTime L i)
    cleanedNotWorseOnSelectedLoss :
      cleanedSquaredRiskLoss L ≤ baselineSquaredRiskLoss L

open QualifiedRiskEvidence public

qualityReceiptEnablesSelectedRiskStatus :
  {m : Nat} →
  (L : PointInTimeLossLedger m) →
  QualifiedRiskEvidence L →
  Policy.SpectralAdequacy
qualityReceiptEnablesSelectedRiskStatus L qualified =
  Policy.qualifiedRiskEstimate

-- Different realised risk can follow the SAME MP band classification.
-- This reuses DASHI's nonfactorability owner to show why an MP label
-- cannot recover held-out forecast quality or risk outcome.
data TwoRiskOutcomes : Set where
  zeroRealized : TwoRiskOutcomes
  positiveRealized : TwoRiskOutcomes

mpLabel : TwoRiskOutcomes → Spectral.SpectralClass
mpLabel zeroRealized = Spectral.nullBand
mpLabel positiveRealized = Spectral.nullBand

realizedMagnitude : TwoRiskOutcomes → Nat
realizedMagnitude zeroRealized = 0
realizedMagnitude positiveRealized = 1

mpLabelInsufficientForRealizedRisk :
  NF.NonFactorabilityWitness mpLabel realizedMagnitude
mpLabelInsufficientForRealizedRisk =
  NF.nonFactorabilityWitness
    zeroRealized positiveRealized refl (λ ())

noMPLabelOnlyRealizedRisk :
  NF.FactorsThrough mpLabel realizedMagnitude →
  Data.Empty.⊥
noMPLabelOnlyRealizedRisk =
  NF.witnessRulesOutEveryFlatFactorisation
    mpLabelInsufficientForRealizedRisk
