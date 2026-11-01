module DASHI.Interop.SeaMeInIt.Unwrap.Competitor.Benchmark where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.String using (String)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (_≤_)

open import DASHI.Interop.SeaMeInIt.Unwrap.Competitor.Core
open import DASHI.Interop.SeaMeInIt.Unwrap.Competitor.Methods

------------------------------------------------------------------------
-- Run receipts and benchmark scoring
------------------------------------------------------------------------

record CompetitorRunReceipt : Set₁ where
  field
    method : CompetitorMethod
    inputHash : String
    outputHash : Maybe String
    metrics : DistortionVector
    severityReport : MethodSeverityReport
    available : Bool
    unavailableReason : Maybe String
    certificateHash : Maybe String

open CompetitorRunReceipt public

record OptionalCompetitorBoundary : Set₁ where
  field
    methodKind : MethodKind
    optionalAvailable : Bool
    reason : Maybe String
    nonFailureOfSuite :
      optionalAvailable ≡ false →
      Set

open OptionalCompetitorBoundary public

record BenchmarkWeights : Set where
  field
    wEdge : Nat
    wArea : Nat
    wAngle : Nat
    wFold : Nat
    wResidual : Nat
    wSeam : Nat
    wRoundTrip : Nat
    wMdl : Nat
    wAgreementDistance : Nat

open BenchmarkWeights public

metricOrPenalty : MetricValue → Nat
metricOrPenalty metric with availability metric
... | measured = value metric
... | unavailable = 999999
... | notApplicable = 0

score : BenchmarkWeights → DistortionVector → Nat
score weights metric =
  wEdge weights * metricOrPenalty (edgeLengthResidual metric)
  + wArea weights * metricOrPenalty (areaResidual metric)
  + wAngle weights * metricOrPenalty (angleResidual metric)
  + wFold weights * metricOrPenalty (foldoverCount metric)
  + wResidual weights * metricOrPenalty (aggregateResidual metric)
  + wSeam weights * metricOrPenalty (seamLength metric)
  + wRoundTrip weights * metricOrPenalty (roundTripMetric metric)
  + wAgreementDistance weights *
      metricOrPenalty (agreementDepthDistance metric)

record BenchmarkSliceReceipt : Set₁ where
  field
    weights : BenchmarkWeights
    candidates : List CompetitorRunReceipt
    candidateInSlice : CompetitorRunReceipt → Set
    winner : CompetitorRunReceipt
    winnerInSlice : candidateInSlice winner
    lowerScore :
      (candidate : CompetitorRunReceipt) →
      candidateInSlice candidate →
      score weights (metrics winner)
        ≤
      score weights (metrics candidate)
    severityBelowPromotionLimit : Set
    noFoldoverPromotion :
      metricOrPenalty (foldoverCount (metrics winner)) ≡ 0
    noGlobalClaim :
      claimsGlobalOptimality
        (claimBoundary (method winner))
      ≡ false
    noIsometryClaim :
      claimsIsometry
        (claimBoundary (method winner))
      ≡ false
    noFakeInverseClaim :
      claimsTrueInverse
        (claimBoundary (method winner))
      ≡ false
    plainReading : String

open BenchmarkSliceReceipt public

record DeclaredBenchmarkWinner : Set₁ where
  field
    slice : BenchmarkSliceReceipt
    winnerKind : MethodKind
    winnerMatches :
      kind (method (winner slice))
      ≡
      winnerKind
    lowerThanDeclaredCandidates : Set
    severityBelowPromotionLimitWitness : Set
    noGlobalOptimalityClaimWitness : Set
    noIsometryClaimWitness : Set
    noFakeInverseClaimWitness : Set

open DeclaredBenchmarkWinner public
