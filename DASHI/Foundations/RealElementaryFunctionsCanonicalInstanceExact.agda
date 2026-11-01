module DASHI.Foundations.RealElementaryFunctionsCanonicalInstanceExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ ; 0ℝ ; 1ℝ ; _+ℝ_ ; _-ℝ_ ; _*ℝ_ ; -ℝ_ ; absℝ ; _≤ℝ_ ; _<ℝ_ )
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Foundations.RealElementaryFunctionsAlternatingSeriesExact as Alt
import DASHI.Foundations.BishopConstructiveRealBridgeExact as Bishop
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as BishopSeries
import DASHI.Foundations.RealElementaryFunctionsBishopTransportExact as BishopTransport

------------------------------------------------------------------------
-- Canonical elementary functions on DASHI's legacy real carrier.
--
-- Marc Daumas, David Lester and César Muñoz,
-- "Verified Real Number Calculations: A Library for Interval Arithmetic",
-- IEEE Transactions on Computers 58 (2009), 226--237.
-- DOI: 10.1109/TC.2008.213; arXiv:0708.3721.
-- Relationship: organization of proof-producing elementary-function bounds.
--
-- Zachary Murray, "Constructive Analysis in the Agda Proof Assistant",
-- BSc Honours thesis, Dalhousie University, April 2022.
-- arXiv:2205.08354. No DOI assigned.
-- Relationship: concrete Bishop reals, arithmetic, sequence/series convergence
-- and Cauchy completeness imported through vendor/bishop.
--
-- Walter Rudin, "Principles of Mathematical Analysis", third edition,
-- McGraw--Hill (1976). No DOI assigned to the book edition used here.
-- Relationship: classical comparison for alternating power series and the
-- exponential/logarithm inverse law; it is not the constructive implementation.
--
-- RealAnalysisAxioms intentionally postulates the legacy carrier.  The functions
-- below remain compatibility names for existing modules.  New analytic work must
-- be backed by BishopBackedDASHIElementaryFunctions, which explicitly transports
-- the concrete Bishop series limits rather than creating a second completeness
-- postulate.
------------------------------------------------------------------------

postulate
  sinℝ cosℝ expℝ logℝ : ℝ → ℝ
  _÷ℝ_ : ℝ → ℝ → ℝ
  powℝ : ℝ → Nat → ℝ
  factorialℝ : Nat → ℝ

  canonicalSinCosAlternatingData :
    Alt.ConfiguredSinCosAlternatingData ℝ

  canonicalNegativeLogOneMinusAuthority :
    Alt.NegativeLogOneMinusAuthority ℝ

  canonicalPositiveExponentialSeriesAuthority :
    Alt.PositiveExponentialSeriesAuthority ℝ

  canonicalLogExpOrderAuthority :
    Alt.LogExpOrderAuthority ℝ

  sineFunctionAgreement :
    Alt.function (Alt.sineSeries canonicalSinCosAlternatingData) ≡ sinℝ

  cosineFunctionAgreement :
    Alt.function (Alt.cosineSeries canonicalSinCosAlternatingData) ≡ cosℝ

  negativeLogFunctionAgreement : Set
  exponentialSeriesFunctionAgreement : Set
  logarithmExponentialFunctionAgreement : Set

  -- One explicit bridge instance replaces any implicit identification of the
  -- postulated legacy carrier with Bishop's setoid carrier.
  bishopBackedLegacyElementaryFunctions :
    BishopTransport.BishopBackedDASHIElementaryFunctions

repositoryElementaryFunctionPrimitivePackage :
  Alt.ConfiguredElementaryFunctionPrimitivePackage ℝ
repositoryElementaryFunctionPrimitivePackage =
  BishopTransport.dashiPrimitivePackage
    bishopBackedLegacyElementaryFunctions

repositorySineTermMagnitudeDecreasing =
  Alt.termMagnitudeDecreasing
    (Alt.sineSeries
      (Alt.sinCos repositoryElementaryFunctionPrimitivePackage))

repositoryCosineTermMagnitudeDecreasing =
  Alt.termMagnitudeDecreasing
    (Alt.cosineSeries
      (Alt.sinCos repositoryElementaryFunctionPrimitivePackage))

repositorySineFirstOmittedTermBound =
  Alt.firstOmittedTermControlsRemainder
    (Alt.sineSeries
      (Alt.sinCos repositoryElementaryFunctionPrimitivePackage))

repositoryCosineFirstOmittedTermBound =
  Alt.firstOmittedTermControlsRemainder
    (Alt.cosineSeries
      (Alt.sinCos repositoryElementaryFunctionPrimitivePackage))

repositoryNegativeLogOneMinusBound =
  Alt.negativeLogOneMinusBound
    (Alt.negativeLog repositoryElementaryFunctionPrimitivePackage)

repositoryExponentialPartialSumBelow =
  Alt.exponentialPartialSumBelow
    (Alt.exponentialSeries repositoryElementaryFunctionPrimitivePackage)

repositoryLogarithmMonotone =
  Alt.logarithmMonotone
    (Alt.logExp repositoryElementaryFunctionPrimitivePackage)

repositoryLogarithmExponential =
  Alt.logarithmExponential
    (Alt.logExp repositoryElementaryFunctionPrimitivePackage)

canonicalRealElementaryAdapterLevel : ProofLevel
canonicalRealElementaryAdapterLevel = machineChecked

bishopConcreteCompletenessImportedLevel : ProofLevel
bishopConcreteCompletenessImportedLevel =
  Bishop.bishopCauchyCompletenessLevel

bishopPowerSeriesLimitConstructionLevel : ProofLevel
bishopPowerSeriesLimitConstructionLevel =
  BishopSeries.bishopPowerSeriesCompletenessLevel

canonicalRealElementaryFunctionAgreementLevel : ProofLevel
canonicalRealElementaryFunctionAgreementLevel = conditional

repositoryElementaryCalculusAuthorityLevel : ProofLevel
repositoryElementaryCalculusAuthorityLevel = conditional
