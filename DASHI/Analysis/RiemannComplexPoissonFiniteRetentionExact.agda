module DASHI.Analysis.RiemannComplexPoissonFiniteRetentionExact where

------------------------------------------------------------------------
-- PURPOSE
--
-- Exact subtraction-free assembly for the two analytic steps that remain
-- between complex Poisson and a finite Alpöge--Furman compression.
--
-- Analytic calibration:
-- Levent Alpöge and Ralph Furman,
-- "More than two thirds of the zeta zeros are simple and on the critical line",
-- arXiv:2608.13637 (2026), DOI: 10.48550/arXiv.2608.13637.
--
-- Intended analytic instantiation:
--
--   sum_k |phiHat(gamma-i alpha-tau_k)|^2 = L Phi(-2 i alpha)
--
-- and
--
--   fullGridExcess >= c_phi alpha^2.
--
-- The present module does not prove those analytic identities.  It proves the
-- exact nonnegative ledger needed once they and a finite-tail estimate are
-- supplied.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)

record ComplexPoissonNormContract : Set₁ where
  field
    AnalyticPair : Set
    squaredTransverseDisplacement : AnalyticPair → Nat
    coerciveWeight : Nat
    criticalBaseline : AnalyticPair → Nat
    fullGridHermitianNorm : AnalyticPair → Nat
    fullGridExcess : AnalyticPair → Nat
    coercivitySlack : AnalyticPair → Nat

    baselinePlusExcessIsFullNorm :
      (x : AnalyticPair) →
      criticalBaseline x + fullGridExcess x ≡ fullGridHermitianNorm x

    weightedDisplacementPlusSlackIsExcess :
      (x : AnalyticPair) →
      coerciveWeight * squaredTransverseDisplacement x + coercivitySlack x
        ≡ fullGridExcess x

record ComplexPoissonStripContinuation : Set₁ where
  field
    ComplexArgument : Set
    inRequiredStrip : ComplexArgument → Set
    conjugateArgument : ComplexArgument → ComplexArgument
    phiKernel : ComplexArgument → ComplexArgument → Nat
    gaborFullGrid : ComplexArgument → ComplexArgument → Nat
    continuedPoissonIdentity :
      (z w : ComplexArgument) →
      inRequiredStrip z → inRequiredStrip w →
      gaborFullGrid z w ≡ phiKernel z w

record FiniteGridTailLedger : Set where
  constructor finiteGridTailLedger
  field
    fullGridExcess : Nat
    finiteGridExcess : Nat
    tailLoss : Nat
    retentionMargin : Nat
    fullIsFinitePlusTail :
      fullGridExcess ≡ finiteGridExcess + tailLoss
    tailPlusMarginIsFinite :
      tailLoss + retentionMargin ≡ finiteGridExcess

open FiniteGridTailLedger public

record CoerciveFiniteRetention : Set where
  constructor coerciveFiniteRetention
  field
    weightedTransverseDefect : Nat
    coercivitySlack : Nat
    tailLedger : FiniteGridTailLedger
    coerciveFullGridIdentity :
      weightedTransverseDefect + coercivitySlack ≡ fullGridExcess tailLedger

open CoerciveFiniteRetention public

record FiniteRetentionCertificate (r : CoerciveFiniteRetention) : Set where
  constructor finiteRetentionCertificate
  field
    doubledFiniteGridExcess : Nat
    dominationIdentity :
      (weightedTransverseDefect r + coercivitySlack r)
        + retentionMargin (tailLedger r)
      ≡ doubledFiniteGridExcess
    doubledFiniteDefinition :
      doubledFiniteGridExcess
        ≡ finiteGridExcess (tailLedger r) + finiteGridExcess (tailLedger r)

record ComplexPoissonFiniteRetentionProducer : Set₁ where
  field
    AnalyticPair : Set
    fullGridIdentityAvailable : AnalyticPair → Set
    coshCoercivityAvailable : AnalyticPair → Set
    finiteTailEstimateAvailable : AnalyticPair → Set
    retainedCertificate : AnalyticPair → CoerciveFiniteRetention

record ComplexPoissonFiniteRetentionBoundary : Set where
  field
    complexPoissonAnalyticSocketConstructed : Bool
    finiteTailLedgerConstructed : Bool
    subtractionFreeRetentionCertificateConstructed : Bool
    analyticComplexPoissonContinuationProvedHere : Bool
    analyticCoshCoercivityProvedHere : Bool
    sourceFiniteWindowTailEstimateProvedHere : Bool
    zetaFiniteRetentionInstantiatedHere : Bool

complexPoissonFiniteRetentionBoundary : ComplexPoissonFiniteRetentionBoundary
complexPoissonFiniteRetentionBoundary = record
  { complexPoissonAnalyticSocketConstructed = true
  ; finiteTailLedgerConstructed = true
  ; subtractionFreeRetentionCertificateConstructed = true
  ; analyticComplexPoissonContinuationProvedHere = false
  ; analyticCoshCoercivityProvedHere = false
  ; sourceFiniteWindowTailEstimateProvedHere = false
  ; zetaFiniteRetentionInstantiatedHere = false
  }
