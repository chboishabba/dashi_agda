module DASHI.Analysis.NonArchimedeanCyclotomicSigmaHalfCompilerExact where

------------------------------------------------------------------------
-- CYCLOTOMIC SIGMA-HALF COMPILER
--
-- A mathematically clean local interpretation of the paper's p=2 half value is
--
--   sigma_cyc := log_2 |W_C|.
--
-- The source already owns the finite orbit-magnitude calculation (conditionally
-- on the canonical orbit receipts, now compiled in DASHI), and separately owns
-- `log2_sqrt_two : log2 (sqrt 2) = 1/2` in UndirectedGapExponent.lean.
--
-- This compiler deliberately does NOT identify sigma_cyc with the independent
-- Prolate/critical-line parameter sigma appearing in s = sigma + i t.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

record CyclotomicSigmaData : Set₁ where
  field
    Scalar : Set
    amplitudeMagnitude sqrtTwo half : Scalar
    log2 : Scalar → Scalar

    amplitudeMagnitudeIsSqrtTwo :
      amplitudeMagnitude ≡ sqrtTwo

    log2SqrtTwoIsHalf :
      log2 sqrtTwo ≡ half

open CyclotomicSigmaData public

cyclotomicSigma : (data : CyclotomicSigmaData) → Scalar data
cyclotomicSigma data = log2 data (amplitudeMagnitude data)

cyclotomicSigmaIsHalf :
  (data : CyclotomicSigmaData) →
  cyclotomicSigma data ≡ half data
cyclotomicSigmaIsHalf data =
  trans
    (cong (log2 data) (amplitudeMagnitudeIsSqrtTwo data))
    (log2SqrtTwoIsHalf data)

record CyclotomicSigmaSourceBoundary : Set where
  constructor cyclotomicSigmaSourceBoundary
  field
    orbitMagnitudeSquaredTwoOwned : Bool
    positiveMagnitudeLetsRecoverSqrtTwo : Bool
    log2SqrtTwoHalfOwned : Bool
    sourceExplicitlyDefinesSigmaCycAsLog2Magnitude : Bool
    dashIDefinitionMakesHalfCompilerAvailable : Bool
    compilerIdentifiesCriticalLineSigma : Bool

canonicalCyclotomicSigmaSourceBoundary : CyclotomicSigmaSourceBoundary
canonicalCyclotomicSigmaSourceBoundary =
  cyclotomicSigmaSourceBoundary true true true false true false

sourceDidNotYetDefineThisSigma :
  CyclotomicSigmaSourceBoundary.sourceExplicitlyDefinesSigmaCycAsLog2Magnitude
    canonicalCyclotomicSigmaSourceBoundary
  ≡ false
sourceDidNotYetDefineThisSigma = refl

halfCompilerDoesNotWeldCriticalLine :
  CyclotomicSigmaSourceBoundary.compilerIdentifiesCriticalLineSigma
    canonicalCyclotomicSigmaSourceBoundary
  ≡ false
halfCompilerDoesNotWeldCriticalLine = refl
