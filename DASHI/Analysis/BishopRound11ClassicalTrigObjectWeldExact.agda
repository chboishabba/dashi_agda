module DASHI.Analysis.BishopRound11ClassicalTrigObjectWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import Real as Bishop

import DASHI.Analysis.SourceBackedTheoremTransportBidiExact as Transport
import DASHI.Analysis.BishopRound11FactorDerivativeInterchangeExact as Round11
import DASHI.Analysis.BishopRound11PowerSeriesDifferentiationSourceTransportExact as Diff
import DASHI.Analysis.TrigonometricPythagoreanSourceAuthorityExact as PythSource
import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary

------------------------------------------------------------------------
-- ONE SAME-OBJECT WELD, TWO CLASSICAL SOURCE THEOREMS
--
-- If the local Round11 Bishop sine/cosine pair is identified with the same
-- classical trigonometric object used by DLMF, that semantic identification
-- should be paid once and reused for both:
--
--   * termwise power-series differentiation;
--   * sin^2 + cos^2 = 1.
--
-- This prevents duplicate application receipts for the same function identity.
------------------------------------------------------------------------

pythagoreanSourceClaim : Transport.SourceBackedClaim
pythagoreanSourceClaim = record
  { Transport.SourceClaim =
      PythSource.pythagoreanIdentityStated
        PythSource.canonicalTrigonometricPythagoreanAuthority
  ; Transport.sourceReceipt = tt
  ; Transport.sourceName =
      PythSource.sourceName PythSource.canonicalTrigonometricPythagoreanAuthority
  ; Transport.sourceLocator =
      PythSource.sourceLocator PythSource.canonicalTrigonometricPythagoreanAuthority
  ; Transport.reading =
      "DLMF §4.21.12 Pythagorean identity for the classical sine/cosine object."
  }

Round11Pythagorean :
  Round11.Round11FactorInterchangeProblem → Set
Round11Pythagorean P =
  (point : Bishop.ℝ) →
  Bishop._≃_
    (Bishop._+_
      (Bishop._*_
        (Elementary.bishopSin (Round11.dataSet P) point)
        (Elementary.bishopSin (Round11.dataSet P) point))
      (Bishop._*_
        (Elementary.bishopCos (Round11.dataSet P) point)
        (Elementary.bishopCos (Round11.dataSet P) point)))
    Bishop.1ℝ

record Round11ClassicalTrigObjectWeld
    (P : Round11.Round11FactorInterchangeProblem) : Set₁ where
  field
    SameClassicalAndBishopTrigObject : Set
    sameClassicalAndBishopTrigObjectEvidence :
      SameClassicalAndBishopTrigObject

    samePowerSeriesCoefficientsCentreAndIndexing : Set
    samePowerSeriesCoefficientsCentreAndIndexingEvidence :
      samePowerSeriesCoefficientsCentreAndIndexing

    classicalInteriorDomainCoversRound11Evaluation : Set
    classicalInteriorDomainCoversRound11EvaluationEvidence :
      classicalInteriorDomainCoversRound11Evaluation

    classicalDerivativeSemanticsMatchesBishopFactorDerivative : Set
    classicalDerivativeSemanticsMatchesBishopFactorDerivativeEvidence :
      classicalDerivativeSemanticsMatchesBishopFactorDerivative

    differentiationSourceToRound11 :
      Transport.SourceClaim Diff.sourceClaim →
      SameClassicalAndBishopTrigObject →
      Round11.Round11FactorInterchangeAuthority P

    pythagoreanSourceToRound11 :
      Transport.SourceClaim pythagoreanSourceClaim →
      SameClassicalAndBishopTrigObject →
      Round11Pythagorean P

    reading : String

open Round11ClassicalTrigObjectWeld public

differentiationTarget :
  (P : Round11.Round11FactorInterchangeProblem) →
  Round11ClassicalTrigObjectWeld P →
  Transport.LocalTheoremTarget Diff.sourceClaim
differentiationTarget P W = record
  { Transport.LocalClaim = Round11.Round11FactorInterchangeAuthority P
  ; Transport.sameMathematicalObject = SameClassicalAndBishopTrigObject W
  ; Transport.sourceSemanticsToLocal = differentiationSourceToRound11 W
  ; Transport.reading = reading W
  }

pythagoreanTarget :
  (P : Round11.Round11FactorInterchangeProblem) →
  Round11ClassicalTrigObjectWeld P →
  Transport.LocalTheoremTarget pythagoreanSourceClaim
pythagoreanTarget P W = record
  { Transport.LocalClaim = Round11Pythagorean P
  ; Transport.sameMathematicalObject = SameClassicalAndBishopTrigObject W
  ; Transport.sourceSemanticsToLocal = pythagoreanSourceToRound11 W
  ; Transport.reading = reading W
  }

compileRound11DerivativeAuthority :
  (P : Round11.Round11FactorInterchangeProblem) →
  (W : Round11ClassicalTrigObjectWeld P) →
  Round11.Round11FactorInterchangeAuthority P
compileRound11DerivativeAuthority P W =
  Transport.transportSourceBackedTheorem
    Diff.sourceClaim
    (differentiationTarget P W)
    (record
      { Transport.objectWeld = sameClassicalAndBishopTrigObjectEvidence W
      })

compileRound11Pythagorean :
  (P : Round11.Round11FactorInterchangeProblem) →
  (W : Round11ClassicalTrigObjectWeld P) →
  Round11Pythagorean P
compileRound11Pythagorean P W =
  Transport.transportSourceBackedTheorem
    pythagoreanSourceClaim
    (pythagoreanTarget P W)
    (record
      { Transport.objectWeld = sameClassicalAndBishopTrigObjectEvidence W
      })

record ReverseSharedTrigWeldObligations : Set where
  field
    sameClassicalAndBishopSinCosFunctions : Set
    samePowerSeriesCoefficientChart : Set
    sameCentreAndIndexing : Set
    sourceInteriorDomainContainsLocalPoints : Set
    classicalDerivativeToFactorDerivativeSemantics : Set

open ReverseSharedTrigWeldObligations public

data SeparateSameFunctionWeldRequiredForEachTrigTheorem : Set where

sameFunctionWeldIsReusableAcrossSourceTheorems :
  SeparateSameFunctionWeldRequiredForEachTrigTheorem → ⊥
sameFunctionWeldIsReusableAcrossSourceTheorems ()

record Status : Set where
  field
    derivativeSourceBacked : Bool
    pythagoreanSourceBacked : Bool
    sharedSameTrigObjectWeldSurfaceOwned : Bool
    oneWeldFeedsBothCompilers : Bool
    sameTrigObjectWeldClosed : Bool

    derivativeSourceBackedIsTrue : derivativeSourceBacked ≡ true
    pythagoreanSourceBackedIsTrue : pythagoreanSourceBacked ≡ true
    sharedSameTrigObjectWeldSurfaceOwnedIsTrue :
      sharedSameTrigObjectWeldSurfaceOwned ≡ true
    oneWeldFeedsBothCompilersIsTrue : oneWeldFeedsBothCompilers ≡ true
    sameTrigObjectWeldClosedIsFalse : sameTrigObjectWeldClosed ≡ false

open Status public

canonicalStatus : Status
canonicalStatus = record
  { derivativeSourceBacked = true
  ; pythagoreanSourceBacked = true
  ; sharedSameTrigObjectWeldSurfaceOwned = true
  ; oneWeldFeedsBothCompilers = true
  ; sameTrigObjectWeldClosed = false
  ; derivativeSourceBackedIsTrue = refl
  ; pythagoreanSourceBackedIsTrue = refl
  ; sharedSameTrigObjectWeldSurfaceOwnedIsTrue = refl
  ; oneWeldFeedsBothCompilersIsTrue = refl
  ; sameTrigObjectWeldClosedIsFalse = refl
  }
