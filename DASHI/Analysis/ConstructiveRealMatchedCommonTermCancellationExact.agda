module DASHI.Analysis.ConstructiveRealMatchedCommonTermCancellationExact where

open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; trans; cong; cong₂)

import DASHI.Analysis.ConstructiveRealSpine as R
import DASHI.Analysis.MarxConstructiveRealRingNormalisation as Ring

------------------------------------------------------------------------
-- EXACT MATCHED COMMON-TERM CANCELLATION
--
-- If two regulated quantities share the same additive common term C,
--
--   A = a + C
--   B = b + C,
--
-- then subtraction before any nonlinear projection gives exactly
--
--   A - B = a - b.
--
-- This is the algebraic kernel needed for Casimir matched plate/reference
-- subtraction.  No convergence, integrability, or regulator-removal theorem is
-- inferred from the cancellation itself.
------------------------------------------------------------------------

commonRightTermCancels :
  {real : R.ConstructedOrderedCompleteReal} →
  (laws : Ring.ConstructedRealRingNormalisationLaws real) →
  (plateResidual referenceResidual common : R.Real real) →
  R._-_ real
    (R._+_ real plateResidual common)
    (R._+_ real referenceResidual common)
  ≡ R._-_ real plateResidual referenceResidual
commonRightTermCancels {real} laws plateResidual referenceResidual common =
  trans
    (Ring.differenceOfSums laws
      referenceResidual plateResidual common common)
    (trans
      (cong
        (R._+_ real (R._-_ real plateResidual referenceResidual))
        (R.subSelf real common))
      (R.addZeroRight real (R._-_ real plateResidual referenceResidual)))

record MatchedRegulatedDecomposition
    (real : R.ConstructedOrderedCompleteReal) : Set₁ where
  field
    Regulator : Set
    plate reference : Regulator → R.Real real
    plateResidual referenceResidual commonTerm : Regulator → R.Real real

    plateDecomposition : ∀ r →
      plate r ≡ R._+_ real (plateResidual r) (commonTerm r)
    referenceDecomposition : ∀ r →
      reference r ≡ R._+_ real (referenceResidual r) (commonTerm r)

open MatchedRegulatedDecomposition public

regulatedDifferenceCancelsCommon :
  {real : R.ConstructedOrderedCompleteReal} →
  (laws : Ring.ConstructedRealRingNormalisationLaws real) →
  (D : MatchedRegulatedDecomposition real) →
  ∀ r →
  R._-_ real (plate D r) (reference D r)
  ≡ R._-_ real (plateResidual D r) (referenceResidual D r)
regulatedDifferenceCancelsCommon {real} laws D r =
  trans
    (cong₂
      (R._-_ real)
      (plateDecomposition D r)
      (referenceDecomposition D r))
    (commonRightTermCancels laws
      (plateResidual D r)
      (referenceResidual D r)
      (commonTerm D r))

record MatchedDifferenceCancellationReceipt
    {real : R.ConstructedOrderedCompleteReal}
    (laws : Ring.ConstructedRealRingNormalisationLaws real)
    (D : MatchedRegulatedDecomposition real) : Set₁ where
  field
    cancellation : ∀ r →
      R._-_ real (plate D r) (reference D r)
      ≡ R._-_ real (plateResidual D r) (referenceResidual D r)

open MatchedDifferenceCancellationReceipt public

buildMatchedDifferenceCancellationReceipt :
  {real : R.ConstructedOrderedCompleteReal} →
  (laws : Ring.ConstructedRealRingNormalisationLaws real) →
  (D : MatchedRegulatedDecomposition real) →
  MatchedDifferenceCancellationReceipt laws D
buildMatchedDifferenceCancellationReceipt laws D = record
  { cancellation = regulatedDifferenceCancelsCommon laws D }

data CommonTermCancellationAutomaticallyProvesResidualConvergence : Set where

data SeparateRawLimitsRequiredAfterExactCancellation : Set where

cancellationDoesNotProveConvergence :
  CommonTermCancellationAutomaticallyProvesResidualConvergence → ⊥
cancellationDoesNotProveConvergence ()

rawLimitsNotRequiredByMatchedDifference :
  SeparateRawLimitsRequiredAfterExactCancellation → ⊥
rawLimitsNotRequiredByMatchedDifference ()
