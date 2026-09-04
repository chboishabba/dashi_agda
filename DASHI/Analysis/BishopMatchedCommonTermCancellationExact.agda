module DASHI.Analysis.BishopMatchedCommonTermCancellationExact where

open import Data.Empty using (⊥)

import Real as BishopReal
import RealProperties as BishopProperties

------------------------------------------------------------------------
-- MATCHED COMMON-TERM CANCELLATION ON THE PINNED BISHOP REAL BACKEND
--
-- This is the setoid-native version needed by the actual Casimir analysis:
--
--   (a + C) - (b + C)  ≃  a - b.
--
-- It is solved by the imported Bishop real ring solver, so no quotient into
-- propositional equality is required.
------------------------------------------------------------------------

bishopCommonRightTermCancels :
  (a b common : BishopReal.ℝ) →
  BishopReal._≃_
    (BishopReal._-_
      (BishopReal._+_ a common)
      (BishopReal._+_ b common))
    (BishopReal._-_ a b)
bishopCommonRightTermCancels a b common =
  solve 3
    (λ a b c → ((a ⊕ c) ⊖ (b ⊕ c)) ⊜ (a ⊖ b))
    BishopProperties.≃-refl
    a b common
  where
    open BishopProperties.ℝ-Solver

record BishopMatchedRegulatedDecomposition : Set₁ where
  field
    Regulator : Set
    plate reference : Regulator → BishopReal.ℝ
    plateResidual referenceResidual commonTerm : Regulator → BishopReal.ℝ

    plateDecomposition : ∀ r →
      BishopReal._≃_
        (plate r)
        (BishopReal._+_ (plateResidual r) (commonTerm r))

    referenceDecomposition : ∀ r →
      BishopReal._≃_
        (reference r)
        (BishopReal._+_ (referenceResidual r) (commonTerm r))

open BishopMatchedRegulatedDecomposition public

bishopRegulatedDifferenceCancelsCommon :
  (D : BishopMatchedRegulatedDecomposition) →
  ∀ r →
  BishopReal._≃_
    (BishopReal._-_ (plate D r) (reference D r))
    (BishopReal._-_ (plateResidual D r) (referenceResidual D r))
bishopRegulatedDifferenceCancelsCommon D r =
  BishopProperties.≃-trans
    (BishopProperties.+-cong
      (plateDecomposition D r)
      (BishopProperties.-‿cong (referenceDecomposition D r)))
    (bishopCommonRightTermCancels
      (plateResidual D r)
      (referenceResidual D r)
      (commonTerm D r))

data MatchedCancellationAutomaticallyProvesResidualLimit : Set where

data RawPlateAndReferenceLimitsBecomeRequired : Set where

cancellationDoesNotProveLimit :
  MatchedCancellationAutomaticallyProvesResidualLimit → ⊥
cancellationDoesNotProveLimit ()

matchedDifferenceDoesNotRequireRawLimits :
  RawPlateAndReferenceLimitsBecomeRequired → ⊥
matchedDifferenceDoesNotRequireRawLimits ()
