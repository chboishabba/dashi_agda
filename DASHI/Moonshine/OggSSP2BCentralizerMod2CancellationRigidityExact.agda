module DASHI.Moonshine.OggSSP2BCentralizerMod2CancellationRigidityExact where

------------------------------------------------------------------------
-- CENTRALIZER MOD-2 CANCELLATION RIGIDITY FRONTIER
--
-- The actual source-native Tate exact sequence has dimensions
--
--   0 -> 98304 -> 98580 -> 276 -> 0.
--
-- Rationally the centralizer pieces are
--
--   98304_-
--   98280_+ + (1 + 299)_+.
--
-- The accompanying CTblLib decomposition-matrix screen tests the stronger
-- characteristic-two statement
--
--   [98304]_2 = [98280]_2 + [24],
--
-- and therefore
--
--   [Tate276] = [1+299]_2 - [24] = [1] + [274] + [1].
--
-- It also tests that the common 98280 Brauer support is disjoint from both the
-- residual 24 and residual 276 supports.  Together with the independent
-- Frobenius-Hom uniqueness screen this means the remaining vertical weld is no
-- longer a semisimplified ambiguity: it is the literal placement of the actual
-- norm map on the common 98280 extension lane.
--
-- This owner remains fail-closed until the runtime receipt is generated.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

commonDimension : Nat
commonDimension = 98280

residualNaturalDimension : Nat
residualNaturalDimension = 24

minusDimension : Nat
minusDimension = 98304

commonPlusResidualIsMinus : commonDimension + residualNaturalDimension ≡ minusDimension
commonPlusResidualIsMinus = refl

record CentralizerMod2RuntimeReceipt : Set where
  constructor centralizer-mod2-runtime-receipt
  field
    candidateCount : Nat
    strongCandidateCount : Nat
    rigidSupportCandidateCount : Nat
    residual24IsSingleDegree24Simple : Bool
    residual276ProfileIsOne274One : Bool
    common98280SupportSeparatedFromResidual24 : Bool
    common98280SupportSeparatedFromResidual276 : Bool

record CancellationRigidityBoundary : Set where
  constructor cancellation-rigidity-boundary
  field
    decompositionScreenImplemented : Bool
    runtimeDecompositionPaid : Bool
    actualTateJHProfileOne274OnePaid : Bool
    common98280SupportSeparated : Bool
    actualNormCommon98280IsomorphismPaid : Bool
    actualTateExteriorSquareWeldPaid : Bool

canonicalCancellationRigidityBoundary : CancellationRigidityBoundary
canonicalCancellationRigidityBoundary =
  cancellation-rigidity-boundary
    true false false false false false

runtimeDecompositionStillOpen :
  CancellationRigidityBoundary.runtimeDecompositionPaid
    canonicalCancellationRigidityBoundary
  ≡ false
runtimeDecompositionStillOpen = refl

actualNormCommon98280StillOpen :
  CancellationRigidityBoundary.actualNormCommon98280IsomorphismPaid
    canonicalCancellationRigidityBoundary
  ≡ false
actualNormCommon98280StillOpen = refl

actualTateExteriorSquareWeldStillOpen :
  CancellationRigidityBoundary.actualTateExteriorSquareWeldPaid
    canonicalCancellationRigidityBoundary
  ≡ false
actualTateExteriorSquareWeldStillOpen = refl
