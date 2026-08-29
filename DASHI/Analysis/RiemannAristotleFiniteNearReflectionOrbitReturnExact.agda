module DASHI.Analysis.RiemannAristotleFiniteNearReflectionOrbitReturnExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE-EXACT LEAN RETURN: FINITE NEAR CARRIER IS REFLECTION-STABLE
--
-- In the supplied Lean source, membership in `nearOffFinset t J` is exactly
--
--   |Im sigma - t| < J,
--
-- while `reflectZero` preserves the imaginary part and is involutive on the
-- zero carrier.  Hence the finite near carrier is stable under functional-
-- equation reflection.  Moreover its summand is already the reflection pair
--
--   Z_sigma + Z_{R sigma},
--
-- whose exact kernel has the odd-height sinh*sin term cancelled.
--
-- This file records that source fact without promoting the Lean theorem into an
-- Agda proof of zeta-zero semantics.
------------------------------------------------------------------------

record FiniteNearReflectionOrbitReturn : Set where
  constructor finite-near-reflection-orbit-return
  field
    nearMembershipDependsOnlyOnImaginaryGap : Bool
    nearMembershipDependsOnlyOnImaginaryGapIsTrue :
      nearMembershipDependsOnlyOnImaginaryGap ≡ true

    reflectionPreservesImaginaryPart : Bool
    reflectionPreservesImaginaryPartIsTrue :
      reflectionPreservesImaginaryPart ≡ true

    reflectionInvolutiveOnZeros : Bool
    reflectionInvolutiveOnZerosIsTrue :
      reflectionInvolutiveOnZeros ≡ true

    finiteNearCarrierReflectionStableBySource : Bool
    finiteNearCarrierReflectionStableBySourceIsTrue :
      finiteNearCarrierReflectionStableBySource ≡ true

    nearSummandAlreadyReflectionPaired : Bool
    nearSummandAlreadyReflectionPairedIsTrue :
      nearSummandAlreadyReflectionPaired ≡ true

    oddHeightChannelCancelledInPairKernel : Bool
    oddHeightChannelCancelledInPairKernelIsTrue :
      oddHeightChannelCancelledInPairKernel ≡ true

    conjugationOrbitCompressionOwned : Bool
    conjugationOrbitCompressionOwnedIsFalse :
      conjugationOrbitCompressionOwned ≡ false

    transportedAsAgdaZetaTheorem : Bool
    transportedAsAgdaZetaTheoremIsFalse :
      transportedAsAgdaZetaTheorem ≡ false

    boundedReading : String

open FiniteNearReflectionOrbitReturn public

canonicalFiniteNearReflectionOrbitReturn : FiniteNearReflectionOrbitReturn
canonicalFiniteNearReflectionOrbitReturn =
  finite-near-reflection-orbit-return
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    "The finite literal nearOffFinset carrier is source-stable under functional-equation reflection because membership depends only on the ordinate gap and reflection preserves the ordinate. Its stored summand is already Z_sigma + Z_Rsigma, so the odd-height channel is cancelled before the finite signed estimate. No conjugation-orbit quotient is claimed: no checked conjugation carrier API has been identified in the supplied source."
