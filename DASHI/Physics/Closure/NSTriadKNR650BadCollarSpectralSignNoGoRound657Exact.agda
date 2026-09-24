{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650BadCollarSpectralSignNoGoRound657Exact where

------------------------------------------------------------------------
-- ROUND657 / BAD-COLLAR PURE SPECTRAL-SIGN NO-GO
--
-- R656 removes the remote cross and the spectrally good part of the collar.
-- The surviving bad collar is NOT another candidate for the same frequency-
-- ordering argument.
--
-- At K = 1 (threshold shell j = 2), the literal witness pair is
--
--   low mode      (2,2,2): shellIndex = 1, |k|^2 = 12,
--   bad-collar    (3,0,0): shellIndex = 2, |k|^2 = 9.
--
-- Thus the bad collar contains a mode with strictly LOWER Euclidean frequency
-- than a legitimate low-packet mode.  With equal positive packet energies and
-- viscosity normalization, the corresponding abstract spectral cross is
--
--     1 * 12 - 9 * 1 = 3 > 0.
--
-- Therefore the surviving R656 cap cannot be eliminated by any theorem that
-- uses only the ordering "bad-collar frequencies >= low frequencies".  The
-- next useful proof must see additional signed nonlinear/covariance structure,
-- trajectory information, or a finer state-dependent decomposition.
--
-- This does NOT refute C2 or any state-dependent collar estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _/_; _-_; _*_; _<_)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNS2b2AdjacentShellSpectralGapNoGoExact as Adjacent
import DASHI.Physics.Closure.NSTriadKNLowCollarRemotePacketSplitExact as Split
import DASHI.Physics.Closure.NSTriadKNR650EuclideanCollarRefinementRound656Exact as R656

badCollarWitnessIsSelected :
  R656.badCollarPacket 1 Adjacent.highWitness ≡ true
badCollarWitnessIsSelected = refl

lowWitnessStillSelected :
  Split.lowPacket 2 Adjacent.lowWitness
  ≡ true
lowWitnessStillSelected = Adjacent.lowWitnessIsInLowerPacketAtTwo

nine twelve three : ℚ
nine = Int.+ 9 / 1
twelve = Int.+ 12 / 1
three = Int.+ 3 / 1

normalizedBadCollarSpectralCross : ℚ
normalizedBadCollarSpectralCross =
  1ℚ * twelve - nine * 1ℚ

normalizedBadCollarSpectralCrossIsThree :
  normalizedBadCollarSpectralCross ≡ three
normalizedBadCollarSpectralCrossIsThree = solve []

normalizedBadCollarSpectralCrossPositive :
  0ℚ < normalizedBadCollarSpectralCross
normalizedBadCollarSpectralCrossPositive =
  ℚP.positive⁻¹ normalizedBadCollarSpectralCross

round657ConcreteBadCollarFrequencyInversionWitness : Bool
round657ConcreteBadCollarFrequencyInversionWitness = true

round657PureFrequencyOrderingPaysBadCollarCross : Bool
round657PureFrequencyOrderingPaysBadCollarCross = false

round657BadCollarNeedsSignedNonlinearOrStateDependentInput : Bool
round657BadCollarNeedsSignedNonlinearOrStateDependentInput = true

round657ActualC2Refuted : Bool
round657ActualC2Refuted = false

round657IntroducesNewClayLeaf : Bool
round657IntroducesNewClayLeaf = false

round657ClayPromotion : Bool
round657ClayPromotion = false

round657ConcreteBadCollarFrequencyInversionWitnessIsTrue :
  round657ConcreteBadCollarFrequencyInversionWitness ≡ true
round657ConcreteBadCollarFrequencyInversionWitnessIsTrue = refl

round657PureFrequencyOrderingPaysBadCollarCrossIsFalse :
  round657PureFrequencyOrderingPaysBadCollarCross ≡ false
round657PureFrequencyOrderingPaysBadCollarCrossIsFalse = refl

round657BadCollarNeedsSignedNonlinearOrStateDependentInputIsTrue :
  round657BadCollarNeedsSignedNonlinearOrStateDependentInput ≡ true
round657BadCollarNeedsSignedNonlinearOrStateDependentInputIsTrue = refl

round657ActualC2RefutedIsFalse :
  round657ActualC2Refuted ≡ false
round657ActualC2RefutedIsFalse = refl

round657IntroducesNewClayLeafIsFalse :
  round657IntroducesNewClayLeaf ≡ false
round657IntroducesNewClayLeafIsFalse = refl

round657ClayPromotionIsFalse :
  round657ClayPromotion ≡ false
round657ClayPromotionIsFalse = refl
