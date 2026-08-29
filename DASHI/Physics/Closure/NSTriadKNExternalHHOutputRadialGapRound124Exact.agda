module DASHI.Physics.Closure.NSTriadKNExternalHHOutputRadialGapRound124Exact where

------------------------------------------------------------------------
-- ROUND124 / HH->LOW OUTPUT-CONTROLLED RADIAL GAP
--
-- Round123 correctly reduced the external Waleffe residue to a pure
-- multiplier-difference object, but its frontier prose highlighted the generic
-- separation-vector bound |k-2p|.  In the actual HH->low geometry p+q=k with
-- p and q both high and k low, the sharper radial estimate is the reverse
-- triangle inequality
--
--   ||p|-|q|| <= |p+q| = |k|.
--
-- This module closes that geometry exactly for the repository's authoritative
-- integer max norm.  The result is cutoff-independent and uses only the
-- already machine-checked resonant reverse-triangle inequalities.
--
-- On an HH Bony cell the output shell is at least Csep=3 below BOTH high
-- inputs.  Combining the radial-gap estimate with the exact ceil-log shell
-- bounds gives the division-free scale picture
--
--   radialGap(p,q) <= 2^j_k,
--   4 * 2^j_k <= ||p||_infinity,
--   4 * 2^j_k <= ||q||_infinity.
--
-- Thus the commutator gap is carried by the LOW OUTPUT scale, not by the large
-- vector difference q-p.  The remaining seam is to transport this exact
-- lattice radial gain to the physical same-helicity curl eigenvalue gap and
-- then pay the signed HH class in the critical norm.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Nat.Base using (_≤_; _<_; z≤n; s≤s)
import Data.Nat.Properties as Nat
open import Data.Product.Base using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNOfficialInfinityNormTriangle as Infinity
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNCeilLogShellBounds as Ceil
import DASHI.Physics.Closure.NSTriadKNDyadicEuclideanShellMarginRound88Exact as R88
import DASHI.Physics.Closure.NSTriadKNLuoPhysicalFiveClassSupportRound25Exact as Support

------------------------------------------------------------------------
-- A tiny constructive Nat absolute-difference carrier.  It is extensionally
-- the usual distance |m-n|, but the recursive presentation lets the bound below
-- use only the two reverse-triangle inequalities already present in the repo.
------------------------------------------------------------------------

natRadialGap : Nat → Nat → Nat
natRadialGap zero n = n
natRadialGap m zero = m
natRadialGap (suc m) (suc n) = natRadialGap m n

natRadialGapSymmetric : ∀ m n → natRadialGap m n ≡ natRadialGap n m
natRadialGapSymmetric zero zero = refl
natRadialGapSymmetric zero (suc n) = refl
natRadialGapSymmetric (suc m) zero = refl
natRadialGapSymmetric (suc m) (suc n) = natRadialGapSymmetric m n

-- If each number is at most the other plus c, their radial gap is at most c.
natRadialGapBoundFromTwoSidedAddition :
  ∀ m n c →
  m ≤ n + c →
  n ≤ m + c →
  natRadialGap m n ≤ c
natRadialGapBoundFromTwoSidedAddition zero zero c left right = z≤n
natRadialGapBoundFromTwoSidedAddition zero (suc n) c left right = right
natRadialGapBoundFromTwoSidedAddition (suc m) zero c left right = left
natRadialGapBoundFromTwoSidedAddition
  (suc m) (suc n) c (s≤s left) (s≤s right) =
  natRadialGapBoundFromTwoSidedAddition m n c left right

radialInfinityGap : Physical.PhysicalTriadIncidence → Nat
radialInfinityGap tau =
  natRadialGap
    (Infinity.infinityNorm (Physical.p tau))
    (Infinity.infinityNorm (Physical.q tau))

-- Exact resonant reverse-triangle gain:
--   |||p||_infinity-||q||_infinity| <= ||k||_infinity.
resonantRadialInfinityGapBelowOutput :
  (tau : Physical.PhysicalTriadIncidence) →
  radialInfinityGap tau ≤ Infinity.infinityNorm (Physical.k tau)
resonantRadialInfinityGapBelowOutput tau =
  natRadialGapBoundFromTwoSidedAddition
    (Infinity.infinityNorm (Physical.p tau))
    (Infinity.infinityNorm (Physical.q tau))
    (Infinity.infinityNorm (Physical.k tau))
    pBelowQPlusK
    qBelowPPlusK
  where
  consequences = Infinity.officialResonantNormConsequences tau

  pBelowQPlusK :
    Infinity.infinityNorm (Physical.p tau)
    ≤ Infinity.infinityNorm (Physical.q tau)
      + Infinity.infinityNorm (Physical.k tau)
  pBelowQPlusK =
    subst
      (Infinity.infinityNorm (Physical.p tau) ≤_)
      (Nat.+-comm
        (Infinity.infinityNorm (Physical.k tau))
        (Infinity.infinityNorm (Physical.q tau)))
      (Infinity.pReverseTriangle consequences)

  qBelowPPlusK :
    Infinity.infinityNorm (Physical.q tau)
    ≤ Infinity.infinityNorm (Physical.p tau)
      + Infinity.infinityNorm (Physical.k tau)
  qBelowPPlusK =
    subst
      (Infinity.infinityNorm (Physical.q tau) ≤_)
      (Nat.+-comm
        (Infinity.infinityNorm (Physical.k tau))
        (Infinity.infinityNorm (Physical.p tau)))
      (Infinity.qReverseTriangle consequences)

resonantRadialInfinityGapBelowOutputShellScale :
  (tau : Physical.PhysicalTriadIncidence) →
  radialInfinityGap tau ≤ Shell.pow2 (Shell.shellIndex (Physical.k tau))
resonantRadialInfinityGapBelowOutputShellScale tau =
  Nat.≤-trans
    (resonantRadialInfinityGapBelowOutput tau)
    (Ceil.ceilLogShellUpperMagnitude
      (Infinity.infinityNorm (Physical.k tau)))

------------------------------------------------------------------------
-- Three-shell HH separation gives a factor-four lower scale on each high leg.
-- This is the unsquared counterpart of the stronger Round88 Euclidean-square
-- reserve and reuses Round88's already checked shell arithmetic.
------------------------------------------------------------------------

fourOutputScaleBelowSeparatedHighInfinity :
  ∀ {high outputShell} →
  outputShell + Shell.Csep ≤ Shell.shellIndex high →
  4 * Shell.pow2 outputShell ≤ Infinity.infinityNorm high
fourOutputScaleBelowSeparatedHighInfinity {high} {outputShell} separated =
  let
    separatedThree : outputShell + 3 ≤ Shell.shellIndex high
    separatedThree = separated

    separatedSuccessors :
      suc (suc (suc outputShell)) ≤ Shell.shellIndex high
    separatedSuccessors =
      subst
        (_≤ Shell.shellIndex high)
        (R88.plusThreeAsThreeSuccessors outputShell)
        separatedThree

    exponentBelow :
      suc (suc outputShell) ≤ Shell.shellIndex high Nat.∸ 1
    exponentBelow = R88.dropOneFromThreeShellSeparation separatedSuccessors

    powerBelow :
      Shell.pow2 (suc (suc outputShell))
      ≤ Shell.pow2 (Shell.shellIndex high Nat.∸ 1)
    powerBelow = R88.pow2Monotone exponentBelow

    highShellPositive : 0 < Shell.shellIndex high
    highShellPositive =
      R88.threeShellSeparationForcesPositiveHighShell separatedSuccessors

    lowerStrict :
      Shell.pow2 (Shell.shellIndex high Nat.∸ 1)
      < Infinity.infinityNorm high
    lowerStrict =
      Ceil.ceilLogShellLowerMagnitude
        (Infinity.infinityNorm high)
        highShellPositive
  in
  subst
    (_≤ Infinity.infinityNorm high)
    (R88.pow2TwoSuccessorsIsFourTimes outputShell)
    (Nat.<⇒≤ (Nat.≤-<-trans powerBelow lowerStrict))

record HighHighOutputRadialGapGain
    (tau : Physical.PhysicalTriadIncidence) : Set where
  constructor high-high-output-radial-gap-gain
  field
    gapBelowOutputNorm :
      radialInfinityGap tau ≤ Infinity.infinityNorm (Physical.k tau)

    gapBelowOutputShellScale :
      radialInfinityGap tau ≤ Shell.pow2 (Shell.shellIndex (Physical.k tau))

    fourOutputScalesBelowP :
      4 * Shell.pow2 (Shell.shellIndex (Physical.k tau))
      ≤ Infinity.infinityNorm (Physical.p tau)

    fourOutputScalesBelowQ :
      4 * Shell.pow2 (Shell.shellIndex (Physical.k tau))
      ≤ Infinity.infinityNorm (Physical.q tau)

open HighHighOutputRadialGapGain public

highHighOutputRadialGapGain :
  ∀ {tau} →
  Support.TriadicClassCertificate tau Support.HH →
  HighHighOutputRadialGapGain tau
highHighOutputRadialGapGain {tau} certificate =
  high-high-output-radial-gap-gain
    (resonantRadialInfinityGapBelowOutput tau)
    (resonantRadialInfinityGapBelowOutputShellScale tau)
    (fourOutputScaleBelowSeparatedHighInfinity (proj₁ gaps))
    (fourOutputScaleBelowSeparatedHighInfinity (proj₂ gaps))
  where
  gaps = Support.highHighWeakGaps (Support.classMeaning certificate)

round124ResonantRadialGapBelowOutputClosed : Bool
round124ResonantRadialGapBelowOutputClosed = true

round124HHOutputScaleGainClosed : Bool
round124HHOutputScaleGainClosed = true

round124HHUsesOutputReverseTriangleRatherThanLargeSeparationVector : Bool
round124HHUsesOutputReverseTriangleRatherThanLargeSeparationVector = true

round124PhysicalHelicalEigenvalueGapTransportClosed : Bool
round124PhysicalHelicalEigenvalueGapTransportClosed = false

round124HHCriticalSignedClassPaymentClosed : Bool
round124HHCriticalSignedClassPaymentClosed = false

round124ResonantRadialGapBelowOutputClosedIsTrue :
  round124ResonantRadialGapBelowOutputClosed ≡ true
round124ResonantRadialGapBelowOutputClosedIsTrue = refl

round124HHOutputScaleGainClosedIsTrue :
  round124HHOutputScaleGainClosed ≡ true
round124HHOutputScaleGainClosedIsTrue = refl

round124PhysicalHelicalEigenvalueGapTransportClosedIsFalse :
  round124PhysicalHelicalEigenvalueGapTransportClosed ≡ false
round124PhysicalHelicalEigenvalueGapTransportClosedIsFalse = refl

round124HHCriticalSignedClassPaymentClosedIsFalse :
  round124HHCriticalSignedClassPaymentClosed ≡ false
round124HHCriticalSignedClassPaymentClosedIsFalse = refl
