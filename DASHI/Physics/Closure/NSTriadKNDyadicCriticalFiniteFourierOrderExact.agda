module DASHI.Physics.Closure.NSTriadKNDyadicCriticalFiniteFourierOrderExact where

------------------------------------------------------------------------
-- DYADIC / PHYSICAL H^(1/2) MULTIPLIER COMPARISON ON FINITE FOURIER SUMS
--
-- R518 supplies squared-radius bounds on each positive dyadic shell.  R519 now
-- transports those bounds through the constructed Bishop Nat square root.
-- BishopFiniteWeightedSumOrderExact then lifts the modewise comparison through
-- an arbitrary finite Fourier list against any nonnegative modal mass.
--
-- This is exactly the finite-carrier transport that R517 left after the scalar
-- root monotonicity seam.  No Navier--Stokes cancellation estimate appears and
-- no postulate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Nat.Base using (_<_)

import Real as BishopReal
import RealProperties as BishopProps

import DASHI.Foundations.BishopFiniteWeightedSumOrderExact as Sum
import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteIntegerModeNorm as ModeNorm
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNCanonicalDyadicEuclideanAnnulusRound518Exact as R518
import DASHI.Physics.Closure.NSTriadKNBishopNatRootCriticalMultiplierBoundaryRound519Exact as R519

-- Tiny local membership type avoids importing another list-membership API into
-- this narrow finite-order owner.
data OccursIn {A : Set} (x : A) : List A → Set where
  here : ∀ {rest} → OccursIn x (x ∷ rest)
  there : ∀ {y rest} → OccursIn x rest → OccursIn x (y ∷ rest)

lowerCriticalWeight : Z3.FourierMode → BishopReal.ℝ
lowerCriticalWeight k = R519.sqrtNat (R518.canonicalDyadicLowerSquare k)

physicalCriticalWeight : Z3.FourierMode → BishopReal.ℝ
physicalCriticalWeight k = R519.sqrtNat (ModeNorm.modeNatNormSquared k)

upperCriticalWeight : Z3.FourierMode → BishopReal.ℝ
upperCriticalWeight k = R519.sqrtNat (R518.canonicalDyadicUpperSquare k)

modewiseLowerCriticalWeight :
  (k : Z3.FourierMode) →
  0 < Shell.shellIndex k →
  BishopReal._≤_ (lowerCriticalWeight k) (physicalCriticalWeight k)
modewiseLowerCriticalWeight k positive =
  R519.lowerRootBelowPhysical
    (R519.canonicalModewiseCriticalMultiplierComparison
      (R518.canonicalLowerSquareBelowModeNorm k positive)
      (R518.modeNormBelowCanonicalUpperSquare k))

modewiseUpperCriticalWeight :
  (k : Z3.FourierMode) →
  0 < Shell.shellIndex k →
  BishopReal._≤_ (physicalCriticalWeight k) (upperCriticalWeight k)
modewiseUpperCriticalWeight k positive =
  R519.physicalRootBelowUpper
    (R519.canonicalModewiseCriticalMultiplierComparison
      (R518.canonicalLowerSquareBelowModeNorm k positive)
      (R518.modeNormBelowCanonicalUpperSquare k))

record FiniteCriticalWeightComparison
    (items : List Z3.FourierMode)
    (mass : Z3.FourierMode → BishopReal.ℝ) : Set where
  constructor finite-critical-weight-comparison
  field
    allPositiveShell :
      (k : Z3.FourierMode) → OccursIn k items → 0 < Shell.shellIndex k
    massNonnegative :
      (k : Z3.FourierMode) → BishopReal.NonNegative (mass k)
    lowerSumBelowPhysical :
      BishopReal._≤_
        (Sum.weightedSum lowerCriticalWeight mass items)
        (Sum.weightedSum physicalCriticalWeight mass items)
    physicalSumBelowUpper :
      BishopReal._≤_
        (Sum.weightedSum physicalCriticalWeight mass items)
        (Sum.weightedSum upperCriticalWeight mass items)

open FiniteCriticalWeightComparison public

buildFiniteCriticalWeightComparison :
  (items : List Z3.FourierMode) →
  (mass : Z3.FourierMode → BishopReal.ℝ) →
  ((k : Z3.FourierMode) → OccursIn k items → 0 < Shell.shellIndex k) →
  ((k : Z3.FourierMode) → BishopReal.NonNegative (mass k)) →
  FiniteCriticalWeightComparison items mass
buildFiniteCriticalWeightComparison items mass positive massNN = record
  { allPositiveShell = positive
  ; massNonnegative = massNN
  ; lowerSumBelowPhysical = lowerGo items positive
  ; physicalSumBelowUpper = upperGo items positive
  }
  where
  lowerGo :
    (xs : List Z3.FourierMode) →
    ((k : Z3.FourierMode) → OccursIn k xs → 0 < Shell.shellIndex k) →
    BishopReal._≤_
      (Sum.weightedSum lowerCriticalWeight mass xs)
      (Sum.weightedSum physicalCriticalWeight mass xs)
  lowerGo [] pos = BishopProps.≤-refl
  lowerGo (k ∷ rest) pos =
    let
      head = modewiseLowerCriticalWeight k (pos k here)
      tailPos :
        (x : Z3.FourierMode) → OccursIn x rest → 0 < Shell.shellIndex x
      tailPos x member = pos x (there member)
    in
    BishopProps.+-mono-≤
      (BishopProps.*-monoʳ-≤-nonNeg head (massNN k))
      (lowerGo rest tailPos)

  upperGo :
    (xs : List Z3.FourierMode) →
    ((k : Z3.FourierMode) → OccursIn k xs → 0 < Shell.shellIndex k) →
    BishopReal._≤_
      (Sum.weightedSum physicalCriticalWeight mass xs)
      (Sum.weightedSum upperCriticalWeight mass xs)
  upperGo [] pos = BishopProps.≤-refl
  upperGo (k ∷ rest) pos =
    let
      head = modewiseUpperCriticalWeight k (pos k here)
      tailPos :
        (x : Z3.FourierMode) → OccursIn x rest → 0 < Shell.shellIndex x
      tailPos x member = pos x (there member)
    in
    BishopProps.+-mono-≤
      (BishopProps.*-monoʳ-≤-nonNeg head (massNN k))
      (upperGo rest tailPos)

roundFiniteHOneHalfMultiplierTransportClosed : Bool
roundFiniteHOneHalfMultiplierTransportClosed = true

roundIntroducesNSCancellationEstimate : Bool
roundIntroducesNSCancellationEstimate = false

roundUsesPostulate : Bool
roundUsesPostulate = false

roundClayPromotion : Bool
roundClayPromotion = false

roundFiniteHOneHalfMultiplierTransportClosedIsTrue :
  roundFiniteHOneHalfMultiplierTransportClosed ≡ true
roundFiniteHOneHalfMultiplierTransportClosedIsTrue = refl

roundUsesPostulateIsFalse : roundUsesPostulate ≡ false
roundUsesPostulateIsFalse = refl
