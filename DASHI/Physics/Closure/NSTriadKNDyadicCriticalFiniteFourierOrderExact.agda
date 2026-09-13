module DASHI.Physics.Closure.NSTriadKNDyadicCriticalFiniteFourierOrderExact where

------------------------------------------------------------------------
-- DYADIC / PHYSICAL CRITICAL MULTIPLIER COMPARISON ON FINITE FOURIER SUMS
--
-- R518 supplies squared-radius bounds on each positive dyadic shell.  R519 now
-- transports those bounds through the constructed Bishop Nat square root.
-- BishopFiniteWeightedSumOrderExact lifts the modewise comparisons through an
-- arbitrary finite Fourier list against any nonnegative modal mass.
--
-- H^(1/2) uses the root multiplier.  H^(3/2) uses its cube.  Because all three
-- root weights are nonnegative, the same modewise order transports through the
-- cube by vendor/bishop's monotone multiplication.  No Navier--Stokes
-- cancellation estimate or postulate is introduced.
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

cube : BishopReal.ℝ → BishopReal.ℝ
cube x = BishopReal._*_ (BishopReal._*_ x x) x

lowerCriticalThreeHalfWeight : Z3.FourierMode → BishopReal.ℝ
lowerCriticalThreeHalfWeight k = cube (lowerCriticalWeight k)

physicalCriticalThreeHalfWeight : Z3.FourierMode → BishopReal.ℝ
physicalCriticalThreeHalfWeight k = cube (physicalCriticalWeight k)

upperCriticalThreeHalfWeight : Z3.FourierMode → BishopReal.ℝ
upperCriticalThreeHalfWeight k = cube (upperCriticalWeight k)

rootNonnegative :
  (n : Agda.Builtin.Nat.Nat) →
  BishopReal.NonNegative (R519.sqrtNat n)
rootNonnegative = R519.canonicalNatRootNonnegative

cubeMonotone :
  ∀ {x y : BishopReal.ℝ} →
  BishopReal.NonNegative x →
  BishopReal.NonNegative y →
  BishopReal._≤_ x y →
  BishopReal._≤_ (cube x) (cube y)
cubeMonotone {x} {y} xNN yNN x≤y =
  let
    squareNNx : BishopReal.NonNegative (BishopReal._*_ x x)
    squareNNx = BishopProps.nonNegx,y⇒nonNegx*y xNN xNN

    squareNNy : BishopReal.NonNegative (BishopReal._*_ y y)
    squareNNy = BishopProps.nonNegx,y⇒nonNegx*y yNN yNN

    squareOrder :
      BishopReal._≤_ (BishopReal._*_ x x) (BishopReal._*_ y y)
    squareOrder = BishopProps.*-mono-≤ xNN xNN x≤y x≤y
  in
  BishopProps.*-mono-≤ squareNNx xNN squareOrder x≤y

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

modewiseLowerCriticalThreeHalfWeight :
  (k : Z3.FourierMode) →
  0 < Shell.shellIndex k →
  BishopReal._≤_
    (lowerCriticalThreeHalfWeight k)
    (physicalCriticalThreeHalfWeight k)
modewiseLowerCriticalThreeHalfWeight k positive =
  cubeMonotone
    (rootNonnegative (R518.canonicalDyadicLowerSquare k))
    (rootNonnegative (ModeNorm.modeNatNormSquared k))
    (modewiseLowerCriticalWeight k positive)

modewiseUpperCriticalThreeHalfWeight :
  (k : Z3.FourierMode) →
  0 < Shell.shellIndex k →
  BishopReal._≤_
    (physicalCriticalThreeHalfWeight k)
    (upperCriticalThreeHalfWeight k)
modewiseUpperCriticalThreeHalfWeight k positive =
  cubeMonotone
    (rootNonnegative (ModeNorm.modeNatNormSquared k))
    (rootNonnegative (R518.canonicalDyadicUpperSquare k))
    (modewiseUpperCriticalWeight k positive)

record FiniteCriticalWeightComparison
    (items : List Z3.FourierMode)
    (mass : Z3.FourierMode → BishopReal.ℝ) : Set where
  constructor finite-critical-weight-comparison
  field
    allPositiveShell :
      (k : Z3.FourierMode) → OccursIn k items → 0 < Shell.shellIndex k
    massNonnegative :
      (k : Z3.FourierMode) → BishopReal.NonNegative (mass k)

    lowerHalfSumBelowPhysical :
      BishopReal._≤_
        (Sum.weightedSum lowerCriticalWeight mass items)
        (Sum.weightedSum physicalCriticalWeight mass items)
    physicalHalfSumBelowUpper :
      BishopReal._≤_
        (Sum.weightedSum physicalCriticalWeight mass items)
        (Sum.weightedSum upperCriticalWeight mass items)

    lowerThreeHalfSumBelowPhysical :
      BishopReal._≤_
        (Sum.weightedSum lowerCriticalThreeHalfWeight mass items)
        (Sum.weightedSum physicalCriticalThreeHalfWeight mass items)
    physicalThreeHalfSumBelowUpper :
      BishopReal._≤_
        (Sum.weightedSum physicalCriticalThreeHalfWeight mass items)
        (Sum.weightedSum upperCriticalThreeHalfWeight mass items)

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
  ; lowerHalfSumBelowPhysical = lowerHalfGo items positive
  ; physicalHalfSumBelowUpper = upperHalfGo items positive
  ; lowerThreeHalfSumBelowPhysical = lowerThreeHalfGo items positive
  ; physicalThreeHalfSumBelowUpper = upperThreeHalfGo items positive
  }
  where
  lowerHalfGo :
    (xs : List Z3.FourierMode) →
    ((k : Z3.FourierMode) → OccursIn k xs → 0 < Shell.shellIndex k) →
    BishopReal._≤_
      (Sum.weightedSum lowerCriticalWeight mass xs)
      (Sum.weightedSum physicalCriticalWeight mass xs)
  lowerHalfGo [] pos = BishopProps.≤-refl
  lowerHalfGo (k ∷ rest) pos =
    let
      head = modewiseLowerCriticalWeight k (pos k here)
      tailPos :
        (x : Z3.FourierMode) → OccursIn x rest → 0 < Shell.shellIndex x
      tailPos x member = pos x (there member)
    in
    BishopProps.+-mono-≤
      (BishopProps.*-monoʳ-≤-nonNeg head (massNN k))
      (lowerHalfGo rest tailPos)

  upperHalfGo :
    (xs : List Z3.FourierMode) →
    ((k : Z3.FourierMode) → OccursIn k xs → 0 < Shell.shellIndex k) →
    BishopReal._≤_
      (Sum.weightedSum physicalCriticalWeight mass xs)
      (Sum.weightedSum upperCriticalWeight mass xs)
  upperHalfGo [] pos = BishopProps.≤-refl
  upperHalfGo (k ∷ rest) pos =
    let
      head = modewiseUpperCriticalWeight k (pos k here)
      tailPos :
        (x : Z3.FourierMode) → OccursIn x rest → 0 < Shell.shellIndex x
      tailPos x member = pos x (there member)
    in
    BishopProps.+-mono-≤
      (BishopProps.*-monoʳ-≤-nonNeg head (massNN k))
      (upperHalfGo rest tailPos)

  lowerThreeHalfGo :
    (xs : List Z3.FourierMode) →
    ((k : Z3.FourierMode) → OccursIn k xs → 0 < Shell.shellIndex k) →
    BishopReal._≤_
      (Sum.weightedSum lowerCriticalThreeHalfWeight mass xs)
      (Sum.weightedSum physicalCriticalThreeHalfWeight mass xs)
  lowerThreeHalfGo [] pos = BishopProps.≤-refl
  lowerThreeHalfGo (k ∷ rest) pos =
    let
      head = modewiseLowerCriticalThreeHalfWeight k (pos k here)
      tailPos :
        (x : Z3.FourierMode) → OccursIn x rest → 0 < Shell.shellIndex x
      tailPos x member = pos x (there member)
    in
    BishopProps.+-mono-≤
      (BishopProps.*-monoʳ-≤-nonNeg head (massNN k))
      (lowerThreeHalfGo rest tailPos)

  upperThreeHalfGo :
    (xs : List Z3.FourierMode) →
    ((k : Z3.FourierMode) → OccursIn k xs → 0 < Shell.shellIndex k) →
    BishopReal._≤_
      (Sum.weightedSum physicalCriticalThreeHalfWeight mass xs)
      (Sum.weightedSum upperCriticalThreeHalfWeight mass xs)
  upperThreeHalfGo [] pos = BishopProps.≤-refl
  upperThreeHalfGo (k ∷ rest) pos =
    let
      head = modewiseUpperCriticalThreeHalfWeight k (pos k here)
      tailPos :
        (x : Z3.FourierMode) → OccursIn x rest → 0 < Shell.shellIndex x
      tailPos x member = pos x (there member)
    in
    BishopProps.+-mono-≤
      (BishopProps.*-monoʳ-≤-nonNeg head (massNN k))
      (upperThreeHalfGo rest tailPos)

roundFiniteHOneHalfMultiplierTransportClosed : Bool
roundFiniteHOneHalfMultiplierTransportClosed = true

roundFiniteHThreeHalfMultiplierTransportClosed : Bool
roundFiniteHThreeHalfMultiplierTransportClosed = true

roundIntroducesNSCancellationEstimate : Bool
roundIntroducesNSCancellationEstimate = false

roundUsesPostulate : Bool
roundUsesPostulate = false

roundClayPromotion : Bool
roundClayPromotion = false

roundFiniteHOneHalfMultiplierTransportClosedIsTrue :
  roundFiniteHOneHalfMultiplierTransportClosed ≡ true
roundFiniteHOneHalfMultiplierTransportClosedIsTrue = refl

roundFiniteHThreeHalfMultiplierTransportClosedIsTrue :
  roundFiniteHThreeHalfMultiplierTransportClosed ≡ true
roundFiniteHThreeHalfMultiplierTransportClosedIsTrue = refl

roundUsesPostulateIsFalse : roundUsesPostulate ≡ false
roundUsesPostulateIsFalse = refl
