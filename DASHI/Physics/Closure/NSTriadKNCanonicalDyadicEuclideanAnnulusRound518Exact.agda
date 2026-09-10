module DASHI.Physics.Closure.NSTriadKNCanonicalDyadicEuclideanAnnulusRound518Exact where

------------------------------------------------------------------------
-- ROUND518 / CANONICAL DYADIC -> EUCLIDEAN-SQUARE ANNULUS
--
-- Close the finite arithmetic on the literal Fourier mode carrier before any
-- fractional multiplier is introduced.  For j = shellIndex(k), R88 and the
-- ceil-log bounds imply
--
--   2^(2(j-1)) <= |k|_2^2 <= 3 * 2^(2j)
--
-- whenever j>0.  The upper bound holds for every mode.
--
-- This owner is now deliberately independent of the later R517 whole-norm
-- status.  R519+ and the finite Fourier-order owners consume this geometry;
-- R518 no longer imports a downstream historical Boolean merely to mirror it.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_; _<_; _∸_)
import Data.Nat.Properties as Nat

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSPeriodicConcreteIntegerModeNorm as ModeNorm
import DASHI.Physics.Closure.NSTriadKNOfficialInfinityNormTriangle as Infinity
import DASHI.Physics.Closure.NSTriadKNLiteralDyadicShellConstants as Shell
import DASHI.Physics.Closure.NSTriadKNCeilLogShellBounds as Ceil
import DASHI.Physics.Closure.NSTriadKNDyadicEuclideanShellMarginRound88Exact as R88

canonicalDyadicLowerSquare : Z3.FourierMode → Nat
canonicalDyadicLowerSquare k =
  R88.natSquare (Shell.pow2 (Shell.shellIndex k ∸ 1))

canonicalDyadicUpperSquare : Z3.FourierMode → Nat
canonicalDyadicUpperSquare k =
  3 * R88.natSquare (Shell.pow2 (Shell.shellIndex k))

canonicalLowerSquareBelowModeNorm :
  (k : Z3.FourierMode) →
  0 < Shell.shellIndex k →
  canonicalDyadicLowerSquare k ≤ ModeNorm.modeNatNormSquared k
canonicalLowerSquareBelowModeNorm k positive =
  let
    lowerStrict :
      Shell.pow2 (Shell.shellIndex k ∸ 1)
      < Infinity.infinityNorm k
    lowerStrict =
      Ceil.ceilLogShellLowerMagnitude (Infinity.infinityNorm k) positive

    lowerMagnitude :
      Shell.pow2 (Shell.shellIndex k ∸ 1)
      ≤ Infinity.infinityNorm k
    lowerMagnitude = Nat.<⇒≤ lowerStrict

    lowerSquare :
      canonicalDyadicLowerSquare k
      ≤ R88.natSquare (Infinity.infinityNorm k)
    lowerSquare = R88.squareMonotone lowerMagnitude
  in
  Nat.≤-trans lowerSquare (R88.infinitySquareBelowModeNatNorm k)

modeNormBelowCanonicalUpperSquare :
  (k : Z3.FourierMode) →
  ModeNorm.modeNatNormSquared k ≤ canonicalDyadicUpperSquare k
modeNormBelowCanonicalUpperSquare k =
  R88.modeNatNormBelowPacketThreeSquare
    {k = k}
    {K = Shell.shellIndex k}
    Nat.≤-refl

record CanonicalDyadicEuclideanAnnulus (k : Z3.FourierMode) : Set where
  constructor canonical-dyadic-euclidean-annulus
  field
    positiveShell : 0 < Shell.shellIndex k
    lowerSquaredRadius :
      canonicalDyadicLowerSquare k ≤ ModeNorm.modeNatNormSquared k
    upperSquaredRadius :
      ModeNorm.modeNatNormSquared k ≤ canonicalDyadicUpperSquare k

open CanonicalDyadicEuclideanAnnulus public

canonicalPositiveShellAnnulus :
  (k : Z3.FourierMode) →
  (positive : 0 < Shell.shellIndex k) →
  CanonicalDyadicEuclideanAnnulus k
canonicalPositiveShellAnnulus k positive = record
  { positiveShell = positive
  ; lowerSquaredRadius = canonicalLowerSquareBelowModeNorm k positive
  ; upperSquaredRadius = modeNormBelowCanonicalUpperSquare k
  }

------------------------------------------------------------------------
-- Frontier refinement.
------------------------------------------------------------------------

round518CanonicalDyadicEuclideanSquaredAnnulusClosed : Bool
round518CanonicalDyadicEuclideanSquaredAnnulusClosed = true

round518RequiresSquareRootToCloseFiniteShellGeometry : Bool
round518RequiresSquareRootToCloseFiniteShellGeometry = false

round518IntroducesWholeNormAssumption : Bool
round518IntroducesWholeNormAssumption = false

round518DownstreamStatusDependencyRemoved : Bool
round518DownstreamStatusDependencyRemoved = true

round518ClayPromotion : Bool
round518ClayPromotion = false

round518CanonicalDyadicEuclideanSquaredAnnulusClosedIsTrue :
  round518CanonicalDyadicEuclideanSquaredAnnulusClosed ≡ true
round518CanonicalDyadicEuclideanSquaredAnnulusClosedIsTrue = refl

round518RequiresSquareRootToCloseFiniteShellGeometryIsFalse :
  round518RequiresSquareRootToCloseFiniteShellGeometry ≡ false
round518RequiresSquareRootToCloseFiniteShellGeometryIsFalse = refl

round518DownstreamStatusDependencyRemovedIsTrue :
  round518DownstreamStatusDependencyRemoved ≡ true
round518DownstreamStatusDependencyRemovedIsTrue = refl

round518ClayPromotionIsFalse : round518ClayPromotion ≡ false
round518ClayPromotionIsFalse = refl
