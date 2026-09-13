module DASHI.Physics.Closure.NSTriadKNCanonicalDyadicEuclideanAnnulusRound518Exact where

------------------------------------------------------------------------
-- ROUND518 / CANONICAL DYADIC -> EUCLIDEAN-SQUARE ANNULUS
--
-- R517 correctly leaves the cutoff-uniform dyadic H^(1/2)/H^(3/2) norm
-- equivalence open.  Before treating that as one monolithic analysis theorem,
-- close the finite arithmetic actually available on the literal Fourier mode
-- carrier.
--
-- For j = shellIndex(k), R88 and the ceil-log bounds imply
--
--   2^(2(j-1)) <= |k|_2^2 <= 3 * 2^(2j)
--
-- whenever j>0.  The upper bound holds for every mode.  Thus the canonical
-- dyadic weight and the literal Euclidean squared radius are already uniformly
-- comparable before any square root / fractional Sobolev multiplier is
-- introduced.
--
-- The remaining R517 receipt is therefore narrower: transport these squared-
-- radius bounds through the physical fractional multiplier and finite Fourier
-- norm, rather than reproving shell geometry or packet localization.
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
import DASHI.Physics.Closure.NSTriadKNDyadicCriticalNormEquivalenceBoundaryRound517Exact as R517

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

round518R517HOneHalfEquivalenceClosed : Bool
round518R517HOneHalfEquivalenceClosed =
  R517.round517UniformDyadicHOneHalfEquivalenceClosed

round518R517HThreeHalfEquivalenceClosed : Bool
round518R517HThreeHalfEquivalenceClosed =
  R517.round517UniformDyadicHThreeHalfEquivalenceClosed

round518RemainingCoordinateIsFractionalMultiplierTransport : Bool
round518RemainingCoordinateIsFractionalMultiplierTransport = true

round518ClayPromotion : Bool
round518ClayPromotion = false

round518CanonicalDyadicEuclideanSquaredAnnulusClosedIsTrue :
  round518CanonicalDyadicEuclideanSquaredAnnulusClosed ≡ true
round518CanonicalDyadicEuclideanSquaredAnnulusClosedIsTrue = refl

round518RequiresSquareRootToCloseFiniteShellGeometryIsFalse :
  round518RequiresSquareRootToCloseFiniteShellGeometry ≡ false
round518RequiresSquareRootToCloseFiniteShellGeometryIsFalse = refl

round518R517HOneHalfEquivalenceClosedIsFalse :
  round518R517HOneHalfEquivalenceClosed ≡ false
round518R517HOneHalfEquivalenceClosedIsFalse =
  R517.round517UniformDyadicHOneHalfEquivalenceClosedIsFalse

round518R517HThreeHalfEquivalenceClosedIsFalse :
  round518R517HThreeHalfEquivalenceClosed ≡ false
round518R517HThreeHalfEquivalenceClosedIsFalse =
  R517.round517UniformDyadicHThreeHalfEquivalenceClosedIsFalse

round518ClayPromotionIsFalse : round518ClayPromotion ≡ false
round518ClayPromotionIsFalse = refl
