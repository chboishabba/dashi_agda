module DASHI.Analysis.RiemannComplexPoissonChannelSplitExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CALIBRATION
--
-- Levent Alpöge and Ralph Furman,
-- "More than two thirds of the zeta zeros are simple and on the critical line",
-- arXiv:2608.13637 (2026), DOI: 10.48550/arXiv.2608.13637.
--
-- Machine-checked companion consulted:
-- Anthropic, `zeta-23-lean`, especially Zeta23/Defs.lean and
-- Zeta23/Poisson.lean.
--
-- For z_i = gamma_i - i alpha_i, the bilinear channel sees
-- alpha_i-alpha_j while the Hermitian channel sees alpha_i+alpha_j.  Hence
-- diagonal bilinear Poisson is transverse-blind, whereas diagonal Hermitian
-- Poisson sees 2 alpha_i.  This file proves only that exact signed-coordinate
-- algebra, not the analytic complex continuation itself.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (zero; suc)
open import Data.Integer using (ℤ; +_; -[1+_]; _+_; _-_; -_)
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:-_; con; _:=_)

record CentredComplexCoordinate : Set where
  constructor centredComplexCoordinate
  field
    ordinate : ℤ
    transverse : ℤ

open CentredComplexCoordinate public

record PoissonArgument : Set where
  constructor poissonArgument
  field
    ordinateDifference : ℤ
    transverseChannel : ℤ

open PoissonArgument public

bilinearArgument :
  CentredComplexCoordinate → CentredComplexCoordinate → PoissonArgument
bilinearArgument x y =
  poissonArgument
    (ordinate x - ordinate y)
    (transverse x - transverse y)

hermitianArgument :
  CentredComplexCoordinate → CentredComplexCoordinate → PoissonArgument
hermitianArgument x y =
  poissonArgument
    (ordinate x - ordinate y)
    (transverse x + transverse y)

bilinearDiagonalTransverseVanishes :
  (x : CentredComplexCoordinate) →
  transverseChannel (bilinearArgument x x) ≡ + 0
bilinearDiagonalTransverseVanishes (centredComplexCoordinate gamma alpha) =
  solve 1 (λ alpha → alpha :- alpha := con (+ 0)) refl alpha

hermitianDiagonalTransverseDoubles :
  (x : CentredComplexCoordinate) →
  transverseChannel (hermitianArgument x x)
    ≡ transverse x + transverse x
hermitianDiagonalTransverseDoubles x = refl

bilinearDiagonalOrdinateVanishes :
  (x : CentredComplexCoordinate) →
  ordinateDifference (bilinearArgument x x) ≡ + 0
bilinearDiagonalOrdinateVanishes (centredComplexCoordinate gamma alpha) =
  solve 1 (λ gamma → gamma :- gamma := con (+ 0)) refl gamma

hermitianDiagonalOrdinateVanishes :
  (x : CentredComplexCoordinate) →
  ordinateDifference (hermitianArgument x x) ≡ + 0
hermitianDiagonalOrdinateVanishes = bilinearDiagonalOrdinateVanishes

reflectCoordinate : CentredComplexCoordinate → CentredComplexCoordinate
reflectCoordinate x = centredComplexCoordinate (ordinate x) (- transverse x)

reflectCoordinateInvolutive :
  (x : CentredComplexCoordinate) →
  reflectCoordinate (reflectCoordinate x) ≡ x
reflectCoordinateInvolutive (centredComplexCoordinate gamma (+ zero)) = refl
reflectCoordinateInvolutive (centredComplexCoordinate gamma (+ (suc alpha))) = refl
reflectCoordinateInvolutive (centredComplexCoordinate gamma -[1+ alpha ]) = refl

hermitianDiagonalReflectionFlipsChannel :
  (x : CentredComplexCoordinate) →
  transverseChannel (hermitianArgument (reflectCoordinate x) (reflectCoordinate x))
    ≡ - transverseChannel (hermitianArgument x x)
hermitianDiagonalReflectionFlipsChannel (centredComplexCoordinate gamma alpha) =
  solve 1
    (λ alpha → ((con (+ 0) :- alpha) :+ (con (+ 0) :- alpha))
      := con (+ 0) :- (alpha :+ alpha))
    refl alpha

bilinearDiagonalReflectionStillZero :
  (x : CentredComplexCoordinate) →
  transverseChannel
    (bilinearArgument (reflectCoordinate x) (reflectCoordinate x)) ≡ + 0
bilinearDiagonalReflectionStillZero x =
  bilinearDiagonalTransverseVanishes (reflectCoordinate x)

bilinearAndHermitianRecoverTwiceFirstTransverse :
  (x y : CentredComplexCoordinate) →
  transverseChannel (bilinearArgument x y)
    + transverseChannel (hermitianArgument x y)
    ≡ transverse x + transverse x
bilinearAndHermitianRecoverTwiceFirstTransverse
  (centredComplexCoordinate gammaX alphaX)
  (centredComplexCoordinate gammaY alphaY) =
  solve 2
    (λ x y → (x :- y) :+ (x :+ y) := x :+ x)
    refl alphaX alphaY

hermitianMinusBilinearRecoversTwiceSecondTransverse :
  (x y : CentredComplexCoordinate) →
  transverseChannel (hermitianArgument x y)
    - transverseChannel (bilinearArgument x y)
    ≡ transverse y + transverse y
hermitianMinusBilinearRecoversTwiceSecondTransverse
  (centredComplexCoordinate gammaX alphaX)
  (centredComplexCoordinate gammaY alphaY) =
  solve 2
    (λ x y → (x :+ y) :- (x :- y) := y :+ y)
    refl alphaX alphaY

record ComplexPoissonChannelBoundary : Set where
  field
    differenceVsSumChannelSplitConstructed : Bool
    diagonalBilinearBlindnessProved : Bool
    diagonalHermitianDoublingProved : Bool
    reflectionChannelFlipProved : Bool
    analyticComplexPoissonContinuationProvedHere : Bool
    phiEvenCoshCoercivityProvedHere : Bool

complexPoissonChannelBoundary : ComplexPoissonChannelBoundary
complexPoissonChannelBoundary = record
  { differenceVsSumChannelSplitConstructed = true
  ; diagonalBilinearBlindnessProved = true
  ; diagonalHermitianDoublingProved = true
  ; reflectionChannelFlipProved = true
  ; analyticComplexPoissonContinuationProvedHere = false
  ; phiEvenCoshCoercivityProvedHere = false
  }
