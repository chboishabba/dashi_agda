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
-- For a centred zero coordinate
--
--   z_i = gamma_i - i alpha_i,
--
-- two kernels naturally occur after complex continuation of the Gabor/Poisson
-- identity:
--
--   bilinear:   Phi(z_i - z_j)
--               transverse channel alpha_i - alpha_j,
--
--   Hermitian:  Phi(z_i - conjugate(z_j))
--               transverse channel alpha_i + alpha_j.
--
-- Hence on the diagonal i=j:
--
--   bilinear transverse argument  = 0,
--   Hermitian transverse argument = 2 alpha_i.
--
-- This exact signed-coordinate algebra explains why the published diagonal
-- bilinear square has a displacement-blind baseline while the proposed
-- Hermitian norm can retain |alpha|.  It does NOT prove the analytic complex
-- Poisson continuation itself.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_; -[1+_]; _+_; _-_; -_)
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:-_; con; _:=_)

record CentredComplexCoordinate : Set where
  constructor centredComplexCoordinate
  field
    ordinate : ℤ
    transverse : ℤ

open CentredComplexCoordinate public

------------------------------------------------------------------------
-- We represent only the two real coordinates of a complex difference:
-- (real/ordinate difference, coefficient of -i).
------------------------------------------------------------------------

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

------------------------------------------------------------------------
-- Diagonal separation.
------------------------------------------------------------------------

bilinearDiagonalTransverseVanishes :
  (x : CentredComplexCoordinate) →
  transverseChannel (bilinearArgument x x) ≡ + 0
bilinearDiagonalTransverseVanishes (centredComplexCoordinate gamma alpha) =
  solve 1
    (λ alpha → alpha :- alpha := con (+ 0))
    refl
    alpha

hermitianDiagonalTransverseDoubles :
  (x : CentredComplexCoordinate) →
  transverseChannel (hermitianArgument x x)
    ≡ transverse x + transverse x
hermitianDiagonalTransverseDoubles x = refl

bilinearDiagonalOrdinateVanishes :
  (x : CentredComplexCoordinate) →
  ordinateDifference (bilinearArgument x x) ≡ + 0
bilinearDiagonalOrdinateVanishes (centredComplexCoordinate gamma alpha) =
  solve 1
    (λ gamma → gamma :- gamma := con (+ 0))
    refl
    gamma

hermitianDiagonalOrdinateVanishes :
  (x : CentredComplexCoordinate) →
  ordinateDifference (hermitianArgument x x) ≡ + 0
hermitianDiagonalOrdinateVanishes = bilinearDiagonalOrdinateVanishes

------------------------------------------------------------------------
-- Reflection alpha -> -alpha.
--
-- The diagonal bilinear channel is fixed at zero.  The Hermitian channel flips
-- orientation but keeps the same inverse-pair magnitude role: +2 alpha <->
-- -2 alpha.  Thus any even observable of this channel descends through the
-- reflection orbit while retaining transverse magnitude.
------------------------------------------------------------------------

reflectCoordinate : CentredComplexCoordinate → CentredComplexCoordinate
reflectCoordinate x =
  centredComplexCoordinate (ordinate x) (- transverse x)

reflectCoordinateInvolutive :
  (x : CentredComplexCoordinate) →
  reflectCoordinate (reflectCoordinate x) ≡ x
reflectCoordinateInvolutive (centredComplexCoordinate gamma (+ alpha)) = refl
reflectCoordinateInvolutive (centredComplexCoordinate gamma -[1+ alpha ]) = refl

hermitianDiagonalReflectionFlipsChannel :
  (x : CentredComplexCoordinate) →
  transverseChannel (hermitianArgument (reflectCoordinate x) (reflectCoordinate x))
    ≡ - transverseChannel (hermitianArgument x x)
hermitianDiagonalReflectionFlipsChannel (centredComplexCoordinate gamma alpha) =
  solve 1
    (λ alpha → ((con (+ 0) :- alpha) :+ (con (+ 0) :- alpha))
      := con (+ 0) :- (alpha :+ alpha))
    refl
    alpha

bilinearDiagonalReflectionStillZero :
  (x : CentredComplexCoordinate) →
  transverseChannel
    (bilinearArgument (reflectCoordinate x) (reflectCoordinate x)) ≡ + 0
bilinearDiagonalReflectionStillZero x =
  bilinearDiagonalTransverseVanishes (reflectCoordinate x)

------------------------------------------------------------------------
-- Two-point channel algebra.
------------------------------------------------------------------------

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
    refl
    alphaX alphaY

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
    refl
    alphaX alphaY

------------------------------------------------------------------------
-- Boundary.
------------------------------------------------------------------------

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
