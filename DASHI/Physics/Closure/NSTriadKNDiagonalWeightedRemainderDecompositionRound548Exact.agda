module DASHI.Physics.Closure.NSTriadKNDiagonalWeightedRemainderDecompositionRound548Exact where

------------------------------------------------------------------------
-- ROUND548 / DIAGONAL R406 NONLINEAR REMAINDER = GRAM + WEIGHTED FLUX TANGENT
--
-- R547 isolates the diagonal of the symmetric physical pair scalar
--
--   F(alpha,alpha) = w_aa * r_aa.
--
-- This is NOT the same object as the older R447 Cauchy/Gram diagonal.  However
-- R290 already gives, for every damped Gram pair,
--
--   weightedFluxTangent = - gram + weightedNonlinearRemainder.
--
-- Hence exactly
--
--   weightedNonlinearRemainder = gram + weightedFluxTangent.
--
-- Specializing to the literal double-mixed self-pair therefore turns R547's
-- nonlinear diagonal into a nonnegative self-Gram term plus a weighted
-- self-Gram flux tangent.  No integration or sign estimate is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; Positive; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNWeightedGramFluxCompilerRound290Exact as R290
import DASHI.Physics.Closure.NSTriadKNDoubleMixedGramPairToResolventRound389Exact as R389
import DASHI.Physics.Closure.NSTriadKNDirectResolventPairSwapSymmetryRound538Exact as R538

F : C3.RealField _
F = Rational.rationalRealField

weightedRemainderIsGramPlusFluxTangent :
  (pair : R290.DampedGramPair) →
  R290.weightedNonlinearRemainder pair
  ≡ R290.gram pair + R290.weightedGramFluxTangent pair
weightedRemainderIsGramPlusFluxTangent pair
  rewrite R290.weightedFluxDerivativeIdentity pair =
  solve
    (R290.gram pair
      ∷ R290.weightedNonlinearRemainder pair
      ∷ [])

module PhysicalDiagonal
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem F)
    (S : Helical.HelicalModeScalars F) where

  module Pair = R389.DoubleMixedPair physicalSystem S
  module Swap = R538.PairSwap physicalSystem S

  selfPair :
    (alpha : Physical.PhysicalTriadIncidence) →
    Positive (R291.pairRate (Pair.physicalDoubleMixedPair alpha alpha)) →
    R290.DampedGramPair
  selfPair alpha positive =
    Pair.pairRatePositiveBuildsR290 alpha alpha positive

  diagonalScalar : Physical.PhysicalTriadIncidence → ℚ
  diagonalScalar alpha = Swap.symmetricWeightedRemainder alpha alpha

  diagonalGram :
    (alpha : Physical.PhysicalTriadIncidence) →
    Positive (R291.pairRate (Pair.physicalDoubleMixedPair alpha alpha)) → ℚ
  diagonalGram alpha positive = R290.gram (selfPair alpha positive)

  diagonalFluxTangent :
    (alpha : Physical.PhysicalTriadIncidence) →
    Positive (R291.pairRate (Pair.physicalDoubleMixedPair alpha alpha)) → ℚ
  diagonalFluxTangent alpha positive =
    R290.weightedGramFluxTangent (selfPair alpha positive)

  diagonalFlux :
    (alpha : Physical.PhysicalTriadIncidence) →
    Positive (R291.pairRate (Pair.physicalDoubleMixedPair alpha alpha)) → ℚ
  diagonalFlux alpha positive =
    R290.weightedGramFlux (selfPair alpha positive)

  diagonalScalarDecomposition :
    (alpha : Physical.PhysicalTriadIncidence) →
    (positive : Positive
      (R291.pairRate (Pair.physicalDoubleMixedPair alpha alpha))) →
    diagonalScalar alpha
    ≡ diagonalGram alpha positive + diagonalFluxTangent alpha positive
  diagonalScalarDecomposition alpha positive =
    trans
      (sym
        (Swap.literalR290WeightedRemainderIsSymmetricScalar
          alpha alpha positive))
      (weightedRemainderIsGramPlusFluxTangent (selfPair alpha positive))

round548GenericR290DiagonalDecompositionClosed : Bool
round548GenericR290DiagonalDecompositionClosed = true

round548PhysicalDiagonalNonlinearDecompositionClosed : Bool
round548PhysicalDiagonalNonlinearDecompositionClosed = true

round548DiagonalFluxActualTimeDerivativeProved : Bool
round548DiagonalFluxActualTimeDerivativeProved = false

round548SignedSpacetimeEstimateClosed : Bool
round548SignedSpacetimeEstimateClosed = false

round548ClayPromotion : Bool
round548ClayPromotion = false

round548PhysicalDiagonalNonlinearDecompositionClosedIsTrue :
  round548PhysicalDiagonalNonlinearDecompositionClosed ≡ true
round548PhysicalDiagonalNonlinearDecompositionClosedIsTrue = refl

round548ClayPromotionIsFalse : round548ClayPromotion ≡ false
round548ClayPromotionIsFalse = refl
