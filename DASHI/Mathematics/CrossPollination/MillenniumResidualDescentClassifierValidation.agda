module DASHI.Mathematics.CrossPollination.MillenniumResidualDescentClassifierValidation where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Mathematics.CrossPollination.MillenniumResidualDescentClassifierExact as Residual

------------------------------------------------------------------------
-- The classifier itself is positive infrastructure.
------------------------------------------------------------------------

validationHodgeReopeningRecognition :
  Residual.hodgeConjectureRecognizedAsReopening
    Residual.canonicalMillenniumResidualClassifierBoundary
  ≡ true
validationHodgeReopeningRecognition = refl

validationBSDTwoObserverRecognition :
  Residual.bsdRankConjectureRecognizedAsTwoObserverWeld
    Residual.canonicalMillenniumResidualClassifierBoundary
  ≡ true
validationBSDTwoObserverRecognition = refl

validationUniformNonDescentGrammar :
  Residual.uniformNonDescentGrammarAvailable
    Residual.canonicalMillenniumResidualClassifierBoundary
  ≡ true
validationUniformNonDescentGrammar = refl

validationPostcompositionNoRepair :
  Residual.postcompositionCannotRestoreErasedInformation
    Residual.canonicalMillenniumResidualClassifierBoundary
  ≡ true
validationPostcompositionNoRepair = refl

------------------------------------------------------------------------
-- Millennium theorem-bearing inputs remain fail-closed.
------------------------------------------------------------------------

validationNoHodgeLift :
  Residual.hodgeAlgebraicLiftConstructed
    Residual.canonicalMillenniumResidualClassifierBoundary
  ≡ false
validationNoHodgeLift = refl

validationNoUnconditionalBSDRankWeld :
  Residual.bsdRankWeldConstructedUnconditionally
    Residual.canonicalMillenniumResidualClassifierBoundary
  ≡ false
validationNoUnconditionalBSDRankWeld = refl

validationNoPolynomialAlgorithmExhaustion :
  Residual.polynomialAlgorithmFamilyExhaustionConstructed
    Residual.canonicalMillenniumResidualClassifierBoundary
  ≡ false
validationNoPolynomialAlgorithmExhaustion = refl

validationNoMillenniumPromotion :
  Residual.anyOfThreeMillenniumProblemsSolvedHere
    Residual.canonicalMillenniumResidualClassifierBoundary
  ≡ false
validationNoMillenniumPromotion = refl

validationPvsNPCoverageStillOpen :
  Residual.candidateFamilyCoverageOfAllPolynomialAlgorithmsPaid
    Residual.canonicalPvsNPUniformNonDescentResearchBoundary
  ≡ false
validationPvsNPCoverageStillOpen = refl

validationPvsNPUniformObstructionStillOpen :
  Residual.npCompleteUniformObstructionPaid
    Residual.canonicalPvsNPUniformNonDescentResearchBoundary
  ≡ false
validationPvsNPUniformObstructionStillOpen = refl
