module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound40MultiplierLocalityValidation where

------------------------------------------------------------------------
-- Round Forty validation root.
--
-- Imported cumulatively by the Round-39 root on this child branch so the
-- existing pull-request workflow typechecks the complete new tranche.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanSelectedVariationSignConventionExact as Sign
import DASHI.Physics.YangMills.BalabanSelectedMultiplierPairingRedundancyInvariantExact
import DASHI.Physics.YangMills.BalabanSelectedConstraintCollarPairingExact
import DASHI.Physics.YangMills.BalabanSelectedRawExtractorConstraintDefectAtomsExact
import DASHI.Physics.YangMills.BalabanSelectedMultiplierDefectGreenContractionExact
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedResidualOwnershipExact
import DASHI.Physics.YangMills.BalabanSelectedConstraintGramCombesThomasExact
import DASHI.Physics.YangMills.BalabanSelectedKKTMultiplierLocalityExact
import DASHI.Physics.YangMills.BalabanP33FiniteKKTBlockCombesThomasConstantsExact
import DASHI.Physics.YangMills.BalabanP33FiniteKKTBlockInverseExact
import DASHI.Physics.YangMills.BalabanP33ConstraintGramD4CovarianceExact
import DASHI.Physics.YangMills.BalabanP33PhysicalSingletonBudgetOptimizationExact as Optimization
import DASHI.Physics.YangMills.BalabanSelectedBackgroundCoefficientFieldExact as Coefficients
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedSingletonClosureExact

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Rational.Base as ℚ using
  (0ℚ; _+_; _-_; -_; _≤_)

correctedSingletonSignRegression :
  ∀ singleton raw pairing →
  singleton + Sign.canonicalProjectedSpillover raw pairing ≡ 0ℚ →
  singleton ≡ - raw + pairing
correctedSingletonSignRegression = Sign.singletonResidualSignExact

wrongDoubleNegativeRegression :
  ∀ raw pairing →
  (- raw + pairing) ≡ (- raw - pairing) →
  pairing + pairing ≡ 0ℚ
wrongDoubleNegativeRegression =
  Sign.wrongDoubleNegativeWouldForcePairCancellation

generatedOptimizationRegression :
  ∀ {Parameter}
    {model : Optimization.PhysicalSingletonCostModel Parameter} →
  (certificate : Optimization.GeneratedPhysicalSingletonCertificate model) →
  Optimization.reportedSingletonTotalCost certificate
  ≤ Optimization.singletonBudget
generatedOptimizationRegression =
  Optimization.singletonTotalBelowBudget

literalFieldIsNotRationalClaimRegression :
  Coefficients.literalSelectedField
  ≡ Coefficients.rationalSpecialisation → ⊥
literalFieldIsNotRationalClaimRegression =
  Coefficients.literalFieldIsNotRationalSpecialisation
