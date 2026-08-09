module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound40MultiplierLocalityValidation where

------------------------------------------------------------------------
-- Cumulative Round Forty validation root.
--
-- Round 40 imports the complete Round-39 redundancy-safe KKT/Green lane and
-- adds the multiplier-locality and correlated-residual tranche:
--
-- * one canonical selected-variation sign convention;
-- * redundancy-invariant multiplier-defect pairing;
-- * exact restriction to the plaquette constraint collar;
-- * literal source/defect subset atoms and two-source Green contraction;
-- * pair-indexed Boolean/D4/orientation/collar ownership;
-- * Combes--Thomas for the multiplier Gram and complete KKT block constants;
-- * genuine two-sided finite KKT inversion from reduced coercivity;
-- * D4 covariance of Gram, pseudoinverse and Green pairing;
-- * generated physical owner optimization with a dual no-fit certificate;
-- * explicit selected-background coefficient-field authority;
-- * the terminal corrected-sign singleton and correlated-Wilson reducers.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound39PseudoinverseKKTValidation

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
