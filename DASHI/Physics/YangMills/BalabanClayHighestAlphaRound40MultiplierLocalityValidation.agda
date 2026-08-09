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
-- * two-source Moore--Penrose Green contraction;
-- * pair-indexed Boolean/D4/orientation/collar ownership;
-- * Combes--Thomas for the multiplier Gram and complete KKT block constants;
-- * genuine two-sided finite KKT inversion from reduced coercivity;
-- * D4 covariance of Gram, pseudoinverse and Green pairing;
-- * generated physical owner optimization with a dual no-fit certificate;
-- * explicit selected-background coefficient-field authority;
-- * the terminal corrected-sign singleton lower-bound reducer.
------------------------------------------------------------------------

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound39PseudoinverseKKTValidation

import DASHI.Physics.YangMills.BalabanSelectedVariationSignConventionExact as Sign
import DASHI.Physics.YangMills.BalabanSelectedMultiplierPairingRedundancyInvariantExact as Redundancy
import DASHI.Physics.YangMills.BalabanSelectedConstraintCollarPairingExact as Collar
import DASHI.Physics.YangMills.BalabanSelectedMultiplierDefectGreenContractionExact as Green
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedGreenAtomOwnershipExact as Ownership
import DASHI.Physics.YangMills.BalabanSelectedConstraintGramCombesThomasExact as GramCT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTBlockCombesThomasConstantsExact as BlockCT
import DASHI.Physics.YangMills.BalabanP33FiniteKKTBlockInverseExact as BlockInverse
import DASHI.Physics.YangMills.BalabanP33ConstraintGramD4CovarianceExact as D4
import DASHI.Physics.YangMills.BalabanP33PhysicalSingletonBudgetOptimizationExact as Optimization
import DASHI.Physics.YangMills.BalabanSelectedBackgroundCoefficientFieldExact as Coefficients
import DASHI.Physics.YangMills.BalabanSelectedCorrelatedSingletonClosureExact as Closure

open import Agda.Builtin.Equality using (_≡_)
open import Data.Empty using (⊥)
open import Data.Rational.Base as ℚ using (ℚ; 0ℚ; _+_; _*_; -_; _≤_)

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

terminalCorrelatedSingletonRegression :
  ∀ data →
  - (DASHI.Physics.YangMills.BalabanSelectedBackgroundVariationSelectorExact.remainingSingletonCoefficient
      * Closure.charge data)
  ≤ Closure.singleton data
terminalCorrelatedSingletonRegression =
  Closure.selectedCorrelatedSingletonLower
