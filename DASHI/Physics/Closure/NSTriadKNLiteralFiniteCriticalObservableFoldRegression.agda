module DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNLiteralFiniteCriticalObservableFoldExact as Fold

------------------------------------------------------------------------
-- RED-FIRST CONTRACT FOR THE STRICT S0 PHASE LEAF.
--
-- The production owner must construct the finite critical observables from the
-- live R240 trajectory itself.  In particular:
--
--   * endpoint critical mass is a literal finite weighted velocity fold;
--   * dissipation is the time integral of the corresponding 3/2-weight fold;
--   * nonlinear production is the time integral of the SAME finite weighted
--     real Hermitian pairing against Audit.projectedNonlinearity;
--   * R517 supplies the finite-carrier critical multiplier comparison;
--   * no R414 same-object/normalisation theorem is fabricated here.
------------------------------------------------------------------------

literalCriticalEndpointFoldIsConstructed :
  Fold.literalCriticalEndpointFoldConstructed ≡ true
literalCriticalEndpointFoldIsConstructed =
  Fold.literalCriticalEndpointFoldConstructedIsTrue

literalCriticalDissipationFoldIsConstructed :
  Fold.literalCriticalDissipationFoldConstructed ≡ true
literalCriticalDissipationFoldIsConstructed =
  Fold.literalCriticalDissipationFoldConstructedIsTrue

literalProjectedNonlinearProductionFoldIsConstructed :
  Fold.literalProjectedNonlinearProductionFoldConstructed ≡ true
literalProjectedNonlinearProductionFoldIsConstructed =
  Fold.literalProjectedNonlinearProductionFoldConstructedIsTrue

r517CriticalMultiplierComparisonIsReused :
  Fold.r517CriticalMultiplierComparisonReused ≡ true
r517CriticalMultiplierComparisonIsReused =
  Fold.r517CriticalMultiplierComparisonReusedIsTrue

productionIsNotDefinedByEnergyResidual :
  Fold.productionDefinedByEnergyResidual ≡ false
productionIsNotDefinedByEnergyResidual =
  Fold.productionDefinedByEnergyResidualIsFalse

r414ProductionNormalisationStillRequiresProof :
  Fold.r414ProductionNormalisationRecovered ≡ false
r414ProductionNormalisationStillRequiresProof =
  Fold.r414ProductionNormalisationRecoveredIsFalse

r414FullSliceStillRequiresS1S4 :
  Fold.r414FullPhysicalSliceConstructed ≡ false
r414FullSliceStillRequiresS1S4 =
  Fold.r414FullPhysicalSliceConstructedIsFalse
