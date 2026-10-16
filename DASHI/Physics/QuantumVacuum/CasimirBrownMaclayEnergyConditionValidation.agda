module DASHI.Physics.QuantumVacuum.CasimirBrownMaclayEnergyConditionValidation where

open import DASHI.Core.Prelude
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _/_; _*_; -_)

import DASHI.Physics.QuantumVacuum.CasimirBrownMaclayEnergyConditionExact as CasimirEC
import DASHI.Physics.QuantumVacuum.CasimirSO3StressContractionMaxCutExact as Stress
import DASHI.Physics.Closure.SU2SO3369HypervoxelBridge as SO3

------------------------------------------------------------------------
-- RED-first regression surface for the literal normalized Brown-Maclay
-- spatial stress owner and the local Casimir energy-condition fingerprint.
------------------------------------------------------------------------

normalPressureRegression :
  Stress.normalPressure CasimirEC.brownMaclayNormalizedSpatialStress
  ≡ - (Int.+ 3 / 1)
normalPressureRegression = CasimirEC.normalPressureIsMinusThree

tangentOnePressureRegression :
  CasimirEC.brownMaclayNormalizedSpatialStress
    (Stress.plateTangentOneAxis , Stress.plateTangentOneAxis)
  ≡ 1ℚ
tangentOnePressureRegression = CasimirEC.tangentOnePressureIsPlusOne

tangentTwoPressureRegression :
  CasimirEC.brownMaclayNormalizedSpatialStress
    (Stress.plateTangentTwoAxis , Stress.plateTangentTwoAxis)
  ≡ 1ℚ
tangentTwoPressureRegression = CasimirEC.tangentTwoPressureIsPlusOne

offDiagonalNormalTractionOneRegression :
  Stress.tractionAgainstPlateNormal
    CasimirEC.brownMaclayNormalizedSpatialStress
    Stress.plateTangentOneAxis
  ≡ 0ℚ
offDiagonalNormalTractionOneRegression =
  CasimirEC.tangentOneNormalTractionVanishes

offDiagonalNormalTractionTwoRegression :
  Stress.tractionAgainstPlateNormal
    CasimirEC.brownMaclayNormalizedSpatialStress
    Stress.plateTangentTwoAxis
  ≡ 0ℚ
offDiagonalNormalTractionTwoRegression =
  CasimirEC.tangentTwoNormalTractionVanishes

energyDensityRegression :
  CasimirEC.normalizedEnergyDensity ≡ - 1ℚ
energyDensityRegression = refl

tangentNullSaturatesRegression :
  CasimirEC.tangentNullCombination ≡ 0ℚ
tangentNullSaturatesRegression = CasimirEC.tangentNullCombinationIsZero

normalNullViolatesRegression :
  CasimirEC.normalNullCombination ≡ - (Int.+ 4 / 1)
normalNullViolatesRegression = CasimirEC.normalNullCombinationIsNegativeFour

activeStressRegression :
  CasimirEC.activeStressCombination ≡ - (Int.+ 2 / 1)
activeStressRegression = CasimirEC.activeStressCombinationIsNegativeTwo

lorentzTraceRegression :
  CasimirEC.lorentzTraceCombination ≡ 0ℚ
lorentzTraceRegression = CasimirEC.lorentzTraceCombinationIsZero

arbitraryNullDirectionRegression :
  (normalWeight : ℚ) →
  CasimirEC.normalizedNullContractionFromNormalWeight normalWeight
  ≡ - ((Int.+ 4 / 1) * normalWeight)
arbitraryNullDirectionRegression =
  CasimirEC.nullContractionIsNegativeFourTimesNormalWeight

necDirectionRegression :
  CasimirEC.directionalNEC Stress.normal
  ≡ CasimirEC.conditionViolated
necDirectionRegression = refl

necTangentRegression :
  CasimirEC.directionalNEC Stress.tangentOne
  ≡ CasimirEC.conditionSaturated
necTangentRegression = refl

wecRegression :
  CasimirEC.casimirWEC ≡ CasimirEC.conditionViolated
wecRegression = refl

secRegression :
  CasimirEC.casimirSEC ≡ CasimirEC.conditionViolated
secRegression = refl

decRegression :
  CasimirEC.casimirDEC ≡ CasimirEC.conditionViolated
decRegression = refl

sourceCitationNonPromotionRegression :
  CasimirEC.BrownMaclayCitationAutomaticallyConstructsSameObjectStress → ⊥
sourceCitationNonPromotionRegression =
  CasimirEC.brownMaclayCitationDoesNotConstructSameObjectStress

casimirForceIsNotGravityMeasurementRegression :
  CasimirEC.CasimirStressAutomaticallyMeasuresGRBackreaction → ⊥
casimirForceIsNotGravityMeasurementRegression =
  CasimirEC.casimirStressDoesNotMeasureGRBackreaction
