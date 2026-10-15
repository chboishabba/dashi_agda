module DASHI.Physics.Closure.MonsterC3UniformCountingEnsembleValidation where

open import DASHI.Core.Prelude
import DASHI.Physics.Closure.MonsterC3UniformCountingEnsembleExact as Ensemble

fineCountIs196883 :
  Ensemble.UniformNormalization.stateCount Ensemble.fineUniformNormalization
  ≡ 196883
fineCountIs196883 = refl

fineWeightNumeratorIsOne :
  Ensemble.UniformNormalization.weightNumerator Ensemble.fineUniformNormalization
  ≡ 1
fineWeightNumeratorIsOne = refl

fineWeightDenominatorIs196883 :
  Ensemble.UniformNormalization.weightDenominator Ensemble.fineUniformNormalization
  ≡ 196883
fineWeightDenominatorIs196883 = refl

coarseCountIs53 :
  Ensemble.UniformNormalization.stateCount Ensemble.coarseUniformNormalization
  ≡ 53
coarseCountIs53 = refl

mathematicalNormalisationPaid :
  Ensemble.CountingEnsembleBoundary.normalizedFiniteCountingWeightsPaid
    Ensemble.canonicalCountingEnsembleBoundary
  ≡ true
mathematicalNormalisationPaid = refl

sameObjectMonsterIdentificationUnpaid :
  Ensemble.CountingEnsembleBoundary.finCarrierIdentifiedWithLiteralMonsterStates
    Ensemble.canonicalCountingEnsembleBoundary
  ≡ false
sameObjectMonsterIdentificationUnpaid = refl

physicalEntropyIdentificationUnpaid :
  Ensemble.CountingEnsembleBoundary.uniformCountingMeasureIsPhysicalThermalEnsemble
    Ensemble.canonicalCountingEnsembleBoundary
  ≡ false
physicalEntropyIdentificationUnpaid = refl
