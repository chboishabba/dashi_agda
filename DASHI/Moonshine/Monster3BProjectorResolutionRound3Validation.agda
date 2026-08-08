module DASHI.Moonshine.Monster3BProjectorResolutionRound3Validation where

import DASHI.Moonshine.Monster3BHighestAlphaValidation
import DASHI.Moonshine.Monster3BModelProjectorResolutionExact as Resolution
import DASHI.Moonshine.Monster3BModelStoneVonNeumannRecognitionExact as Stone

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Fin.Base using (Fin)

import DASHI.Moonshine.Monster3BFiniteHeisenbergGeneratorsExact as H
import DASHI.Moonshine.Monster3BFiniteProjectorModelExact as Model
import DASHI.Moonshine.Monster3BFiniteWeightProjectorExact as Projector

modelResolutionHasCorrectDimension :
  Resolution.totalDimension Resolution.canonicalModelProjectorResolution
  ≡ 65610
modelResolutionHasCorrectDimension = refl

selectedProjectorOwnsEveryModelBasis :
  (position : H.X6) →
  (multiplicity : Fin 90) →
  Projector.weightProjectorCoefficient position
    (Model.zetaBasis position multiplicity)
  ≡ 1
selectedProjectorOwnsEveryModelBasis position multiplicity =
  Resolution.projectorCoefficientOnOwnWeight
    (Model.zetaBasis position multiplicity)

evaluationRoundTrip :
  (label : Model.TranslatedMultiplicityLabel) →
  Stone.inverse Stone.canonicalFiniteEvaluationIsomorphism
    (Stone.forward Stone.canonicalFiniteEvaluationIsomorphism label)
  ≡ label
evaluationRoundTrip = Stone.evaluationMapIsIsomorphism

allStandardTranslationsAreFixedPointFree :
  (axis : H.Axis6) →
  (basis : Model.ZetaModelBasis) →
  Model.translatedBasis axis basis ≡ basis →
  ⊥
allStandardTranslationsAreFixedPointFree =
  Stone.standardTranslationHasNoFixedModelBasis
