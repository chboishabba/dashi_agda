module DASHI.Biology.IBSResponsePredictorAtlasRegression where

open import DASHI.Core.Prelude using (⊥)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Biology.IBSResponsePredictorAtlasExact as Predictor

atlasRegression : Predictor.canonicalIBSResponsePredictorAtlas ≡ Predictor.canonicalIBSResponsePredictorAtlas
atlasRegression = refl

frontierRegression : Predictor.canonicalIBSResponsePredictionParetoFrontier ≡ Predictor.canonicalIBSResponsePredictionParetoFrontier
frontierRegression = refl

predictorNotMediatorRegression : Predictor.PredictorIsMediatorPermission → ⊥
predictorNotMediatorRegression = Predictor.predictorDoesNotBecomeMediator

internalModelNotClinicalClassifierRegression : Predictor.InternalPredictionIsValidatedClinicalClassifierPermission → ⊥
internalModelNotClinicalClassifierRegression = Predictor.internalPredictionDoesNotBecomeClinicalClassifier
