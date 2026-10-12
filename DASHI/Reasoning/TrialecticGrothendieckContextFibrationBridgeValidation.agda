module DASHI.Reasoning.TrialecticGrothendieckContextFibrationBridgeValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.TrialecticGrothendieckContextFibrationBridgeExact as Bridge

boundary : Bridge.TrialecticGrothendieckContextFibrationBridgeBoundary
boundary = Bridge.canonicalTrialecticGrothendieckContextFibrationBridgeBoundary

projectionCategoryAdapterPaid :
  Bridge.projectionCategoryAdapterPaid boundary ≡ true
projectionCategoryAdapterPaid = refl

cellPresheafInstantiatesContextIndexedObservation :
  Bridge.cellPresheafInstantiatesContextIndexedObservation boundary ≡ true
cellPresheafInstantiatesContextIndexedObservation = refl

splitLiftExistenceReused :
  Bridge.splitLiftExistenceReused boundary ≡ true
splitLiftExistenceReused = refl

fullBenabouUniquenessStillOpen :
  Bridge.fullBenabouUniquenessPromoted boundary ≡ false
fullBenabouUniquenessStillOpen = refl
