module DASHI.Reasoning.TrialecticC3GlobalNaturalityNoGoValidation where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Reasoning.TrialecticC3GlobalNaturalityNoGoExact as NoGo

boundary : NoGo.TrialecticC3GlobalNaturalityNoGoBoundary
boundary = NoGo.canonicalTrialecticC3GlobalNaturalityNoGoBoundary

participantANotEnoughForB : NoGo.participantANotSufficientForB boundary ≡ true
participantANotEnoughForB = refl

fullABEdgeRepairsB : NoGo.fullABEdgeSufficientForB boundary ≡ true
fullABEdgeRepairsB = refl

naiveGlobalC3NaturalityRejected : NoGo.naiveGlobalC3NaturalityPaid boundary ≡ false
naiveGlobalC3NaturalityRejected = refl

richerLocalContextRequired : NoGo.richerLocalContextRequired boundary ≡ true
richerLocalContextRequired = refl
