module DASHI.Economics.AICapitalOutcomeCompatibility20261016Validation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Economics.AICapitalOutcomeCompatibility20261016Exact as Fit

commoditisationHasCurrentSupport : Fit.supportedCoordinates Fit.commoditisationFit ≡ 4
commoditisationHasCurrentSupport = refl

refinancingStressHasCurrentSupport : Fit.supportedCoordinates Fit.refinancingStressFit ≡ 6
refinancingStressHasCurrentSupport = refl

policyMoatNotCurrentlySelected : Fit.fullSignaturePaid Fit.policyMoatFit ≡ false
policyMoatNotCurrentlySelected = refl

noTerminalRegimeSelected : Fit.anyTerminalRegimeSelected ≡ false
noTerminalRegimeSelected = refl
