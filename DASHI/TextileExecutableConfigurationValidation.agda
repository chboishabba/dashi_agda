module DASHI.TextileExecutableConfigurationValidation where

open import DASHI.Core.Prelude

import DASHI.Combinatorics.TextileExecutableStrandConfigurationExact as Exec

adjacentYangBaxterRegression :
  ∀ {n i} →
  (window : Exec.TripleWindowAt n i) →
  Exec.executeYangBaxterLeft window ≡ Exec.executeYangBaxterRight window
adjacentYangBaxterRegression = Exec.adjacentTripleYangBaxterOnConfigurations

farCommutationRegression :
  ∀ {n} →
  (window : Exec.DistantWindow n) →
  Exec.executeFarLeftThenRight window ≡ Exec.executeFarRightThenLeft window
farCommutationRegression = Exec.distantGeneratorsCommuteOnConfigurations

executableBoundaryRegression : Exec.TextileExecutableConfigurationBoundary
executableBoundaryRegression = Exec.canonicalTextileExecutableConfigurationBoundary
