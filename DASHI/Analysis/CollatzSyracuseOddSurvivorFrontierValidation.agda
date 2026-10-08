module DASHI.Analysis.CollatzSyracuseOddSurvivorFrontierValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.CollatzSyracuseOddSurvivorFrontierExact as Frontier

oddFrontierCompilerOwned :
  Frontier.OddSurvivorFrontierBoundary.oddFrontierCompilerPaid
    Frontier.canonicalOddSurvivorFrontierBoundary
  ≡ 1
oddFrontierCompilerOwned = refl

unboundedOddFrontierStillOpen :
  Frontier.OddSurvivorFrontierBoundary.unboundedOddFrontierProducerPaid
    Frontier.canonicalOddSurvivorFrontierBoundary
  ≡ 0
unboundedOddFrontierStillOpen = refl
