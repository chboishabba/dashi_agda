module DASHI.Analysis.CollatzSyracuseResidualSurvivorFrontierValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.CollatzSyracuseResidualSurvivorFrontierExact as Residual

residualFrontierCompilerPaid :
  Residual.ResidualSurvivorFrontierBoundary.residualFrontierCompilerPaid
    Residual.canonicalResidualSurvivorFrontierBoundary
  ≡ 1
residualFrontierCompilerPaid = refl

residualFrontierGrowthOpen :
  Residual.ResidualSurvivorFrontierBoundary.unboundedResidualFrontierProducerPaid
    Residual.canonicalResidualSurvivorFrontierBoundary
  ≡ 0
residualFrontierGrowthOpen = refl
