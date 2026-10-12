module DASHI.Analysis.CollatzSyracuseResidualFrontierStrictnessGuardValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.CollatzSyracuseResidualFrontierStrictnessGuardExact as Guard

boundedFrontierRejected :
  Guard.ResidualFrontierStrictnessBoundary.globallyBoundedFrontierRejected
    Guard.canonicalResidualFrontierStrictnessBoundary
  ≡ 1
boundedFrontierRejected = refl

finiteCoverageNotUnbounded :
  Guard.ResidualFrontierStrictnessBoundary.finiteCoverageCreatesUnboundedness
    Guard.canonicalResidualFrontierStrictnessBoundary
  ≡ 0
finiteCoverageNotUnbounded = refl
