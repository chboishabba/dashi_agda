module DASHI.Analysis.CollatzSyracuseResidualInverseLimitObstructionValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.CollatzSyracuseResidualInverseLimitObstructionExact as Inverse

inverseLimitCarrierPaid :
  Inverse.ResidualInverseLimitBoundary.residualSurvivorTowerPaid
    Inverse.canonicalResidualInverseLimitBoundary
  ≡ 1
inverseLimitCarrierPaid = refl

infiniteHistoryObstructionPaid :
  Inverse.ResidualInverseLimitBoundary.infiniteHistoryRefutesStrictDescentPaid
    Inverse.canonicalResidualInverseLimitBoundary
  ≡ 1
infiniteHistoryObstructionPaid = refl

absenceDoesNotConstructDescent :
  Inverse.ResidualInverseLimitBoundary.noInverseLimitAutomaticallyConstructsDescent
    Inverse.canonicalResidualInverseLimitBoundary
  ≡ 0
absenceDoesNotConstructDescent = refl
