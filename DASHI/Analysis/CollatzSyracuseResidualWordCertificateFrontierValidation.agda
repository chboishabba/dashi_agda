module DASHI.Analysis.CollatzSyracuseResidualWordCertificateFrontierValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.CollatzSyracuseResidualWordCertificateFrontierExact as Frontier

certificateCoverageCompilerPaid :
  Frontier.ResidualWordCertificateFrontierBoundary.finiteCertificateCoverageCompilerPaid
    Frontier.canonicalResidualWordCertificateFrontierBoundary
  ≡ 1
certificateCoverageCompilerPaid = refl

unboundedFrontierStillRequired :
  Frontier.ResidualWordCertificateFrontierBoundary.unboundedResidualFrontierStillRequired
    Frontier.canonicalResidualWordCertificateFrontierBoundary
  ≡ 1
unboundedFrontierStillRequired = refl

finiteCoverageDoesNotCreateUnboundedness :
  Frontier.ResidualWordCertificateFrontierBoundary.finiteCoverageCreatesUnboundedFrontier
    Frontier.canonicalResidualWordCertificateFrontierBoundary
  ≡ 0
finiteCoverageDoesNotCreateUnboundedness = refl
