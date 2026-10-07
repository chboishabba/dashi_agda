module DASHI.Cognition.Teleodynamics.TeleodynamicCovarianceRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Cognition.Teleodynamics.TeleodynamicCovarianceAdapterExact as Cov

existingSpectralGeometryOwnerReused :
  Cov.pnfSpectralGeometryOwnerReused Cov.canonicalTeleodynamicCovarianceBoundary ≡ true
existingSpectralGeometryOwnerReused = refl

covarianceIsNotNormalizedCorrelation :
  Cov.covarianceEqualsNormalizedCorrelation Cov.canonicalTeleodynamicCovarianceBoundary ≡ false
covarianceIsNotNormalizedCorrelation = refl

spectralGeometryDoesNotCreateConsciousness :
  Cov.spectrumEstablishesConsciousness Cov.canonicalTeleodynamicCovarianceBoundary ≡ false
spectralGeometryDoesNotCreateConsciousness = refl
