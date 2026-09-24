module DASHI.Law.ExactNonFactorabilityResidualCompilerRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Law.ExactNonFactorabilityResidualCompilerExact as Residual

boundary : Residual.ExactNonFactorabilityResidualCompilerBoundary
boundary = Residual.canonicalExactNonFactorabilityResidualCompilerBoundary

retainsDefect :
  Residual.exactResidualRetainsQueryDefect boundary ≡ true
retainsDefect =
  Residual.exactResidualRetainsQueryDefectIsTrue boundary

axisRoutesExactly :
  Residual.lostAxisDeterministicallyChoosesResearchKind boundary ≡ true
axisRoutesExactly =
  Residual.lostAxisDeterministicallyChoosesResearchKindIsTrue boundary

approximateCannotPromote :
  Residual.approximateCollisionMayPromoteExactResidual boundary ≡ false
approximateCannotPromote =
  Residual.approximateCollisionMayPromoteExactResidualIsFalse boundary

residualCreatesNoAuthority :
  Residual.residualCreatesSemanticAuthority boundary ≡ false
residualCreatesNoAuthority =
  Residual.residualCreatesSemanticAuthorityIsFalse boundary
