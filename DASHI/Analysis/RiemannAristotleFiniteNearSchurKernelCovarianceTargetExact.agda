module DASHI.Analysis.RiemannAristotleFiniteNearSchurKernelCovarianceTargetExact where

------------------------------------------------------------------------
-- G2 BIDI TARGET: POST-SCHUR COVARIANCE IN REFLECTION-PAIRED KERNEL COORDINATES
--
-- Forward source:
--
-- LiteralWeilOffOrdinateReflectionPair.lean owns, for every taper g_m,
--
--   K_m(a,delta;u) + K_m(-a,delta;u)
--     = 4 g_m(u) cosh(a u) cos(delta u).
--
-- Hence one raw finite near zero/reflection-pair contribution is a real
-- three-coordinate vector
--
--   k_sigma = (k_0(sigma), k_1(sigma), k_2(sigma)).
--
-- Backward consumer:
--
-- G2 now needs only the signed finite covariance of the POST-SCHUR cells
--
--   sum_{sigma != tau} <E k_sigma, E k_tau>.
--
-- The important seam is E: the deterministic two-nuisance Schur map is fixed
-- and linear on the three-taper response space.  We must not silently replace
-- E k_sigma by k_sigma.  This module therefore records the exact research
-- target after all generic Gram algebra has been compiled away.
--
-- A future source-native producer may express E by its literal 3x3 coefficients
-- and expand <E k_sigma,E k_tau> = k_sigma^T (E^T E) k_tau.  No positivity or
-- absolute majorant is assumed here.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record FiniteNearSchurKernelCovarianceTarget : Set where
  constructor finite-near-schur-kernel-covariance-target
  field
    reflectionPairLeanOwner : String
    reflectionPairLeanTheorem : String

    rawPairKernelFormulaOwnedInLean : Bool
    rawPairKernelFormulaOwnedInLeanIsTrue :
      rawPairKernelFormulaOwnedInLean ≡ true

    oddSinhSinChannelCancelledBeforeCovariance : Bool
    oddSinhSinChannelCancelledBeforeCovarianceIsTrue :
      oddSinhSinChannelCancelledBeforeCovariance ≡ true

    finiteGramDebtExpandedToOrderedPairsInAgda : Bool
    finiteGramDebtExpandedToOrderedPairsInAgdaIsTrue :
      finiteGramDebtExpandedToOrderedPairsInAgda ≡ true

    postSchurMapMustRemainExplicit : Bool
    postSchurMapMustRemainExplicitIsTrue :
      postSchurMapMustRemainExplicit ≡ true

    replacePostSchurCellByRawKernelCellAllowed : Bool
    replacePostSchurCellByRawKernelCellAllowedIsFalse :
      replacePostSchurCellByRawKernelCellAllowed ≡ false

    literalSchurKernelCoordinateExpansionClosed : Bool
    literalSchurKernelCoordinateExpansionClosedIsFalse :
      literalSchurKernelCoordinateExpansionClosed ≡ false

    signedFiniteSchurKernelCovarianceEstimateClosed : Bool
    signedFiniteSchurKernelCovarianceEstimateClosedIsFalse :
      signedFiniteSchurKernelCovarianceEstimateClosed ≡ false

    boundedReading : String

open FiniteNearSchurKernelCovarianceTarget public

canonicalFiniteNearSchurKernelCovarianceTarget :
  FiniteNearSchurKernelCovarianceTarget
canonicalFiniteNearSchurKernelCovarianceTarget =
  finite-near-schur-kernel-covariance-target
    "LiteralWeilOffOrdinateReflectionPair.lean"
    "LiteralWeilOffOrdinateReflectionPair.zeroConeValue_add_reflect_eq_integral"
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    "G2 has been reduced to a finite signed ordered-pair covariance. Each raw three-taper coordinate is source-owned by the reflection-pair cosine/cosh kernel, with the odd sinh*sin channel already cancelled. The remaining representation seam is the fixed deterministic Schur map E: one must expand <E k_sigma,E k_tau> in the literal kernel coordinates (equivalently via E^T E) before proving the signed finite covariance upper bound. No absolute W(t) route and no replacement E=identity is admitted."
