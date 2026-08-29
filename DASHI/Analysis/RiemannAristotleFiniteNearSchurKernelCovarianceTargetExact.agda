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
-- three-coordinate vector k_sigma.
--
-- Backward consumer:
--
-- G2 needs only the signed finite covariance of POST-SCHUR cells
--
--   sum_{sigma != tau} <E k_sigma, E k_tau>.
--
-- Agda now owns two representation routes after this point:
--
--   (1) a fixed 3x3 Schur-matrix bilinear compiler;
--   (2) a stronger conditional one-dimensional determinant compiler.
--
-- The second route would identify
--
--   <E x,E y>
--     = det(n1,n2,x) det(n1,n2,y) / wedgeSq(n1,n2).
--
-- That bilinear determinant identity is NOT promoted here: the source evidence
-- currently establishes exact double Gram-Schmidt elimination and determinant
-- survival, but this return has not located a checked theorem with precisely
-- the bilinear identity. Once supplied, only the signed scalar determinant
-- covariance estimate remains.
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

    fixedMatrixCoordinateCompilerClosed : Bool
    fixedMatrixCoordinateCompilerClosedIsTrue :
      fixedMatrixCoordinateCompilerClosed ≡ true

    determinantScalarizationCompilerReady : Bool
    determinantScalarizationCompilerReadyIsTrue :
      determinantScalarizationCompilerReady ≡ true

    literalBilinearDeterminantIdentityOwned : Bool
    literalBilinearDeterminantIdentityOwnedIsFalse :
      literalBilinearDeterminantIdentityOwned ≡ false

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
    true refl
    true refl
    false refl
    false refl
    "G2 is now an explicit finite signed ordered-pair covariance. Each raw three-taper coordinate is source-owned by the reflection-pair cosine/cosh kernel, with the odd sinh*sin channel already cancelled. The fixed-matrix Schur-coordinate compiler is closed. A stronger one-dimensional determinant covariance compiler is also ready, but the exact Lean bilinear identity <E x,E y> = det(n1,n2,x) det(n1,n2,y) / wedgeSq(n1,n2) is not claimed without a checked source theorem. After that source identity, the only analytic leaf is the signed finite oscillatory determinant covariance bound."
