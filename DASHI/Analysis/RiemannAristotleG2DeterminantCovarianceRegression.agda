module DASHI.Analysis.RiemannAristotleG2DeterminantCovarianceRegression where

open import DASHI.Core.Prelude
import DASHI.Analysis.RiemannAristotleCurrentFrontierExact as F
import DASHI.Analysis.RiemannAristotleDeterminantCovarianceCompilerExact as D

determinantCompilerClosed :
  F.AristotleCurrentFrontier.determinantScalarizationCompilerClosedInAgda
    F.canonicalAristotleCurrentFrontier ≡ true
determinantCompilerClosed = refl

literalLeanBilinearDeterminantIdentityStillOpen :
  F.AristotleCurrentFrontier.literalLeanBilinearDeterminantIdentitySupplied
    F.canonicalAristotleCurrentFrontier ≡ false
literalLeanBilinearDeterminantIdentityStillOpen = refl

signedRHGramDebtStillOpen :
  F.AristotleCurrentFrontier.signedRHGramDebtEstimateClosed
    F.canonicalAristotleCurrentFrontier ≡ false
signedRHGramDebtStillOpen = refl

compilerBoundaryClosed :
  D.DeterminantCovarianceBoundary.determinantScalarizationCompilerClosedInAgda
    D.canonicalDeterminantCovarianceBoundary ≡ true
compilerBoundaryClosed = refl

sourceIdentityNotPromoted :
  D.DeterminantCovarianceBoundary.literalLeanBilinearDeterminantIdentitySupplied
    D.canonicalDeterminantCovarianceBoundary ≡ false
sourceIdentityNotPromoted = refl

analyticCovarianceStillOpen :
  D.DeterminantCovarianceBoundary.finiteSignedDeterminantCovarianceEstimateClosed
    D.canonicalDeterminantCovarianceBoundary ≡ false
analyticCovarianceStillOpen = refl
