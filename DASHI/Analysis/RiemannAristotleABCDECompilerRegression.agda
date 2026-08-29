module DASHI.Analysis.RiemannAristotleABCDECompilerRegression where

open import DASHI.Core.Prelude
import DASHI.Analysis.RiemannAristotleABCDECompilerExact as C

identityCompilerClosed :
  C.ABCDECutsetStatus.postElim2IdentityCompilerClosed
    C.canonicalABCDECutsetStatus ≡ true
identityCompilerClosed = refl

zeroTailEstimateNotFabricated :
  C.ABCDECutsetStatus.signedProjectedZeroTailEstimateClosed
    C.canonicalABCDECutsetStatus ≡ false
zeroTailEstimateNotFabricated = refl

primeGammaPaymentNotFabricated :
  C.ABCDECutsetStatus.projectedPrimeGammaPaymentClosed
    C.canonicalABCDECutsetStatus ≡ false
primeGammaPaymentNotFabricated = refl

marginCompilerClosed :
  C.ABCDECutsetStatus.farTailMarginCompilerClosed
    C.canonicalABCDECutsetStatus ≡ true
marginCompilerClosed = refl

finalLogicalCompilerClosed :
  C.ABCDECutsetStatus.finalNoOffLineToRHCompilerClosed
    C.canonicalABCDECutsetStatus ≡ true
finalLogicalCompilerClosed = refl

shortSupportCompatibilityStillOpen :
  C.ABCDECutsetStatus.shortSupportCompatibleThreeTaperFamilyOwned
    C.canonicalABCDECutsetStatus ≡ false
shortSupportCompatibilityStillOpen = refl

equalHeightRouteStillOpen :
  C.ABCDECutsetStatus.equalHeightClusterRouteClosed
    C.canonicalABCDECutsetStatus ≡ false
equalHeightRouteStillOpen = refl

rhStillNotDerived :
  C.ABCDECutsetStatus.rhDerived C.canonicalABCDECutsetStatus ≡ false
rhStillNotDerived = refl
