module DASHI.Analysis.RiemannAristotleCurrentFrontierRegression where

open import DASHI.Core.Prelude
import DASHI.Analysis.RiemannAristotleCurrentFrontierExact as F

universalEvenConeConstructionClosed :
  F.AristotleCurrentFrontier.universalEvenConeConstructionClosedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
universalEvenConeConstructionClosed = refl

twoRadiusDiscriminatorClosed :
  F.AristotleCurrentFrontier.twoRadiusOffLineDiscriminatorClosedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
twoRadiusDiscriminatorClosed = refl

primeProjectiveDebtZero :
  F.AristotleCurrentFrontier.highOrdinatePrimeProjectiveDebtZeroInLean
    F.canonicalAristotleCurrentFrontier ≡ true
primeProjectiveDebtZero = refl

targetLeadingCoefficientClosed :
  F.AristotleCurrentFrontier.targetLeadingCoefficientAndRemainderClosedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
targetLeadingCoefficientClosed = refl

reflectionPairKernelClosed :
  F.AristotleCurrentFrontier.reflectionPairKernelClosedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
reflectionPairKernelClosed = refl

reflectionFarTailConvergent :
  F.AristotleCurrentFrontier.reflectionFarTailAbsoluteConvergenceClosedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
reflectionFarTailConvergent = refl

uniformCurvatureClosed :
  F.AristotleCurrentFrontier.uniformReflectionCarrierCurvatureClosedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
uniformCurvatureClosed = refl

latestLeanBridgeKernelChecked :
  F.AristotleCurrentFrontier.latestLeanBridgeBuildKernelChecked
    F.canonicalAristotleCurrentFrontier ≡ true
latestLeanBridgeKernelChecked = refl

wholeCarrierStrictBudgetIsContradictionTarget :
  F.AristotleCurrentFrontier.wholePostSchurCarrierStrictBudgetIsContradictionTarget
    F.canonicalAristotleCurrentFrontier ≡ true
wholeCarrierStrictBudgetIsContradictionTarget = refl

eliminationAlgebraDoesNotCloseStrictBudget :
  F.AristotleCurrentFrontier.eliminationAlgebraAloneClosesStrictBudget
    F.canonicalAristotleCurrentFrontier ≡ false
eliminationAlgebraDoesNotCloseStrictBudget = refl

deterministicThreeTaperConstructionOpen :
  F.AristotleCurrentFrontier.deterministicNuisanceThreeTaperConstructionClosed
    F.canonicalAristotleCurrentFrontier ≡ false
deterministicThreeTaperConstructionOpen = refl

strictSignedWholeOffCarrierCancellationOpen :
  F.AristotleCurrentFrontier.strictSignedWholeOffCarrierCancellationClosed
    F.canonicalAristotleCurrentFrontier ≡ false
strictSignedWholeOffCarrierCancellationOpen = refl

lowOrdinateComplementOpen :
  F.AristotleCurrentFrontier.lowOrdinateComplementCertified
    F.canonicalAristotleCurrentFrontier ≡ false
lowOrdinateComplementOpen = refl

rhStillOpen :
  F.AristotleCurrentFrontier.finalRHImplicationClosed
    F.canonicalAristotleCurrentFrontier ≡ false
rhStillOpen = refl
