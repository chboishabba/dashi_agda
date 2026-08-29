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

wholeCarrierStrictBudgetRejected :
  F.AristotleCurrentFrontier.wholePostSchurCarrierStrictBudgetValid
    F.canonicalAristotleCurrentFrontier ≡ false
wholeCarrierStrictBudgetRejected = refl

targetRemainderSplitOpen :
  F.AristotleCurrentFrontier.literalTargetRemainderSplitClosed
    F.canonicalAristotleCurrentFrontier ≡ false
targetRemainderSplitOpen = refl

strictSignedRemainderCancellationOpen :
  F.AristotleCurrentFrontier.strictSignedRemainderCancellationClosed
    F.canonicalAristotleCurrentFrontier ≡ false
strictSignedRemainderCancellationOpen = refl

deterministicThreeTaperConstructionOpen :
  F.AristotleCurrentFrontier.deterministicNuisanceThreeTaperConstructionClosed
    F.canonicalAristotleCurrentFrontier ≡ false
deterministicThreeTaperConstructionOpen = refl

lowOrdinateComplementOpen :
  F.AristotleCurrentFrontier.lowOrdinateComplementCertified
    F.canonicalAristotleCurrentFrontier ≡ false
lowOrdinateComplementOpen = refl

rhStillOpen :
  F.AristotleCurrentFrontier.finalRHImplicationClosed
    F.canonicalAristotleCurrentFrontier ≡ false
rhStillOpen = refl
