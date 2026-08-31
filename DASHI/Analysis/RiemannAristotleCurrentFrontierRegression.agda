module DASHI.Analysis.RiemannAristotleCurrentFrontierRegression where

open import DASHI.Core.Prelude
import DASHI.Analysis.RiemannAristotleCurrentFrontierExact as F

evenConeClosed :
  F.AristotleCurrentFrontier.universalEvenConeConstructionClosedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
evenConeClosed = refl

twoRadiusClosed :
  F.AristotleCurrentFrontier.twoRadiusOffLineDiscriminatorClosedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
twoRadiusClosed = refl

primeZero :
  F.AristotleCurrentFrontier.highOrdinatePrimeProjectiveDebtZeroInLean
    F.canonicalAristotleCurrentFrontier ≡ true
primeZero = refl

deterministicSchurKernelChecked :
  F.AristotleCurrentFrontier.deterministicProjectiveSchurKernelCheckedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
deterministicSchurKernelChecked = refl

explicitFarCutoffClosed :
  F.AristotleCurrentFrontier.explicitFarShellCutoffBoundClosedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
explicitFarCutoffClosed = refl

explicitFarDecayClosed :
  F.AristotleCurrentFrontier.explicitFarShellTendsToZeroClosedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
explicitFarDecayClosed = refl

finiteNearCarrierClosed :
  F.AristotleCurrentFrontier.finiteSignedNearCarrierClosedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
finiteNearCarrierClosed = refl

literalDoffCutoffClosed :
  F.AristotleCurrentFrontier.literalDoffCutoffCarrierClosedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
literalDoffCutoffClosed = refl

latestLeanBuildChecked :
  F.AristotleCurrentFrontier.latestLeanBridgeBuildKernelChecked
    F.canonicalAristotleCurrentFrontier ≡ true
latestLeanBuildChecked = refl

nearFarCompilerClosed :
  F.AristotleCurrentFrontier.nearFarShellCompositionCompilerClosedInAgda
    F.canonicalAristotleCurrentFrontier ≡ true
nearFarCompilerClosed = refl

allowanceCompilerClosed :
  F.AristotleCurrentFrontier.nearFarAllowanceCompilerClosedInAgda
    F.canonicalAristotleCurrentFrontier ≡ true
allowanceCompilerClosed = refl

finiteSchurPerturbationCompilerClosed :
  F.AristotleCurrentFrontier.finiteNearCoreSchurPerturbationCompilerClosedInAgda
    F.canonicalAristotleCurrentFrontier ≡ true
finiteSchurPerturbationCompilerClosed = refl

leanFormulaNotPromotedToAgdaProof :
  F.AristotleCurrentFrontier.explicitLeanTailFormulaTransportedAsAgdaProof
    F.canonicalAristotleCurrentFrontier ≡ false
leanFormulaNotPromotedToAgdaProof = refl

finiteNearSchurCancellationOpen :
  F.AristotleCurrentFrontier.finiteSignedNearSchurCancellationClosed
    F.canonicalAristotleCurrentFrontier ≡ false
finiteNearSchurCancellationOpen = refl

jointFiniteMarginOpen :
  F.AristotleCurrentFrontier.jointFiniteNearFarMarginClosed
    F.canonicalAristotleCurrentFrontier ≡ false
jointFiniteMarginOpen = refl

threeTaperConstructionOpen :
  F.AristotleCurrentFrontier.deterministicNuisanceThreeTaperConstructionClosed
    F.canonicalAristotleCurrentFrontier ≡ false
threeTaperConstructionOpen = refl

lowOrdinateOpen :
  F.AristotleCurrentFrontier.lowOrdinateComplementCertified
    F.canonicalAristotleCurrentFrontier ≡ false
lowOrdinateOpen = refl

rhOpen :
  F.AristotleCurrentFrontier.finalRHImplicationClosed
    F.canonicalAristotleCurrentFrontier ≡ false
rhOpen = refl
