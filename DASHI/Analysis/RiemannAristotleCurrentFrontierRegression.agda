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

gammaQuadraticEnvelopeClosed :
  F.AristotleCurrentFrontier.gammaProjectiveQuadraticEnvelopeClosedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
gammaQuadraticEnvelopeClosed = refl

poleQuadraticEnvelopeClosed :
  F.AristotleCurrentFrontier.poleProjectiveQuadraticEnvelopeClosedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
poleQuadraticEnvelopeClosed = refl

targetLeadingCoefficientClosed :
  F.AristotleCurrentFrontier.targetLeadingCoefficientAndRemainderClosedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
targetLeadingCoefficientClosed = refl

conditionalThreeTaperClosed :
  F.AristotleCurrentFrontier.conditionalTwoZeroThreeTaperClosedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
conditionalThreeTaperClosed = refl

conditionalThreeTaperNotUniversal :
  F.AristotleCurrentFrontier.conditionalTwoZeroIsUniversalRHBridge
    F.canonicalAristotleCurrentFrontier ≡ false
conditionalThreeTaperNotUniversal = refl

reflectionPairKernelImplemented :
  F.AristotleCurrentFrontier.reflectionPairKernelSourceImplementedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
reflectionPairKernelImplemented = refl

reflectionProjectiveCarrierImplemented :
  F.AristotleCurrentFrontier.reflectionSymmetrizedProjectiveCarrierSourceImplementedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
reflectionProjectiveCarrierImplemented = refl

deterministicSchurCompilerImplemented :
  F.AristotleCurrentFrontier.deterministicProjectiveSchurCompilerSourceImplementedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
deterministicSchurCompilerImplemented = refl

newBidiLeanReceiptPending :
  F.AristotleCurrentFrontier.newBidiLeanSourceMachineChecked
    F.canonicalAristotleCurrentFrontier ≡ false
newBidiLeanReceiptPending = refl

deterministicThreeTaperConstructionOpen :
  F.AristotleCurrentFrontier.deterministicNuisanceThreeTaperConstructionClosed
    F.canonicalAristotleCurrentFrontier ≡ false
deterministicThreeTaperConstructionOpen = refl

signedPostSchurTailOpen :
  F.AristotleCurrentFrontier.signedPostSchurOffOrdinateEstimateClosed
    F.canonicalAristotleCurrentFrontier ≡ false
signedPostSchurTailOpen = refl

lowOrdinateComplementOpen :
  F.AristotleCurrentFrontier.lowOrdinateComplementCertified
    F.canonicalAristotleCurrentFrontier ≡ false
lowOrdinateComplementOpen = refl

rhStillOpen :
  F.AristotleCurrentFrontier.finalRHImplicationClosed
    F.canonicalAristotleCurrentFrontier ≡ false
rhStillOpen = refl
