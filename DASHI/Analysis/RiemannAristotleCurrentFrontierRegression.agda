module DASHI.Analysis.RiemannAristotleCurrentFrontierRegression where

open import DASHI.Core.Prelude
import DASHI.Analysis.RiemannAristotleCurrentFrontierExact as F

oneZeroClosed :
  F.AristotleCurrentFrontier.oneZeroEndpointClosedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
oneZeroClosed = refl

twoZeroClosed :
  F.AristotleCurrentFrontier.inhabitedTwoZeroThreeTaperClosedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
twoZeroClosed = refl

selectedDebtRetired :
  F.AristotleCurrentFrontier.selectedTwoZeroResidualDebtRequired
    F.canonicalAristotleCurrentFrontier ≡ false
selectedDebtRetired = refl

twoZeroUniversalWitnessesStillOpen :
  F.AristotleCurrentFrontier.twoZeroUniversalWitnessProductionClosed
    F.canonicalAristotleCurrentFrontier ≡ false
twoZeroUniversalWitnessesStillOpen = refl

universalEvenConePoleQuotientClosed :
  F.AristotleCurrentFrontier.universalEvenConePoleQuotientClosedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
universalEvenConePoleQuotientClosed = refl

highOrdinatePrimeExactlyZero :
  F.AristotleCurrentFrontier.highOrdinatePrimeVectorZeroClosedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
highOrdinatePrimeExactlyZero = refl

reflectionPairKernelImplemented :
  F.AristotleCurrentFrontier.reflectionPairKernelSourceImplementedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
reflectionPairKernelImplemented = refl

reflectionSymmetrizedCarrierImplemented :
  F.AristotleCurrentFrontier.reflectionSymmetrizedCarrierSourceImplementedInLean
    F.canonicalAristotleCurrentFrontier ≡ true
reflectionSymmetrizedCarrierImplemented = refl

newReflectionKernelReceiptStillPending :
  F.AristotleCurrentFrontier.newReflectionSourceMachineChecked
    F.canonicalAristotleCurrentFrontier ≡ false
newReflectionKernelReceiptStillPending = refl

signedReflectionTailStillOpen :
  F.AristotleCurrentFrontier.signedReflectionTailEstimateClosed
    F.canonicalAristotleCurrentFrontier ≡ false
signedReflectionTailStillOpen = refl

gammaPaymentStillOpen :
  F.AristotleCurrentFrontier.projectedGammaPaymentClosed
    F.canonicalAristotleCurrentFrontier ≡ false
gammaPaymentStillOpen = refl

lowOrdinateComplementStillOpen :
  F.AristotleCurrentFrontier.lowOrdinateComplementCertified
    F.canonicalAristotleCurrentFrontier ≡ false
lowOrdinateComplementStillOpen = refl

equalHeightDegeneracyStillVisible :
  F.AristotleCurrentFrontier.equalHeightDegeneracyRemoved
    F.canonicalAristotleCurrentFrontier ≡ false
equalHeightDegeneracyStillVisible = refl

rhStillOpen :
  F.AristotleCurrentFrontier.finalRHImplicationClosed
    F.canonicalAristotleCurrentFrontier ≡ false
rhStillOpen = refl
