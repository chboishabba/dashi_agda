module DASHI.Analysis.RiemannAristotleG2CurrentCutRegression where

open import DASHI.Core.Prelude
import DASHI.Analysis.RiemannAristotleG2CurrentCutExact as G2

g1Closed : G2.g1ThreeCoordinateToGenericGramClosed G2.canonicalAristotleG2CurrentCut ≡ true
g1Closed = refl

g2aClosed : G2.g2aOrderedPairGramDebtClosed G2.canonicalAristotleG2CurrentCut ≡ true
g2aClosed = refl

g2bClosed : G2.g2bRawThreeTaperBilinearCompilerClosed G2.canonicalAristotleG2CurrentCut ≡ true
g2bClosed = refl

checkedNormDetOwner : G2.checkedLeanNormDeterminantIdentityExists G2.canonicalAristotleG2CurrentCut ≡ true
checkedNormDetOwner = refl

g2cPolarizationClosed : G2.g2cPolarizationDerivationClosedInAgda G2.canonicalAristotleG2CurrentCut ≡ true
g2cPolarizationClosed = refl

g2cFreshLeanKernelReceiptPending : G2.g2cFreshLeanBilinearKernelReceiptPresent G2.canonicalAristotleG2CurrentCut ≡ false
g2cFreshLeanKernelReceiptPending = refl

reflectionOddChannelClosed : G2.reflectionPairOddSinhSinCancellationClosedInLean G2.canonicalAristotleG2CurrentCut ≡ true
reflectionOddChannelClosed = refl

reflectionOnlyCancellationRejected : G2.reflectionOnlyForcesRemainingGramCancellation G2.canonicalAristotleG2CurrentCut ≡ false
reflectionOnlyCancellationRejected = refl

g2dScalarized : G2.g2dReducedToSingleSignedScalarDeterminantSum G2.canonicalAristotleG2CurrentCut ≡ true
g2dScalarized = refl

g2dOrdinateCancellationOpen : G2.g2dAdditionalOrdinatePhaseCancellationBoundClosed G2.canonicalAristotleG2CurrentCut ≡ false
g2dOrdinateCancellationOpen = refl

noGenericGramSchurAlgebraLeft : G2.genericGramOrSchurAlgebraRemaining G2.canonicalAristotleG2CurrentCut ≡ false
noGenericGramSchurAlgebraLeft = refl

rhStillOpen : G2.rhDerived G2.canonicalAristotleG2CurrentCut ≡ false
rhStillOpen = refl
