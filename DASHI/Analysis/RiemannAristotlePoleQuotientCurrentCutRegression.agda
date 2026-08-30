module DASHI.Analysis.RiemannAristotlePoleQuotientCurrentCutRegression where

open import DASHI.Core.Prelude
import DASHI.Analysis.RiemannAristotlePoleQuotientCurrentCutExact as F

rankTwoScalarizationChecked :
  F.rankTwoDeterminantScalarizationKernelCheckedInLean F.canonicalPoleQuotientCurrentCut ≡ true
rankTwoScalarizationChecked = refl

rankTwoFinalConsumerRejected :
  F.rankTwoStrictBalancedFinalConsumerAdmissible F.canonicalPoleQuotientCurrentCut ≡ false
rankTwoFinalConsumerRejected = refl

universalPoleQuotientReused :
  F.universalPoleQuotientReusedForFinalLane F.canonicalPoleQuotientCurrentCut ≡ true
universalPoleQuotientReused = refl

clusterPositiveOwned :
  F.sameOrdinateClusterStrictlyPositiveInLeanOwner F.canonicalPoleQuotientCurrentCut ≡ true
clusterPositiveOwned = refl

primeZeroOwned :
  F.highOrdinatePrimeVectorExactlyZeroInLeanOwner F.canonicalPoleQuotientCurrentCut ≡ true
primeZeroOwned = refl

gammaRetained :
  F.gammaRetainedInFinalComplement F.canonicalPoleQuotientCurrentCut ≡ true
gammaRetained = refl

complementCompilerClosed :
  F.poleQuotientComplementMarginCompilerClosedInAgda F.canonicalPoleQuotientCurrentCut ≡ true
complementCompilerClosed = refl

splitBudgetCompilerClosed :
  F.splitOffGammaBudgetCompilerClosedInAgda F.canonicalPoleQuotientCurrentCut ≡ true
splitBudgetCompilerClosed = refl

poleOffUsesSignedReflectionKernel :
  F.poleQuotientOffCarrierUsesSignedReflectionCosineKernel F.canonicalPoleQuotientCurrentCut ≡ true
poleOffUsesSignedReflectionKernel = refl

qTransportRejected :
  F.rankTwoDeterminantQTransportedToPoleQuotientCarrier F.canonicalPoleQuotientCurrentCut ≡ false
qTransportRejected = refl

poleOffSocketEncoded :
  F.poleQuotientOffOrdinateTargetSocketEncoded F.canonicalPoleQuotientCurrentCut ≡ true
poleOffSocketEncoded = refl

gammaSocketEncoded :
  F.poleQuotientGammaTargetSocketEncoded F.canonicalPoleQuotientCurrentCut ≡ true
gammaSocketEncoded = refl

clusterMarginSocketEncoded :
  F.poleQuotientClusterMarginTargetSocketEncoded F.canonicalPoleQuotientCurrentCut ≡ true
clusterMarginSocketEncoded = refl

poleOffBoundOpen :
  F.poleQuotientSignedOffOrdinateBoundClosed F.canonicalPoleQuotientCurrentCut ≡ false
poleOffBoundOpen = refl

gammaBudgetOpen :
  F.gammaResidualBudgetClosed F.canonicalPoleQuotientCurrentCut ≡ false
gammaBudgetOpen = refl

quantitativeMarginOpen :
  F.quantitativePoleQuotientClusterMarginClosed F.canonicalPoleQuotientCurrentCut ≡ false
quantitativeMarginOpen = refl

noGenericContradictionAlgebraLeft :
  F.genericContradictionAlgebraRemaining F.canonicalPoleQuotientCurrentCut ≡ false
noGenericContradictionAlgebraLeft = refl

lowOrdinateOpen :
  F.lowOrdinateComplementCertified F.canonicalPoleQuotientCurrentCut ≡ false
lowOrdinateOpen = refl

rhOpen :
  F.rhDerived F.canonicalPoleQuotientCurrentCut ≡ false
rhOpen = refl
