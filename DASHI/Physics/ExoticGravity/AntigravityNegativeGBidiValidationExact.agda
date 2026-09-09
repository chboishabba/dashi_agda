module DASHI.Physics.ExoticGravity.AntigravityNegativeGBidiValidationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.GR.SignedEinsteinCouplingBidiExact as SignedG
import DASHI.Physics.GR.SignedEinsteinCouplingSourceDegeneracyBidiExact as SignedSource
import DASHI.Physics.GR.SignedGRNormalizationBidiExact as Normalization
import DASHI.Physics.ExoticGravity.AntigravityNegativeGCouplingBidiExact as NegativeG
import DASHI.Physics.ExoticGravity.AntigravityNegativeGPairedComparatorExact as Paired
import DASHI.Physics.ExoticGravity.AntigravityNegativeGClaimComparisonWeldExact as ComparisonWeld

------------------------------------------------------------------------
-- SIGN ALGEBRA
------------------------------------------------------------------------

negativeGFlipIsInvolutive :
  SignedG.flipCouplingSign
    (SignedG.flipCouplingSign SignedG.negativeCoupling)
    ≡ SignedG.negativeCoupling
negativeGFlipIsInvolutive =
  SignedG.flipCouplingSignInvolutive SignedG.negativeCoupling

negativeGCouplingMapsToReversedSourceOrientation :
  SignedG.responseOrientation SignedG.negativeCoupling
    ≡ SignedG.reversedSourceOrientation
negativeGCouplingMapsToReversedSourceOrientation = refl

frozenSignFlipReversesDisplayedWeakFieldCorrections :
  SignedG.frozenSignFlipReversesDisplayedLeadingCorrections
    SignedG.canonicalSignedEinsteinCouplingBoundary
    ≡ true
frozenSignFlipReversesDisplayedWeakFieldCorrections = refl

frozenNegativeGIsNotSolvedNegativeGGR :
  SignedG.frozenSignProbeEqualsSelfConsistentNegativeGTheory
    SignedG.canonicalSignedEinsteinCouplingBoundary
    ≡ false
frozenNegativeGIsNotSolvedNegativeGGR = refl

negativeGDoesNotAutomaticallyPreserveBoundOrbitBackground :
  SignedG.negativeGAutomaticallyPreservesBoundOrbitBackground
    SignedG.canonicalSignedEinsteinCouplingBoundary
    ≡ false
negativeGDoesNotAutomaticallyPreserveBoundOrbitBackground = refl

selfConsistentNegativeGNeedsStabilityAnalysis :
  SignedG.selfConsistentNegativeGRequiresStabilityAnalysis
    SignedG.canonicalSignedEinsteinCouplingBoundary
    ≡ true
selfConsistentNegativeGNeedsStabilityAnalysis = refl

------------------------------------------------------------------------
-- GR NORMALIZATION BIDI
------------------------------------------------------------------------

constantSlotNameCannotDetermineGSign :
  Normalization.constantSlotNameDeterminesCouplingSign
    Normalization.canonicalSignedGRNormalizationBoundary
    ≡ false
constantSlotNameCannotDetermineGSign = refl

negativeGCounterfactualReusesNormalizationShape :
  Normalization.negativeGCounterfactualMayReuseExistingNormalizationShape
    Normalization.canonicalSignedGRNormalizationBoundary
    ≡ true
negativeGCounterfactualReusesNormalizationShape = refl

negativeGCounterfactualDoesNotOverwriteMeasuredG :
  Normalization.negativeGCounterfactualOverwritesMeasuredRegistryValue
    Normalization.canonicalSignedGRNormalizationBoundary
    ≡ false
negativeGCounterfactualDoesNotOverwriteMeasuredG = refl

negativeGCounterfactualIsNotMeasuredNegativeG :
  Normalization.negativeGCounterfactualEqualsMeasuredNegativeG
    Normalization.canonicalSignedGRNormalizationBoundary
    ≡ false
negativeGCounterfactualIsNotMeasuredNegativeG = refl

physicalAndCounterfactualBranchesShareGSlot :
  Normalization.constantSlotName Normalization.physicalPositiveGBranch
    ≡ Normalization.constantSlotName Normalization.counterfactualNegativeGBranch
physicalAndCounterfactualBranchesShareGSlot = Normalization.constantSlotCollision

physicalAndCounterfactualBranchSignsRemainDistinct :
  Normalization.branchSign Normalization.physicalPositiveGBranch
    ≡ Normalization.branchSign Normalization.counterfactualNegativeGBranch → ⊥
physicalAndCounterfactualBranchSignsRemainDistinct = Normalization.branchSignsDistinct

------------------------------------------------------------------------
-- COUPLING-SIGN / SOURCE-SIGN DEGENERACY
------------------------------------------------------------------------

negativeGPositiveSourceCollidesWithPositiveGNegativeSourceAtCoarseRHS :
  SignedSource.coarseEffectiveSource SignedSource.negativeGPositiveSource
    ≡ SignedSource.coarseEffectiveSource SignedSource.positiveGNegativeSource
negativeGPositiveSourceCollidesWithPositiveGNegativeSourceAtCoarseRHS =
  SignedSource.sourceSideSignCollision

coarseRHSSignCannotRecoverWhichCoordinateWasNegative :
  SignedSource.coarseRHSSignDeterminesWhetherCouplingOrSourceWasNegative
    SignedSource.canonicalSignedEinsteinSourceBoundary
    ≡ false
coarseRHSSignCannotRecoverWhichCoordinateWasNegative = refl

negativeGDoesNotFlipLambdaAutomatically :
  SignedSource.negativeGAutomaticallyFlipsCosmologicalConstant
    SignedSource.canonicalSignedEinsteinSourceBoundary
    ≡ false
negativeGDoesNotFlipLambdaAutomatically = refl

sameRHSSignDoesNotMeanSamePhysicalTheory :
  SignedSource.sameRHSSignImpliesSamePhysicalTheory
    SignedSource.canonicalSignedEinsteinSourceBoundary
    ≡ false
sameRHSSignDoesNotMeanSamePhysicalTheory = refl

------------------------------------------------------------------------
-- ANTIGRAVITY CLAIM ROUTING
------------------------------------------------------------------------

negativeGIsOnlyCounterfactualTheoryCoordinateHere :
  NegativeG.negativeGIsEstablishedPhysicalConstantSign
    NegativeG.canonicalNegativeGAntigravityBoundary
    ≡ false
negativeGIsOnlyCounterfactualTheoryCoordinateHere = refl

negativeGDirectlyTargetsFreeFallAndRemoteField :
  NegativeG.negativeGDirectlyTargetsFreeFallAndRemoteFieldClaims
    NegativeG.canonicalNegativeGAntigravityBoundary
    ≡ true
negativeGDirectlyTargetsFreeFallAndRemoteField = refl

negativeGDoesNotImplyAlteredInertialMass :
  NegativeG.negativeGAloneImpliesAlteredInertialMass
    NegativeG.canonicalNegativeGAntigravityBoundary
    ≡ false
negativeGDoesNotImplyAlteredInertialMass = refl

negativeGDoesNotImplyReactionlessPropulsion :
  NegativeG.negativeGAloneImpliesReactionlessPropulsion
    NegativeG.canonicalNegativeGAntigravityBoundary
    ≡ false
negativeGDoesNotImplyReactionlessPropulsion = refl

negativeGIsNotNegativeActiveSource :
  NegativeG.negativeGEqualsNegativeActiveSource
    NegativeG.canonicalNegativeGNegativeMassBoundary
    ≡ false
negativeGIsNotNegativeActiveSource = refl

------------------------------------------------------------------------
-- SAME-INPUT +G / -G COMPARATOR
------------------------------------------------------------------------

pairedComparatorRequiresNonGRNegativeGAlternative :
  Paired.negativeGAlternativeMustBeTypedNonGR
    Paired.canonicalSignedGPairedComparatorBoundary
    ≡ true
pairedComparatorRequiresNonGRNegativeGAlternative = refl

sameInputPairIsolatesCouplingSign :
  Paired.sameInputPairIsolatesCouplingSignBetterThanUnpairedComparison
    Paired.canonicalSignedGPairedComparatorBoundary
    ≡ true
sameInputPairIsolatesCouplingSign = refl

betterNegativeGFitDoesNotEstablishNegativeGPhysics :
  Paired.betterNegativeGFitAutomaticallyEstablishesNegativeGPhysics
    Paired.canonicalSignedGPairedComparatorBoundary
    ≡ false
betterNegativeGFitDoesNotEstablishNegativeGPhysics = refl

betterNegativeGFitDoesNotProveAntigravity :
  Paired.betterNegativeGFitAutomaticallyProvesAntigravity
    Paired.canonicalSignedGPairedComparatorBoundary
    ≡ false
betterNegativeGFitDoesNotProveAntigravity = refl

------------------------------------------------------------------------
-- EXACT NEGATIVE-G SLOT WELD INTO CLAIM COMPARISON
------------------------------------------------------------------------

genericModifiedSlotDoesNotMeanNegativeG :
  ComparisonWeld.genericModifiedGravitySlotAutomaticallyMeansNegativeG
    ComparisonWeld.canonicalNegativeGClaimComparisonBoundary
    ≡ false
genericModifiedSlotDoesNotMeanNegativeG = refl

positiveGOrdinarySlotIdentityRequired :
  ComparisonWeld.exactPositiveGOrdinarySlotIdentityRequired
    ComparisonWeld.canonicalNegativeGClaimComparisonBoundary
    ≡ true
positiveGOrdinarySlotIdentityRequired = refl

negativeGAlternativeSlotIdentityRequired :
  ComparisonWeld.exactNegativeGAlternativeSlotIdentityRequired
    ComparisonWeld.canonicalNegativeGClaimComparisonBoundary
    ≡ true
negativeGAlternativeSlotIdentityRequired = refl

negativeGComparisonCannotReuseUnrelatedModifiedPrediction :
  ComparisonWeld.negativeGComparisonMayReuseUnrelatedModifiedPrediction
    ComparisonWeld.canonicalNegativeGClaimComparisonBoundary
    ≡ false
negativeGComparisonCannotReuseUnrelatedModifiedPrediction = refl

negativeGComparisonStillDoesNotProveAntigravity :
  ComparisonWeld.negativeGComparisonAutomaticallyProvesAntigravity
    ComparisonWeld.canonicalNegativeGClaimComparisonBoundary
    ≡ false
negativeGComparisonStillDoesNotProveAntigravity = refl
