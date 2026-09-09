module DASHI.Physics.ExoticGravity.AntigravityNegativeGBidiValidationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.GR.SignedEinsteinCouplingBidiExact as SignedG
import DASHI.Physics.GR.SignedEinsteinCouplingSourceDegeneracyBidiExact as SignedSource
import DASHI.Physics.GR.SignedGRNormalizationBidiExact as Normalization
import DASHI.Physics.GR.SignedNewtonianLimitBidiExact as Newton
import DASHI.Physics.GR.SignedGravitationalWaveCouplingBidiExact as SignedWave
import DASHI.Physics.GR.NegativeGGravitationalWaveTestRoutingExact as WaveRoute
import DASHI.Physics.GR.SignedCosmologicalMatterCouplingBidiExact as Cosmology
import DASHI.Physics.GR.UniversalSignedGCrossScaleFingerprintBidiExact as Universal
import DASHI.Physics.ExoticGravity.AntigravityNegativeGCouplingBidiExact as NegativeG
import DASHI.Physics.ExoticGravity.AntigravityNegativeGPairedComparatorExact as Paired
import DASHI.Physics.ExoticGravity.AntigravityNegativeGClaimComparisonWeldExact as ComparisonWeld
import DASHI.Physics.ExoticGravity.AntigravityNegativeGCrossScaleProofSearchExact as CrossScaleSearch

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
-- NEWTONIAN / POISSON SIGN FIBRE
------------------------------------------------------------------------

negativeGPositiveDensityIsRepulsive :
  Newton.positiveDensityRadialResponse SignedG.negativeCoupling
    ≡ Newton.repulsiveAwayFromPositiveSource
negativeGPositiveDensityIsRepulsive = refl

poissonSignCannotIdentifyNegativeCoordinate :
  Newton.poissonRHSSignDeterminesWhetherGOrDensityWasNegative
    Newton.canonicalSignedNewtonianLimitBoundary
    ≡ false
poissonSignCannotIdentifyNegativeCoordinate = refl

poissonNegativeGIsNotSolvedNegativeGLimit :
  Newton.frozenPoissonSignProbeEqualsSolvedNegativeGNewtonianLimit
    Newton.canonicalSignedNewtonianLimitBoundary
    ≡ false
poissonNegativeGIsNotSolvedNegativeGLimit = refl

exactPoissonReceiptRequired :
  Newton.exactExistingPoissonReceiptRequired
    Newton.canonicalSignedNewtonianLimitBoundary
    ≡ true
exactPoissonReceiptRequired = refl

------------------------------------------------------------------------
-- GRAVITATIONAL-WAVE GENERATION / PROPAGATION SPLIT
------------------------------------------------------------------------

vacuumPropagationDoesNotIdentifyGSign :
  SignedWave.vacuumPropagationObserverAloneDeterminesMatterCouplingSign
    SignedWave.canonicalSignedGravitationalWaveBoundary
    ≡ false
vacuumPropagationDoesNotIdentifyGSign = refl

waveSourceGenerationMayDependOnGSign :
  SignedWave.sourceGenerationMayDependOnCouplingSign
    SignedWave.canonicalSignedGravitationalWaveBoundary
    ≡ true
waveSourceGenerationMayDependOnGSign = refl

exactWaveEquationAndStrainReceiptsRequired :
  SignedWave.exactExistingWaveEquationAndStrainReceiptsRequired
    SignedWave.canonicalSignedGravitationalWaveBoundary
    ≡ true
exactWaveEquationAndStrainReceiptsRequired = refl

inspiralNegativeGNeedsReSolvedSourceDynamics :
  WaveRoute.negativeGRoleFor WaveRoute.WaveTest.inspiralPhaseConsistency
    ≡ WaveRoute.requiresReSolvedSourceDynamics
inspiralNegativeGNeedsReSolvedSourceDynamics = refl

dispersionAloneDoesNotIdentifyGSign :
  WaveRoute.negativeGRoleFor WaveRoute.WaveTest.dispersionPropagation
    ≡ WaveRoute.propagationAloneDoesNotIdentifyGSign
dispersionAloneDoesNotIdentifyGSign = refl

currentGWAgreementDoesNotRuleOutEveryNegativeGConstruction :
  WaveRoute.currentGWAgreementAutomaticallyRulesOutEveryNegativeGConstruction
    WaveRoute.canonicalNegativeGWaveTestBoundary
    ≡ false
currentGWAgreementDoesNotRuleOutEveryNegativeGConstruction = refl

------------------------------------------------------------------------
-- COSMOLOGICAL MATTER-TERM SIGN FIBRE
------------------------------------------------------------------------

cosmologicalMatterTermCannotIdentifyNegativeCoordinate :
  Cosmology.friedmannMatterTermSignAloneDeterminesWhetherGOrDensityWasNegative
    Cosmology.canonicalSignedCosmologyBoundary
    ≡ false
cosmologicalMatterTermCannotIdentifyNegativeCoordinate = refl

negativeGDoesNotAutomaticallyEqualLambda :
  Cosmology.negativeGAutomaticallyEqualsPositiveCosmologicalConstant
    Cosmology.canonicalSignedCosmologyBoundary
    ≡ false
negativeGDoesNotAutomaticallyEqualLambda = refl

negativeGDoesNotAutomaticallyExplainAcceleration :
  Cosmology.negativeGAutomaticallyExplainsAcceleratedExpansion
    Cosmology.canonicalSignedCosmologyBoundary
    ≡ false
negativeGDoesNotAutomaticallyExplainAcceleration = refl

negativeGCosmologyNeedsReSolvedDynamics :
  Cosmology.selfConsistentNegativeGCosmologyRequiresReSolvedDynamics
    Cosmology.canonicalSignedCosmologyBoundary
    ≡ true
negativeGCosmologyNeedsReSolvedDynamics = refl

------------------------------------------------------------------------
-- UNIVERSAL SIGNED-G CROSS-SCALE FINGERPRINT
------------------------------------------------------------------------

universalNegativeGFingerprintIsRepulsiveLocally :
  Universal.localPositiveDensityResponse Universal.negativeGSignFingerprint
    ≡ Newton.repulsiveAwayFromPositiveSource
universalNegativeGFingerprintIsRepulsiveLocally = refl

universalNegativeGFingerprintHasNegativeCosmologicalMatterTerm :
  Universal.cosmologicalPositiveDensityMatterTerm Universal.negativeGSignFingerprint
    ≡ Cosmology.negativeMatterContribution
universalNegativeGFingerprintHasNegativeCosmologicalMatterTerm = refl

localRepulsionDoesNotDetermineUniversalNegativeG :
  Universal.localRepulsiveObservationAutomaticallyMeansUniversalNegativeG
    Universal.canonicalUniversalSignedGCrossScaleBoundary
    ≡ false
localRepulsionDoesNotDetermineUniversalNegativeG = refl

universalNegativeGRequiresSameSignAcrossScales :
  Universal.universalNegativeGRequiresSameSignAcrossScales
    Universal.canonicalUniversalSignedGCrossScaleBoundary
    ≡ true
universalNegativeGRequiresSameSignAcrossScales = refl

vacuumGWPropagationDoesNotPayUniversalSignIdentity :
  Universal.vacuumGWPropagationAlonePaysUniversalSignIdentity
    Universal.canonicalUniversalSignedGCrossScaleBoundary
    ≡ false
vacuumGWPropagationDoesNotPayUniversalSignIdentity = refl

------------------------------------------------------------------------
-- UNIVERSAL NEGATIVE-G PROOF SEARCH
------------------------------------------------------------------------

universalNegativeGSearchStartsLocal :
  CrossScaleSearch.firstUniversalNegativeGStage
    ≡ CrossScaleSearch.localSignDiscriminatorStage
universalNegativeGSearchStartsLocal = refl

localRepulsiveAnomalyDoesNotPayUniversalNegativeG :
  CrossScaleSearch.localRepulsiveAnomalyPaysUniversalNegativeG
    CrossScaleSearch.canonicalNegativeGCrossScaleProofSearchBoundary
    ≡ false
localRepulsiveAnomalyDoesNotPayUniversalNegativeG = refl

positiveDensityAttractionCanDiscriminateFrozenNegativeG :
  CrossScaleSearch.positiveDensityAttractionCanDiscriminateFrozenNegativeGSign
    CrossScaleSearch.canonicalNegativeGCrossScaleProofSearchBoundary
    ≡ true
positiveDensityAttractionCanDiscriminateFrozenNegativeG = refl

rejectionOfUniversalNegativeGDoesNotRejectEveryLocalEffectiveModel :
  CrossScaleSearch.rejectionOfUniversalNegativeGRejectsEveryLocalEffectiveRepulsionModel
    CrossScaleSearch.canonicalNegativeGCrossScaleProofSearchBoundary
    ≡ false
rejectionOfUniversalNegativeGDoesNotRejectEveryLocalEffectiveModel = refl

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
