module DASHI.Physics.ExoticGravity.GravitationalWavePolarizationAndScopeValidationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.GR.GravitationalWavePolarizationSourceAttributionExact as Source
import DASHI.Physics.GR.GravitationalWavePolarizationSignBidiExact as Polarization
import DASHI.Physics.GR.GravitationalWavePhaseSignBidiExact as Phase
import DASHI.Physics.GR.NegativeGGravitationalWavePhaseIdentifiabilityBidiExact as PhaseIdent
import DASHI.Physics.GR.NegativeGGravitationalWavePhaseProofSearchExact as PhaseSearch
import DASHI.Physics.ExoticGravity.AntigravityNegativeGCouplingScopeBidiExact as Scope
import DASHI.Physics.ExoticGravity.AntigravityNegativeGCouplingScopeProofSearchExact as ScopeSearch
import DASHI.Physics.ExoticGravity.SuperconductingResidualCouplingNegativeGInterpretationBidiExact as Interpretation
import DASHI.Physics.ExoticGravity.SuperconductingConstitutiveNegativeGScopeWeldExact as ConstitutiveWeld
import DASHI.Physics.ExoticGravity.SuperconductingConstitutiveNegativeGProofSearchExact as ConstitutiveSearch
import DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGGravitationalWaveBidiExact as MaterialWave

------------------------------------------------------------------------
-- SOURCE ATTRIBUTION
------------------------------------------------------------------------

polarizationSourceHasPinnedDOI :
  Source.doiPinnedWhenAvailable
    Source.canonicalGravitationalWavePolarizationAttributionBoundary
    ≡ true
polarizationSourceHasPinnedDOI = refl

technicalCarrierIsNotLocalRepoArtifact :
  Source.externalTechnicalCarrierIsLocalRepoArtifact
    Source.canonicalGravitationalWavePolarizationAttributionBoundary
    ≡ false
technicalCarrierIsNotLocalRepoArtifact = refl

citationDoesNotImportDASHIBidiProof :
  Source.citationImportsDASHIBidiProof
    Source.canonicalGravitationalWavePolarizationAttributionBoundary
    ≡ false
citationDoesNotImportDASHIBidiProof = refl

sourceDoesNotCallPlusPositivePolarity :
  Source.plusLabelMeansPositivePolarityByCitation
    Source.canonicalGravitationalWavePolarizationAttributionBoundary
    ≡ false
sourceDoesNotCallPlusPositivePolarity = refl

sourceDoesNotCallCrossNegativePolarity :
  Source.crossLabelMeansNegativePolarityByCitation
    Source.canonicalGravitationalWavePolarizationAttributionBoundary
    ≡ false
sourceDoesNotCallCrossNegativePolarity = refl

------------------------------------------------------------------------
-- POLARIZATION BASIS / SIGN / PHASE NON-COLLAPSE
------------------------------------------------------------------------

plusDoesNotMeanPositivePolarity :
  Polarization.plusMeansPositivePolarity
    Polarization.canonicalGravitationalWavePolarizationSignBoundary
    ≡ false
plusDoesNotMeanPositivePolarity = refl

crossDoesNotMeanNegativePolarity :
  Polarization.crossMeansNegativePolarity
    Polarization.canonicalGravitationalWavePolarizationSignBoundary
    ≡ false
crossDoesNotMeanNegativePolarity = refl

eachBasisMayCarryEitherWaveformSign :
  Polarization.eachTensorBasisMayCarryEitherNonzeroWaveformSign
    Polarization.canonicalGravitationalWavePolarizationSignBoundary
    ≡ true
eachBasisMayCarryEitherWaveformSign = refl

waveformSignDoesNotDetermineBasis :
  Polarization.waveformSignDeterminesPolarizationBasis
    Polarization.canonicalGravitationalWavePolarizationSignBoundary
    ≡ false
waveformSignDoesNotDetermineBasis = refl

readoutSignDoesNotDetermineGSign :
  Polarization.detectorReadoutSignDeterminesCouplingSign
    Polarization.canonicalGravitationalWavePolarizationSignBoundary
    ≡ false
readoutSignDoesNotDetermineGSign = refl

basisCannotRecoverGSign :
  Polarization.couplingSignConsumer Polarization.plusPositiveGFixture
    ≡ Polarization.couplingSignConsumer Polarization.plusNegativeGFixture → ⊥
basisCannotRecoverGSign = Polarization.polarizationBasisCannotRecoverGSign

phaseIsSeparateCoordinate :
  Phase.phaseIsSeparateCoordinate
    Phase.canonicalGravitationalWavePhaseSignBoundary
    ≡ true
phaseIsSeparateCoordinate = refl

negativeWaveformSampleDoesNotMeanNegativeG :
  Phase.negativeWaveformSampleMeansNegativeG
    Phase.canonicalGravitationalWavePhaseSignBoundary
    ≡ false
negativeWaveformSampleDoesNotMeanNegativeG = refl

phaseSourceDoesNotProveDASHIInvolution :
  Phase.phaseCoordinateSourceReceiptProvesDASHIPhaseInvolution
    Phase.canonicalGravitationalWavePhaseSignBoundary
    ≡ false
phaseSourceDoesNotProveDASHIInvolution = refl

phaseFlipIsInvolutive :
  (sign : Polarization.WaveformAmplitudeSign) →
  Phase.phaseFlip (Phase.phaseFlip sign) ≡ sign
phaseFlipIsInvolutive = Phase.phaseFlipInvolutive

independentPhaseAnchorRequiredForNegativeGWaveSign :
  PhaseIdent.independentPhaseAnchorRequired
    PhaseIdent.canonicalNegativeGWavePhaseIdentifiabilityBoundary
    ≡ true
independentPhaseAnchorRequiredForNegativeGWaveSign = refl

waveformSignAloneDoesNotIdentifyNegativeG :
  PhaseIdent.negativeWaveformSignAloneIdentifiesNegativeG
    PhaseIdent.canonicalNegativeGWavePhaseIdentifiabilityBoundary
    ≡ false
waveformSignAloneDoesNotIdentifyNegativeG = refl

ligoPhaseSourceDoesNotProveDASHIPhaseCollision :
  PhaseIdent.ligoPhaseSourceProvesDASHICollisionTheorem
    PhaseIdent.canonicalNegativeGWavePhaseIdentifiabilityBoundary
    ≡ false
ligoPhaseSourceDoesNotProveDASHIPhaseCollision = refl

phaseSearchStartsWithIndependentAnchor :
  PhaseSearch.currentFirstNewResidualIsIndependentPhaseAnchor
    PhaseSearch.canonicalNegativeGWaveSignProofSearchBoundary
    ≡ true
phaseSearchStartsWithIndependentAnchor = refl

phaseAnchorAloneDoesNotCloseNegativeG :
  PhaseSearch.phaseAnchorAloneClosesNegativeG
    PhaseSearch.canonicalNegativeGWaveSignProofSearchBoundary
    ≡ false
phaseAnchorAloneDoesNotCloseNegativeG = refl

------------------------------------------------------------------------
-- UNIVERSAL G VERSUS MATERIAL-EFFECTIVE G
------------------------------------------------------------------------

localEffectiveNegativeGIsNotUniversalNegativeG :
  Scope.localNegativeEffectiveCouplingEqualsUniversalNegativeG
    Scope.canonicalNegativeGCouplingScopeBoundary
    ≡ false
localEffectiveNegativeGIsNotUniversalNegativeG = refl

materialChangeDoesNotChangeUniversalNewtonGAutomatically :
  Scope.materialRegimeChangeAutomaticallyChangesUniversalNewtonG
    Scope.canonicalNegativeGCouplingScopeBoundary
    ≡ false
materialChangeDoesNotChangeUniversalNewtonGAutomatically = refl

localRepulsionDoesNotDetermineScope :
  Scope.localRepulsiveObservationDeterminesCouplingScope
    Scope.canonicalNegativeGCouplingScopeBoundary
    ≡ false
localRepulsionDoesNotDetermineScope = refl

universalNegativeGNeedsCrossScaleConsistency :
  Scope.universalNegativeGRequiresCrossScaleConsistency
    Scope.canonicalNegativeGCouplingScopeBoundary
    ≡ true
universalNegativeGNeedsCrossScaleConsistency = refl

materialEffectiveNegativeGNeedsRegimeReplication :
  Scope.materialEffectiveNegativeGRequiresRegimeSpecificReplication
    Scope.canonicalNegativeGCouplingScopeBoundary
    ≡ true
materialEffectiveNegativeGNeedsRegimeReplication = refl

rejectingUniversalNegativeGDoesNotRejectMaterialEffectiveHypothesis :
  Scope.rejectionOfUniversalNegativeGRejectsMaterialEffectiveNegativeG
    Scope.canonicalNegativeGCouplingScopeBoundary
    ≡ false
rejectingUniversalNegativeGDoesNotRejectMaterialEffectiveHypothesis = refl

universalAndMaterialScopesHaveDifferentFirstSearchStage :
  ScopeSearch.universalAndMaterialScopesHaveSameFirstSearchStage
    ScopeSearch.canonicalNegativeGCouplingScopeProofSearchBoundary
    ≡ false
universalAndMaterialScopesHaveDifferentFirstSearchStage = refl

materialScopeStartsWithSameApparatusContrast :
  ScopeSearch.materialScopeStartsWithSameApparatusRegimeContrast
    ScopeSearch.canonicalNegativeGCouplingScopeProofSearchBoundary
    ≡ true
materialScopeStartsWithSameApparatusContrast = refl

------------------------------------------------------------------------
-- RESIDUAL COUPLING != MATERIAL-EFFECTIVE NEGATIVE G
------------------------------------------------------------------------

nonzeroAlphaDoesNotMeanNegativeEffectiveG :
  Interpretation.nonzeroAlphaAutomaticallyMeansNegativeEffectiveG
    Interpretation.canonicalResidualNegativeGInterpretationBoundary
    ≡ false
nonzeroAlphaDoesNotMeanNegativeEffectiveG = refl

reproducibleScalingDoesNotMeanNegativeEffectiveG :
  Interpretation.reproducibleScalingAutomaticallyMeansNegativeEffectiveG
    Interpretation.canonicalResidualNegativeGInterpretationBoundary
    ≡ false
reproducibleScalingDoesNotMeanNegativeEffectiveG = refl

constitutiveMappingRequiredForEffectiveG :
  Interpretation.explicitConstitutiveMappingRequired
    Interpretation.canonicalResidualNegativeGInterpretationBoundary
    ≡ true
constitutiveMappingRequiredForEffectiveG = refl

materialRegimeContrastStillRequiredForEffectiveG :
  Interpretation.materialRegimeContrastStillRequired
    Interpretation.canonicalResidualNegativeGInterpretationBoundary
    ≡ true
materialRegimeContrastStillRequiredForEffectiveG = refl

effectiveGInterpretationDoesNotProveUniversalNegativeG :
  Interpretation.effectiveGInterpretationAutomaticallyProvesUniversalNegativeG
    Interpretation.canonicalResidualNegativeGInterpretationBoundary
    ≡ false
effectiveGInterpretationDoesNotProveUniversalNegativeG = refl

negativeFieldRatioDoesNotMeanNegativeEffectiveG :
  ConstitutiveWeld.negativeTotalFieldRatioAutomaticallyMeansNegativeEffectiveG
    ConstitutiveWeld.canonicalConstitutiveNegativeGBoundary
    ≡ false
negativeFieldRatioDoesNotMeanNegativeEffectiveG = refl

fixedMeasuredSourceRequiredForConstitutiveNegativeG :
  ConstitutiveWeld.fixedMeasuredSourceRequired
    ConstitutiveWeld.canonicalConstitutiveNegativeGBoundary
    ≡ true
fixedMeasuredSourceRequiredForConstitutiveNegativeG = refl

coefficientSignReversalRequiredForConstitutiveNegativeG :
  ConstitutiveWeld.coefficientSignReversalRequired
    ConstitutiveWeld.canonicalConstitutiveNegativeGBoundary
    ≡ true
coefficientSignReversalRequiredForConstitutiveNegativeG = refl

internalConstitutiveWeldNeedsNoFreshCitation :
  ConstitutiveWeld.internalWeldNeedsFreshExternalCitation
    ConstitutiveWeld.canonicalConstitutiveNegativeGBoundary
    ≡ false
internalConstitutiveWeldNeedsNoFreshCitation = refl

constitutiveNegativeGSearchStartsAtSourceCurrent :
  ConstitutiveSearch.currentFirstStageIsSourceCurrent
    ConstitutiveSearch.canonicalConstitutiveNegativeGProofSearchBoundary
    ≡ true
constitutiveNegativeGSearchStartsAtSourceCurrent = refl

closedEnhancementSplitDoesNotMeanNegativeEffectiveG :
  ConstitutiveSearch.closedEnhancementSplitAutomaticallyMeansNegativeEffectiveG
    ConstitutiveSearch.canonicalConstitutiveNegativeGProofSearchBoundary
    ≡ false
closedEnhancementSplitDoesNotMeanNegativeEffectiveG = refl

------------------------------------------------------------------------
-- MATERIAL-EFFECTIVE G x GRAVITATIONAL WAVES
------------------------------------------------------------------------

materialEffectiveGDoesNotAutomaticallyChangeWaveGeneration :
  MaterialWave.materialEffectiveNegativeGAutomaticallyChangesWaveGeneration
    MaterialWave.canonicalMaterialEffectiveGWaveBoundary
    ≡ false
materialEffectiveGDoesNotAutomaticallyChangeWaveGeneration = refl

sourceToRadiativeMappingRequired :
  MaterialWave.explicitSourceToRadiativeMappingRequired
    MaterialWave.canonicalMaterialEffectiveGWaveBoundary
    ≡ true
sourceToRadiativeMappingRequired = refl

materialEffectiveGDoesNotAutomaticallyChangeVacuumPropagation :
  MaterialWave.materialEffectiveNegativeGAutomaticallyChangesVacuumPropagation
    MaterialWave.canonicalMaterialEffectiveGWaveBoundary
    ≡ false
materialEffectiveGDoesNotAutomaticallyChangeVacuumPropagation = refl

materialEffectiveGDoesNotChangePolarizationBasisAutomatically :
  MaterialWave.materialEffectiveNegativeGAutomaticallyChangesPolarizationBasis
    MaterialWave.canonicalMaterialEffectiveGWaveBoundary
    ≡ false
materialEffectiveGDoesNotChangePolarizationBasisAutomatically = refl

negativeWaveSampleDoesNotDetermineMaterialEffectiveCoupling :
  MaterialWave.negativeWaveformSampleDeterminesMaterialEffectiveCoupling
    MaterialWave.canonicalMaterialEffectiveGWaveBoundary
    ≡ false
negativeWaveSampleDoesNotDetermineMaterialEffectiveCoupling = refl
