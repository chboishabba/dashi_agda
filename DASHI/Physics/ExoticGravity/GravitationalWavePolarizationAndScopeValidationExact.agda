module DASHI.Physics.ExoticGravity.GravitationalWavePolarizationAndScopeValidationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.GR.GravitationalWavePolarizationSourceAttributionExact as Source
import DASHI.Physics.GR.GravitationalWavePolarizationSignBidiExact as Polarization
import DASHI.Physics.GR.GravitationalWavePhaseSignBidiExact as Phase
import DASHI.Physics.ExoticGravity.AntigravityNegativeGCouplingScopeBidiExact as Scope
import DASHI.Physics.ExoticGravity.AntigravityNegativeGCouplingScopeProofSearchExact as ScopeSearch

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
