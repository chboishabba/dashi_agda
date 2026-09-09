module DASHI.Physics.ExoticGravity.GravitationalWavePolarizationAndScopeValidationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.GR.GravitationalWavePolarizationSourceAttributionExact as Source
import DASHI.Physics.GR.GravitationalWavePolarizationSignBidiExact as Polarization
import DASHI.Physics.ExoticGravity.AntigravityNegativeGCouplingScopeBidiExact as Scope

------------------------------------------------------------------------
-- SOURCE ATTRIBUTION
------------------------------------------------------------------------

polarizationSourceHasPinnedDOI :
  Source.doiPinnedWhenAvailable
    Source.canonicalGravitationalWavePolarizationAttributionBoundary
    ≡ true
polarizationSourceHasPinnedDOI = refl

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
-- POLARIZATION BASIS / SIGN NON-COLLAPSE
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
