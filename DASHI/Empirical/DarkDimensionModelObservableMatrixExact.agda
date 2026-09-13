module DASHI.Empirical.DarkDimensionModelObservableMatrixExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Empirical.DarkDimensionQuantitativeEnvelopeExact as Quantitative
import DASHI.Physics.Units.SI as SI

------------------------------------------------------------------------
-- MODEL x OBSERVABLE MATRIX
--
-- Numerical evidence only discriminates competing models when it is attached
-- to the same measured observable.  The currently source-paid coordinates are
-- transverse:
--
--   Dark Dimension evolving-sector model : c' and micron radius
--   DAO alternative                      : DAO absolute amplitude
--
-- Therefore c' - A_D, R_perp - A_D, etc. are WrongType operations, not model
-- separations.  A future head-to-head forecast must supply both models on one
-- common observable before a numerical separation can be locked.
------------------------------------------------------------------------

data ModelKind : Set where
  darkDimensionModel : ModelKind
  darkAcousticOscillationModel : ModelKind

data ObservableKind : Set where
  evolvingDarkSectorCPrime : ObservableKind
  extraDimensionRadiusMicrometre : ObservableKind
  daoAbsoluteLinearAmplitude : ObservableKind

------------------------------------------------------------------------
-- Observable-indexed numerical evidence.
------------------------------------------------------------------------

data EvidenceFor : ObservableKind → Set where
  cPrimeEvidence :
    Quantitative.RatioEstimate →
    EvidenceFor evolvingDarkSectorCPrime

  radiusEvidence :
    Quantitative.SIInterval SI.Length SI.microScale →
    EvidenceFor extraDimensionRadiusMicrometre

  daoAmplitudeEvidence :
    Quantitative.DAOAmplitudeInterval →
    EvidenceFor daoAbsoluteLinearAmplitude

data CellEvidence (observable : ObservableKind) : Set where
  unspecifiedForModel : CellEvidence observable
  specifiedForModel : EvidenceFor observable → CellEvidence observable

record ModelObservableCell (observable : ObservableKind) : Set where
  constructor modelObservableCell
  field
    model : ModelKind
    evidence : CellEvidence observable
    numericalCoordinateSpecified : Bool
    sourceScope : String

open ModelObservableCell public

darkDimensionCPrimeCell : ModelObservableCell evolvingDarkSectorCPrime
darkDimensionCPrimeCell =
  modelObservableCell
    darkDimensionModel
    (specifiedForModel (cPrimeEvidence Quantitative.bedroyaCPrimeEnvelope))
    true
    "Bedroya-Obied-Vafa-Wu evolving-dark-sector c' fit coordinate"

darkDimensionRadiusCell : ModelObservableCell extraDimensionRadiusMicrometre
darkDimensionRadiusCell =
  modelObservableCell
    darkDimensionModel
    (specifiedForModel (radiusEvidence Quantitative.darkDimensionRadiusEnvelope))
    true
    "Law-Smith et al. source-supported effective-size interval"

darkDimensionDAOAmplitudeCell : ModelObservableCell daoAbsoluteLinearAmplitude
darkDimensionDAOAmplitudeCell =
  modelObservableCell
    darkDimensionModel
    unspecifiedForModel
    false
    "no Dark-Dimension DAO-amplitude prediction is paid by the sources admitted in this tranche"

daoAmplitudeCell : ModelObservableCell daoAbsoluteLinearAmplitude
daoAmplitudeCell =
  modelObservableCell
    darkAcousticOscillationModel
    (specifiedForModel (daoAmplitudeEvidence Quantitative.publishedDAOAmplitudeInterval))
    true
    "Garny-Niedermann-Sloth published DAO absolute-amplitude interval"

daoCPrimeCell : ModelObservableCell evolvingDarkSectorCPrime
daoCPrimeCell =
  modelObservableCell
    darkAcousticOscillationModel
    unspecifiedForModel
    false
    "DAO source does not supply the evolving-dark-sector c' coordinate"

daoRadiusCell : ModelObservableCell extraDimensionRadiusMicrometre
daoRadiusCell =
  modelObservableCell
    darkAcousticOscillationModel
    unspecifiedForModel
    false
    "DAO source does not supply a Dark-Dimension micron-radius coordinate"

------------------------------------------------------------------------
-- Same-observable requirement.
------------------------------------------------------------------------

record SameObservableRequirement
    (leftObservable rightObservable : ObservableKind) : Set where
  constructor sameObservableRequirement
  field
    sameObservable : leftObservable ≡ rightObservable

open SameObservableRequirement public

data CrossCoordinateDifferencePermission : Set where

crossCoordinateDifferenceIsWrongType :
  CrossCoordinateDifferencePermission → ⊥
crossCoordinateDifferenceIsWrongType ()

------------------------------------------------------------------------
-- Current matrix status.
--
-- Every source-paid numerical coordinate has at least one competing-model hole:
-- Dark Dimension does not specify A_D here, while DAO does not specify c' or
-- R_perp here.  So a shared-observable numerical forecast remains unpaid.
------------------------------------------------------------------------

record ModelObservableMatrixStatus : Set where
  constructor modelObservableMatrixStatus
  field
    darkDimensionCPrimeSpecified : Bool
    darkDimensionRadiusSpecified : Bool
    daoAmplitudeSpecified : Bool
    darkDimensionDAOAmplitudeSpecified : Bool
    daoCPrimeSpecified : Bool
    daoRadiusSpecified : Bool
    sharedObservableNumericalSeparationLocked : Bool
    sameObservableComparisonRequired : Bool

open ModelObservableMatrixStatus public

canonicalModelObservableMatrixStatus : ModelObservableMatrixStatus
canonicalModelObservableMatrixStatus =
  modelObservableMatrixStatus
    true
    true
    true
    false
    false
    false
    false
    true

sharedObservableNumericalSeparationStillOpen :
  sharedObservableNumericalSeparationLocked canonicalModelObservableMatrixStatus
  ≡ false
sharedObservableNumericalSeparationStillOpen = refl

sameObservableRequirementIsActive :
  sameObservableComparisonRequired canonicalModelObservableMatrixStatus
  ≡ true
sameObservableRequirementIsActive = refl
