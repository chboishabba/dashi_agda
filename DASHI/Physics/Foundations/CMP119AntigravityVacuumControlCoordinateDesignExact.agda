{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityVacuumControlCoordinateDesignExact where

open import DASHI.Core.Prelude
open import Data.Rational.Base using (ℚ)

import DASHI.Core.ExperimentalCoordinateDesignExact as Coordinate
import DASHI.Physics.Foundations.CMP119AntigravityCanonicalSourceSectorActionExact as Canonical
import DASHI.Physics.Foundations.CMP119AntigravityVacuumExperimentDiscriminatorExact as VacuumDisc
import DASHI.Physics.Foundations.CMP119AntigravityVacuumSequenceNonidentifiabilityExact as NI

------------------------------------------------------------------------
-- VACUUM COLLISION -> EXPERIMENTAL COORDINATE / CONTROL TARGET
--
-- The non-identifiability theorem says the current coupling+density+
-- background+fluctuation+E/R/B view cannot recover the selected vacuum-
-- constant coordinate.  ExperimentalCoordinateDesignExact supplies the right
-- next question: which extra coordinate must be measured or deliberately
-- varied?
--
-- This owner makes the answer literal without manufacturing an actuator:
--
--   missing measured coordinate = selected constant/remainder readout;
--
-- and an adequate selective control must
--
--   (1) preserve the declared current-source view at the selected scale;
--   (2) change the selected vacuum-constant coordinate at that same scale.
--
-- Such a control automatically gives a nonzero OFF/ON source pair for the
-- differential lane.  Existence, safety, laboratory meaning and physical
-- calibration of such a control remain external/source payments.
------------------------------------------------------------------------

data VacuumExperimentCoordinate : Set where
  projectedVacuumCoordinate : VacuumExperimentCoordinate

data VacuumExperimentDimension : Set where
  projectedVacuumSourceDimension : VacuumExperimentDimension

module _
  {Density Background Fluctuation Control : Set}
  (applyControl :
    Control →
    Canonical.CMP119NormalizedSectorSource Density Background Fluctuation →
    Canonical.CMP119NormalizedSectorSource Density Background Fluctuation)
  (controlReference : Control → String)
  (scale : Nat)
  where

  vacuumExperimentDesign :
    Coordinate.ExperimentalCoordinateDesign
      (Canonical.CMP119NormalizedSectorSource Density Background Fluctuation)
      Control ℚ VacuumExperimentDimension
  vacuumExperimentDesign = record
    { Coordinate.ExperimentalCoordinateDesign.Coordinate =
        VacuumExperimentCoordinate
    ; Coordinate.ExperimentalCoordinateDesign.role =
        λ _ → Coordinate.measuredObservable
    ; Coordinate.ExperimentalCoordinateDesign.dimension =
        λ _ → projectedVacuumSourceDimension
    ; Coordinate.ExperimentalCoordinateDesign.read =
        λ _ source → NI.projectedVacuum source scale
    ; Coordinate.ExperimentalCoordinateDesign.applyControl = applyControl
    ; Coordinate.ExperimentalCoordinateDesign.coordinateReference =
        λ _ → "CMP119 selected vacuum constant/remainder coordinate"
    ; Coordinate.ExperimentalCoordinateDesign.dimensionReference =
        λ _ → "source-normalization / vacuum-constant coordinate; physical units require calibration"
    ; Coordinate.ExperimentalCoordinateDesign.calibrationOrDerivationReference =
        λ _ → "formal constant/remainder-coordinate readout; physical same-object measurement calibration still required"
    ; Coordinate.ExperimentalCoordinateDesign.controlReference = controlReference
    }

  projectedVacuumCoordinateSeparatesCanonicalCollision :
    (source : Canonical.CMP119NormalizedSectorSource
      Density Background Fluctuation) →
    Coordinate.CoordinateSeparatesCollision
      vacuumExperimentDesign
      (λ candidate → VacuumDisc.currentSourceViewAtScale candidate scale)
  projectedVacuumCoordinateSeparatesCanonicalCollision source =
    Coordinate.coordinateSeparatesCollision
      projectedVacuumCoordinate
      (NI.zeroVacuumSource source)
      (NI.unitVacuumSource source)
      refl
      (NI.projectedVacuumSequencesDiffer source scale)

  record VacuumSelectiveControl : Set₁ where
    constructor vacuum-selective-control
    field
      control : Control
      world :
        Canonical.CMP119NormalizedSectorSource
          Density Background Fluctuation

      selectiveControlPreservesCurrentSourceView :
        VacuumDisc.currentSourceViewAtScale
          (applyControl control world) scale
        ≡
        VacuumDisc.currentSourceViewAtScale world scale

      selectiveControlChangesProjectedVacuum :
        NI.projectedVacuum (applyControl control world) scale
        ≡ NI.projectedVacuum world scale → ⊥

      PhysicalControlAdmissionReceipt : Set
      physicalControlAdmissionReceipt : PhysicalControlAdmissionReceipt

      PhysicalVacuumCoordinateCalibrationReceipt : Set
      physicalVacuumCoordinateCalibrationReceipt :
        PhysicalVacuumCoordinateCalibrationReceipt

  open VacuumSelectiveControl public

  selectiveControlMakesVacuumCoordinateModifiable :
    VacuumSelectiveControl →
    Coordinate.CoordinateModifiableBy
      vacuumExperimentDesign
      projectedVacuumCoordinate
  selectiveControlMakesVacuumCoordinateModifiable selective = record
    { Coordinate.CoordinateModifiableBy.control = control selective
    ; Coordinate.CoordinateModifiableBy.world = world selective
    ; Coordinate.CoordinateModifiableBy.changesCoordinate =
        selectiveControlChangesProjectedVacuum selective
    }

  record VacuumSourceDifferenceWitness : Set where
    constructor vacuum-source-difference-witness
    field
      sourceOff : ℚ
      sourceOn : ℚ
      nonzeroSourceDifference : sourceOff ≡ sourceOn → ⊥

  open VacuumSourceDifferenceWitness public

  selectiveControlProducesNonzeroSourcePair :
    VacuumSelectiveControl → VacuumSourceDifferenceWitness
  selectiveControlProducesNonzeroSourcePair selective = record
    { VacuumSourceDifferenceWitness.sourceOff =
        NI.projectedVacuum (world selective) scale
    ; VacuumSourceDifferenceWitness.sourceOn =
        NI.projectedVacuum
          (applyControl (control selective) (world selective)) scale
    ; VacuumSourceDifferenceWitness.nonzeroSourceDifference =
        λ same → selectiveControlChangesProjectedVacuum selective (sym same)
    }

------------------------------------------------------------------------
-- SCHEDULING BOUNDARY
------------------------------------------------------------------------

record VacuumControlCoordinateBoundary : Set where
  constructor vacuum-control-coordinate-boundary
  field
    missingVacuumCoordinateIdentified : Bool
    canonicalCollisionSeparatedByThatCoordinate : Bool
    selectiveControlTargetCompiled : Bool
    selectiveControlProducesNonzeroDifferentialPair : Bool
    formalCoordinateAlreadyIsCalibratedLabObservable : Bool
    physicalSelectiveControlAlreadyConstructed : Bool

canonicalVacuumControlCoordinateBoundary : VacuumControlCoordinateBoundary
canonicalVacuumControlCoordinateBoundary =
  vacuum-control-coordinate-boundary
    true true true true false false

vacuumSelectiveControlTargetCompiled : Bool
vacuumSelectiveControlTargetCompiled = true

physicalVacuumSelectiveControlStillRequired : Bool
physicalVacuumSelectiveControlStillRequired = true

formalProjectedVacuumAlreadyCalibratedPhysicalObservable : Bool
formalProjectedVacuumAlreadyCalibratedPhysicalObservable = false
