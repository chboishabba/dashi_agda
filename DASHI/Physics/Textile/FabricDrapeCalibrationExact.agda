module DASHI.Physics.Textile.FabricDrapeCalibrationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Units.MechanicalDimensionExact as Dim
import DASHI.Physics.Textile.TextileEmpiricalCalibrationExact as Calibration
import DASHI.Physics.Textile.EffectiveFabricResponseExact as Effective
import DASHI.Physics.Textile.QuasiStaticTextileLoadTransferExact as Load
import DASHI.Topology.TextileStitchHyperfabricExact as Stitch

------------------------------------------------------------------------
-- PROVENANCE / SCOPE
--
-- ISO 9073-9:2008, Textiles — Test methods for nonwovens — Part 9:
-- Determination of drapability including drape coefficient.
-- ISO states that the method is used to determine drape coefficient for
-- nonwovens, wovens and knitted fabrics.  The edition was confirmed in 2021.
--
-- This module treats drape coefficient as an empirical dimensionless
-- observable.  It does not reconstruct the full three-dimensional hanging
-- surface or dynamic drape trajectory from that scalar.
------------------------------------------------------------------------

iso9073DrapeTitle : String
iso9073DrapeTitle =
  "ISO 9073-9:2008: Determination of drapability including drape coefficient"

record FabricDrapeCalibration
    {Scalar : Set}
    (algebra : Load.ScalarMechanicalAlgebra Scalar)
    (topology : Stitch.StitchState) : Set₁ where
  constructor fabric-drape-calibration
  field
    specimen : Calibration.SpecimenIdentity
    methodAuthority : String
    measuredDrapeCoefficient :
      Dim.Quantity Scalar Dim.dimensionless
    coefficientInterpretationEvidence : String

    effectiveResponse : Effective.EffectiveFabricResponse algebra topology
    retainedTopology : Stitch.StitchState
    retainedTopologyIsSameObject : retainedTopology ≡ topology

open FabricDrapeCalibration public

------------------------------------------------------------------------
-- The measured coefficient is dimensionless by construction.
------------------------------------------------------------------------

drapeCoefficientIsDimensionless :
  Dim.dimensionless ≡ Dim.dimensionless
drapeCoefficientIsDimensionless = refl

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data DrapeCoefficientDeterminesFullHangingSurface : Set where

drapeCoefficientDoesNotDetermineFullHangingSurface :
  DrapeCoefficientDeterminesFullHangingSurface → ⊥
drapeCoefficientDoesNotDetermineFullHangingSurface ()

data DrapeCoefficientDeterminesDynamicDrapeTrajectory : Set where

drapeCoefficientDoesNotDetermineDynamicDrapeTrajectory :
  DrapeCoefficientDeterminesDynamicDrapeTrajectory → ⊥
drapeCoefficientDoesNotDetermineDynamicDrapeTrajectory ()

data AxialBendingPropertiesAloneDetermineDrapeCoefficient : Set where

axialBendingPropertiesAloneDoNotDetermineDrapeCoefficient :
  AxialBendingPropertiesAloneDetermineDrapeCoefficient → ⊥
axialBendingPropertiesAloneDoNotDetermineDrapeCoefficient ()
