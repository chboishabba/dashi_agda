module DASHI.Physics.Textile.TextileEmpiricalCalibrationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Units.MechanicalDimensionExact as Dim
import DASHI.Physics.Textile.TextileMechanicalDimensionExact as TextileDim
import DASHI.Physics.Textile.TextileMechanicalFibreExact as Mechanics
import DASHI.Physics.Textile.QuasiStaticTextileLoadTransferExact as Load

------------------------------------------------------------------------
-- Measurement-protocol authority.
--
-- ASTM D2256/D2256M: single-strand yarn tensile properties, including
-- breaking force and elongation and modulus-type derived quantities.
-- ISO 2062:2009: single-end breaking force and elongation at break for yarns
-- from packages using CRE tensile testing.
-- ASTM D1388-23: fabric stiffness; bending length is measured and flexural
-- rigidity is calculated.
--
-- These standards define measurement procedures.  They do NOT provide a
-- universal material constant for cotton, wool, nylon, etc.  Numerical values
-- therefore remain producer-supplied specimen/test results.
------------------------------------------------------------------------

astmD2256Title : String
astmD2256Title =
  "ASTM D2256/D2256M: Tensile Properties of Yarns by the Single-Strand Method"

iso2062Title : String
iso2062Title =
  "ISO 2062:2009: Yarns from packages — single-end breaking force and elongation at break"

astmD1388Title : String
astmD1388Title =
  "ASTM D1388-23: Standard Test Method for Stiffness of Fabrics"

astmD1388DOI : String
astmD1388DOI = "10.1520/D1388-23"

data YarnTensileProtocol : Set where
  astmD2256SingleStrand : YarnTensileProtocol
  iso2062CRE : YarnTensileProtocol

record SpecimenIdentity : Set where
  constructor specimen-identity
  field
    specimenLabel : String
    materialLabel : String
    conditioningLabel : String
    laboratoryOrDataset : String
    sourceRecord : String

open SpecimenIdentity public

record YarnTensileCalibration
    {Scalar : Set}
    (algebra : Load.ScalarMechanicalAlgebra Scalar)
    (state : Mechanics.YarnConstitutiveState Scalar) : Set₁ where
  constructor yarn-tensile-calibration
  field
    specimen : SpecimenIdentity
    protocol : YarnTensileProtocol

    measuredBreakingForce : Load.Force Scalar
    measuredElongationAtBreak :
      Dim.Quantity Scalar TextileDim.strainDimension
    measuredLinearDensity :
      Dim.Quantity Scalar TextileDim.linearDensityDimension

    failureForceLaw :
      Dim.magnitude measuredBreakingForce
      ≡ Load.multiply algebra
          (Dim.magnitude (Mechanics.failureStress state))
          (Dim.magnitude (Mechanics.crossSectionArea state))

    failureStrainMatchesMeasurement :
      Dim.magnitude (Mechanics.failureStrain state)
      ≡ Dim.magnitude measuredElongationAtBreak

    linearDensityMatchesMeasurement :
      Dim.magnitude (Mechanics.linearDensity state)
      ≡ Dim.magnitude measuredLinearDensity

open YarnTensileCalibration public

------------------------------------------------------------------------
-- Fabric stiffness calibration is kept distinct from yarn EI.
-- ASTM D1388 reports fabric bending length and a calculated flexural-rigidity
-- observable.  We retain the standard's reported unit convention explicitly
-- rather than silently identifying it with the yarn-scale beam EI coordinate.
------------------------------------------------------------------------

data FabricStiffnessMethod : Set where
  d1388Cantilever : FabricStiffnessMethod
  d1388HeartLoop : FabricStiffnessMethod

record FabricStiffnessCalibration (Scalar : Set) : Set₁ where
  constructor fabric-stiffness-calibration
  field
    specimen : SpecimenIdentity
    method : FabricStiffnessMethod
    bendingLength : Dim.Quantity Scalar Dim.lengthDimension
    reportedFlexuralRigidity : Scalar
    reportedFlexuralRigidityUnit : String
    methodApplicabilityEvidence : String

open FabricStiffnessCalibration public

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data TestStandardSuppliesUniversalMaterialConstant : Set where

testStandardDoesNotSupplyUniversalMaterialConstant :
  TestStandardSuppliesUniversalMaterialConstant → ⊥
testStandardDoesNotSupplyUniversalMaterialConstant ()

data FabricFlexuralRigidityIsYarnBeamEIByDefinition : Set where

fabricFlexuralRigidityIsNotYarnBeamEIByDefinition :
  FabricFlexuralRigidityIsYarnBeamEIByDefinition → ⊥
fabricFlexuralRigidityIsNotYarnBeamEIByDefinition ()

data OneSpecimenCalibrationGeneralisesToAllMaterialLots : Set where

oneSpecimenCalibrationDoesNotGeneraliseToAllMaterialLots :
  OneSpecimenCalibrationGeneralisesToAllMaterialLots → ⊥
oneSpecimenCalibrationDoesNotGeneraliseToAllMaterialLots ()
