module DASHI.Physics.Textile.EffectiveFabricResponseExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Physics.Units.MechanicalDimensionExact as Dim
import DASHI.Physics.Textile.TextileMechanicalDimensionExact as TextileDim
import DASHI.Physics.Textile.QuasiStaticTextileLoadTransferExact as Load
import DASHI.Physics.Textile.TextileEmpiricalCalibrationExact as Calibration
import DASHI.Topology.TextileStitchHyperfabricExact as Stitch

------------------------------------------------------------------------
-- Effective fabric-scale observables.
--
-- ISO 13934-1:2013 specifies strip testing for maximum force and elongation at
-- maximum force and was confirmed current in 2024.  ASTM D5035-11(2024) is a
-- related breaking-force/elongation strip method but explicitly warns that it
-- is not recommended for knitted or >11% high-stretch fabrics.
--
-- To avoid assigning an arbitrary solid cross-sectional area to an open textile
-- network, the axial effective observable here is force per specimen width,
-- not a 3-D Young modulus.  The corresponding extensional stiffness per width
-- obeys n = K epsilon when a producer supplies such a secant/tangent receipt.
------------------------------------------------------------------------

iso13934Title : String
iso13934Title =
  "ISO 13934-1:2013: Tensile properties of fabrics — maximum force and elongation using the strip method"

astmD5035Title : String
astmD5035Title =
  "ASTM D5035-11(2024): Breaking Force and Elongation of Textile Fabrics (Strip Method)"

astmD5035DOI : String
astmD5035DOI = "10.1520/D5035-11R24"

fabricLineForceDimension : Dim.MechanicalDimension
fabricLineForceDimension =
  TextileDim.tensionDimension Dim.⊗ᴰ Dim.inverseLengthDimension

fabricExtensionalStiffnessDimension : Dim.MechanicalDimension
fabricExtensionalStiffnessDimension = fabricLineForceDimension

lineForceTimesWidthIsForce :
  fabricLineForceDimension Dim.⊗ᴰ Dim.lengthDimension
  ≡ TextileDim.tensionDimension
lineForceTimesWidthIsForce = refl

extensionalStiffnessTimesStrainIsLineForce :
  fabricExtensionalStiffnessDimension Dim.⊗ᴰ TextileDim.strainDimension
  ≡ fabricLineForceDimension
extensionalStiffnessTimesStrainIsLineForce = refl

LineForce : Set → Set
LineForce Scalar = Dim.Quantity Scalar fabricLineForceDimension

ExtensionalStiffnessPerWidth : Set → Set
ExtensionalStiffnessPerWidth Scalar =
  Dim.Quantity Scalar fabricExtensionalStiffnessDimension

record FabricAxialEffectiveResponse
    {Scalar : Set}
    (algebra : Load.ScalarMechanicalAlgebra Scalar)
    (topology : Stitch.StitchState) : Set₁ where
  constructor fabric-axial-effective-response
  field
    specimen : Calibration.SpecimenIdentity
    testAuthority : String
    methodApplicabilityEvidence : String

    specimenWidth : Dim.Quantity Scalar Dim.lengthDimension
    appliedForce : Load.Force Scalar
    fabricStrain : Dim.Quantity Scalar TextileDim.strainDimension
    lineForce : LineForce Scalar
    effectiveExtensionalStiffness : ExtensionalStiffnessPerWidth Scalar

    forceFromLineForceAndWidth :
      Dim.magnitude appliedForce
      ≡ Load.multiply algebra
          (Dim.magnitude lineForce)
          (Dim.magnitude specimenWidth)

    effectiveLaw :
      Dim.magnitude lineForce
      ≡ Load.multiply algebra
          (Dim.magnitude effectiveExtensionalStiffness)
          (Dim.magnitude fabricStrain)

    retainedTopology : Stitch.StitchState
    retainedTopologyIsSameObject : retainedTopology ≡ topology

open FabricAxialEffectiveResponse public

------------------------------------------------------------------------
-- Bending response remains a distinct empirical fabric observable.  In
-- particular, the D1388 flexural-rigidity result is not definitionally yarn EI.
------------------------------------------------------------------------

record EffectiveFabricResponse
    {Scalar : Set}
    (algebra : Load.ScalarMechanicalAlgebra Scalar)
    (topology : Stitch.StitchState) : Set₁ where
  constructor effective-fabric-response
  field
    axial : FabricAxialEffectiveResponse algebra topology
    bending : Calibration.FabricStiffnessCalibration Scalar

open EffectiveFabricResponse public

------------------------------------------------------------------------
-- Non-promotion boundaries.
------------------------------------------------------------------------

data FabricExtensionalStiffnessIsYarnYoungModulus : Set where

fabricExtensionalStiffnessIsNotYarnYoungModulus :
  FabricExtensionalStiffnessIsYarnYoungModulus → ⊥
fabricExtensionalStiffnessIsNotYarnYoungModulus ()

data StripTestAuthorityIsAutomaticallyApplicableToEveryKnit : Set where

stripTestAuthorityIsNotAutomaticallyApplicableToEveryKnit :
  StripTestAuthorityIsAutomaticallyApplicableToEveryKnit → ⊥
stripTestAuthorityIsNotAutomaticallyApplicableToEveryKnit ()

data AxialAndBendingResponseDetermineDrape : Set where

axialAndBendingResponseDoNotDetermineDrape :
  AxialAndBendingResponseDetermineDrape → ⊥
axialAndBendingResponseDoNotDetermineDrape ()
