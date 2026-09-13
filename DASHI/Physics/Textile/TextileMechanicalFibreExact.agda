module DASHI.Physics.Textile.TextileMechanicalFibreExact where

open import Agda.Primitive using (Set; Set₁)

import DASHI.Physics.Units.MechanicalDimensionExact as Dim
import DASHI.Physics.Textile.TextileMechanicalDimensionExact as TextileDim

record YarnConstitutiveState (Scalar : Set) : Set where
  constructor yarn-constitutive-state
  field
    restLength : Dim.Quantity Scalar Dim.lengthDimension
    crossSectionArea : Dim.Quantity Scalar Dim.areaDimension
    linearDensity : Dim.Quantity Scalar TextileDim.linearDensityDimension
    tension : Dim.Quantity Scalar TextileDim.tensionDimension
    strain : Dim.Quantity Scalar TextileDim.strainDimension
    tensileStress : Dim.Quantity Scalar TextileDim.stressDimension
    youngModulus : Dim.Quantity Scalar TextileDim.youngModulusDimension
    axialRigidity : Dim.Quantity Scalar TextileDim.axialRigidityDimension
    bendingRigidity : Dim.Quantity Scalar TextileDim.bendingRigidityDimension
    torsionalRigidity : Dim.Quantity Scalar TextileDim.torsionalRigidityDimension
    failureStress : Dim.Quantity Scalar TextileDim.stressDimension
    failureStrain : Dim.Quantity Scalar TextileDim.strainDimension

open YarnConstitutiveState public

record LocalTextileConstraint (Scalar : Set) : Set where
  constructor local-textile-constraint
  field
    normalForce : Dim.Quantity Scalar TextileDim.tensionDimension
    frictionCoefficient : Dim.Quantity Scalar Dim.dimensionless
    localCurvature : Dim.Quantity Scalar TextileDim.curvatureDimension
    slipThreshold : Dim.Quantity Scalar TextileDim.tensionDimension

open LocalTextileConstraint public

record PhysicalTextileFibre
    (Scalar Cell Constraint : Set) : Set₁ where
  constructor physical-textile-fibre
  field
    materialAt : Cell → YarnConstitutiveState Scalar
    constraintAt : Constraint → LocalTextileConstraint Scalar
    arealDensity : Dim.Quantity Scalar TextileDim.arealDensityDimension

open PhysicalTextileFibre public
