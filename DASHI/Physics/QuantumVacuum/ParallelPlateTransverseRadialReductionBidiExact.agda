module DASHI.Physics.QuantumVacuum.ParallelPlateTransverseRadialReductionBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.MeasureIntegralLimitKernelBidiExact as MIL
import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Casimir
import DASHI.Physics.QuantumVacuum.ParallelPlateTransverseMeasureLimitBidiExact as Transverse

------------------------------------------------------------------------
-- TRANSVERSE 2D -> RADIAL 1D REDUCTION, BIDI
--
-- For a rotationally symmetric parallel-plate integrand, the physical
-- transverse continuum is normally reduced schematically as
--
--   ∫ d²k_perp/(2π)² F(|k_perp|)
--       = (1/2π) ∫_0^∞ k dk F(k).
--
-- This owner does not assert the measure theorem.  It exposes exactly the
-- rotational-invariance, polar-coordinate, Jacobian and normalization receipts
-- needed to replace the two-dimensional transverse integral by the radial one
-- on the SAME Casimir integrand.
------------------------------------------------------------------------

record TransversePlaneRadialGeometry
    (kernel : Casimir.CasimirScalarModel) : Set₁ where
  field
    PlanePoint : Set
    Radius : Set
    Angle : Set
    Measure2D : Set
    MeasureRadial : Set

    radius : PlanePoint → Radius
    planeMeasure : Measure2D
    radialMeasure : MeasureRadial

    twoPiNormalization : Casimir.Scalar kernel
    geometryReading : String

open TransversePlaneRadialGeometry public

record RotationallySymmetricCasimirIntegrand
    (kernel : Casimir.CasimirScalarModel)
    (G : TransversePlaneRadialGeometry kernel) : Set₁ where
  field
    Integrand : Set
    planeIntegrand : PlanePoint G → Integrand
    radialIntegrand : Radius G → Integrand

    radialFactorisation :
      (k : PlanePoint G) →
      planeIntegrand k ≡ radialIntegrand (radius G k)

    sameCasimirModeIntegrand : Set
    reading : String

open RotationallySymmetricCasimirIntegrand public

record PolarMeasureReductionReceipt
    (kernel : Casimir.CasimirScalarModel)
    (G : TransversePlaneRadialGeometry kernel)
    (F : RotationallySymmetricCasimirIntegrand kernel G) : Set₁ where
  field
    planeIntegral : (PlanePoint G → Integrand F) → Casimir.Scalar kernel
    radialIntegral : (Radius G → Integrand F) → Casimir.Scalar kernel

    polarCoordinatesAdmissible : Set
    angularIntegrationClosed : Set
    jacobianFactorRadius : Set
    normalizationTwoPiClosed : Set
    radialDomainIsNonnegativeHalfLine : Set

    reductionEquality :
      planeIntegral (planeIntegrand F) ≡ radialIntegral (radialIntegrand F)

    sameMeasureObject : Set
    reductionReading : String

open PolarMeasureReductionReceipt public

------------------------------------------------------------------------
-- Casimir weld: the 2D object being reduced must literally be the transverse
-- family already bound to the regulated plate/reference difference.
------------------------------------------------------------------------

record CasimirRadialReduction
    (kernel : Casimir.CasimirScalarModel)
    (T : Transverse.CasimirTransverseMeasureFamily kernel) : Set₁ where
  field
    geometry : TransversePlaneRadialGeometry kernel
    symmetricIntegrand : RotationallySymmetricCasimirIntegrand kernel geometry
    reduction : PolarMeasureReductionReceipt kernel geometry symmetricIntegrand

    transversePointIdentifiedWithPlanePoint : Set
    transverseMeasureIdentifiedWithPlaneMeasure : Set
    regulatedIntegrandIdentifiedModewise : Set
    sameRegulatedDifferenceAfterReduction : Set

    reading : String

open CasimirRadialReduction public

------------------------------------------------------------------------
-- Reverse obligations.
------------------------------------------------------------------------

record RadialReductionObligations
    (kernel : Casimir.CasimirScalarModel) : Set₁ where
  field
    rotationalSymmetryOfPlateSpectrum : Set
    integrandDependsOnlyOnRadius : Set
    polarChangeOfVariablesTheorem : Set
    angularMeasureNormalization : Set
    jacobianReceipt : Set
    noBoundaryOrZeroModeLost : Set
    sameObjectWeldToTransverseDifference : Set
    reading : String

open RadialReductionObligations public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data RotationalNotationAutomaticallyProvesMeasureReduction : Set where

data RadialIntegralAutomaticallyEqualsCasimirIntegral : Set where

rotationalNotationDoesNotProveJacobian :
  RotationalNotationAutomaticallyProvesMeasureReduction → ⊥
rotationalNotationDoesNotProveJacobian ()

radialFormulaNeedsSameObjectWeld :
  RadialIntegralAutomaticallyEqualsCasimirIntegral → ⊥
radialFormulaNeedsSameObjectWeld ()

record RadialReductionStatus : Set where
  field
    radialReductionInterfaceOwned : Bool
    sameObjectCasimirWeldInterfaceOwned : Bool
    concretePolarMeasureTheoremClosed : Bool
    radialCasimirIntegralClosed : Bool

    radialReductionInterfaceOwnedIsTrue : radialReductionInterfaceOwned ≡ true
    sameObjectCasimirWeldInterfaceOwnedIsTrue :
      sameObjectCasimirWeldInterfaceOwned ≡ true
    concretePolarMeasureTheoremClosedIsFalse :
      concretePolarMeasureTheoremClosed ≡ false
    radialCasimirIntegralClosedIsFalse : radialCasimirIntegralClosed ≡ false

open RadialReductionStatus public

canonicalRadialReductionStatus : RadialReductionStatus
canonicalRadialReductionStatus = record
  { radialReductionInterfaceOwned = true
  ; sameObjectCasimirWeldInterfaceOwned = true
  ; concretePolarMeasureTheoremClosed = false
  ; radialCasimirIntegralClosed = false
  ; radialReductionInterfaceOwnedIsTrue = refl
  ; sameObjectCasimirWeldInterfaceOwnedIsTrue = refl
  ; concretePolarMeasureTheoremClosedIsFalse = refl
  ; radialCasimirIntegralClosedIsFalse = refl
  }
