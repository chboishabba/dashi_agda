module DASHI.Physics.QuantumVacuum.ParallelPlateRadialSpectralIntegrandBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Analysis.ConstructiveRealSpine as CRS
import DASHI.Analysis.OrdinaryComplexPolar as Polar
import DASHI.Physics.QuantumVacuum.CasimirParallelPlateKernel as Casimir
import DASHI.Physics.QuantumVacuum.ParallelPlateConstructiveRealSpectralAuthorityExact as Spectral
import DASHI.Physics.QuantumVacuum.ParallelPlateTransverseRadialReductionBidiExact as Radial

------------------------------------------------------------------------
-- EXPLICIT RADIAL CASIMIR SPECTRAL INTEGRAND, BIDI
--
-- After the transverse 2D -> radial reduction, one mode has the schematic
-- integrand
--
--   k * sqrt(k^2 + a_n^2) * R_epsilon(sqrt(k^2 + a_n^2))
--
-- with a_n = n*pi/d.  This owner records that exact shape on the existing
-- constructive-real spectral authority.  It does not prove integrability or
-- evaluate the integral.
------------------------------------------------------------------------

record RadialModeData
    (kernel : Casimir.CasimirScalarModel)
    (A : Spectral.ParallelPlateConstructiveRealSpectralAuthority kernel) : Set₁ where
  field
    Radius : Set
    radiusValue : Radius → CRS.Real (Spectral.ScalarBridge.real (Spectral.scalarPackage A))

    Mode : Set
    longitudinalScale : Mode → CRS.Real (Spectral.ScalarBridge.real (Spectral.scalarPackage A))

    radicandNonnegative :
      Radius → Mode → Set

    modeFrequencyWithoutC :
      Radius → Mode → CRS.Real (Spectral.ScalarBridge.real (Spectral.scalarPackage A))

    frequencyLaw :
      (k : Radius) → (m : Mode) →
      radicandNonnegative k m → Set

    reading : String

open RadialModeData public

record RadialRegulatedIntegrand
    (kernel : Casimir.CasimirScalarModel)
    (A : Spectral.ParallelPlateConstructiveRealSpectralAuthority kernel)
    (D : RadialModeData kernel A) : Set₁ where
  field
    Integrand : Set

    regulated :
      Spectral.RegulatorParameter A →
      Radius D → Mode D → Integrand

    unregulated : Radius D → Mode D → Integrand

    radialJacobianIncluded : Set
    zeroPointHalfIncluded : Set
    polarizationWeightIncluded : Set
    regulatorWeightIncluded : Set

    explicitShapeWeld :
      (epsilon : Spectral.RegulatorParameter A) →
      (k : Radius D) →
      (m : Mode D) → Set

    pointwiseRegulatorRemovalWeld : Set
    reading : String

open RadialRegulatedIntegrand public

------------------------------------------------------------------------
-- Useful substitution target.  With u = sqrt(k^2 + a^2), k dk = u du, the
-- radial energy integral reduces schematically to an integral of u^2 times the
-- regulator.  The change-of-variables theorem is an analytic payment.
------------------------------------------------------------------------

record RadialEnergySubstitution
    (kernel : Casimir.CasimirScalarModel) : Set₁ where
  field
    Radius EnergyVariable Integrand Scalar : Set

    substitution : Radius → EnergyVariable
    radialIntegrand : Radius → Integrand
    energyIntegrand : EnergyVariable → Integrand

    lowerEndpoint : EnergyVariable

    substitutionMonotone : Set
    substitutionDifferentiable : Set
    jacobianIdentity : Set
    endpointTransport : Set
    integralChangeOfVariables : Set

    reducedIntegralValue : Scalar
    reading : String

open RadialEnergySubstitution public

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ExplicitIntegrandAutomaticallyIntegrable : Set where

data FormalSubstitutionAutomaticallyEvaluatesIntegral : Set where

explicitShapeDoesNotAutoSupplyIntegrability :
  ExplicitIntegrandAutomaticallyIntegrable → ⊥
explicitShapeDoesNotAutoSupplyIntegrability ()

substitutionNeedsAnalyticTheorem :
  FormalSubstitutionAutomaticallyEvaluatesIntegral → ⊥
substitutionNeedsAnalyticTheorem ()
