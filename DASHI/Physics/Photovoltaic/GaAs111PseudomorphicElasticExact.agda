module DASHI.Physics.Photovoltaic.GaAs111PseudomorphicElasticExact where

-- Source-numeral exact [111] pseudomorphic GaAs compatibility.
-- This is a film on a coherent [111] plane, NOT a quantum-dot strain map.
-- C11,C12,C44 (GPa x 10): user-supplied 300 K GaAs source fixture.
-- Cross-check source: Phys Rev B 84, 195207 (2011), eqs 28-31;
-- Vurgaftman/Meyer/Ram-Mohan DOI 10.1063/1.1368156.
-- Reuses the original PV Bir-Pikus owner; no ESD surface edited.
-- Agda Golden kernel typecheck still OPEN.

open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
import DASHI.Physics.Photovoltaic.GaAs111BirPikusC3vFiniteExact as BP
import DASHI.Physics.Photovoltaic.GaAsKane369MaterialDiscriminatorExact as GaAs
import DASHI.Physics.Semiconductor.Device.DriftDiffusionContinuityExact as Carrier

c11TenthsGPa c12TenthsGPa c44TenthsGPa : Nat
c11TenthsGPa = 1188
c12TenthsGPa = 538
c44TenthsGPa = 594

-- Elastic zero-normal-traction equation, in positive magnitude form:
-- (C11+2C12+4C44)*|eps_out| =
--   2*(C11+2C12-2C44)*eps_in for positive tensile eps_in.
-- Source coefficients are multiplied by 10 to be natural numbers.
elasticDenominator elasticNumerator : Nat
elasticDenominator = 4640
elasticNumerator = 2152

denominatorFromCubicStiffness :
  elasticDenominator ≡ c11TenthsGPa + 2 * c12TenthsGPa + 4 * c44TenthsGPa
denominatorFromCubicStiffness = refl

numeratorWithoutSubtraction :
  elasticNumerator + 4 * c44TenthsGPa
  ≡ 2 * (c11TenthsGPa + 2 * c12TenthsGPa)
numeratorWithoutSubtraction = refl

-- Reduced exact magnitude ratio |eps_out|/eps_in = 269/580.
normalStressFreeGaAsCrossProduct :
  elasticDenominator * 269 ≡ elasticNumerator * 580
normalStressFreeGaAsCrossProduct = refl

-- IMPORTANT: Pseudomorphic is film-layer-specific. No transfer to a
-- dislocated InGaAs alloy or finite self-assembled GaAs/InP quantum dot.
record Pseudomorphic111SameMaterialAdmission : Set where
  field
    sourceLayerMaterial : String
    sourceSubstrateMaterial : String
    sourceLatticeMismatch : String
    sourceCubicElasticCoefficients : String
    independentlyObservedRelaxation : String
    sourceStrainTensor : String
    sourcePiezoConstantConvention : String
    sourceScreeningAndInterfaceFields : String
    sourceOpticalPolarizationData : String
    sourceAbsorptionAndPowerData : String

-- Explicit physical consumer names. Neither is manufactured from a scalar
-- ratio, C3v matrix covariance, or a source string.
record ElasticToPVPhysicalWeld : Set₁ where
  field
    sourceFilm : Pseudomorphic111SameMaterialAdmission
    gaasMaterial : GaAs.GaAsAtomic369ToKaneWeld
    carriers : Carrier.CarrierContinuity
    normalizedPhotonFluxReceipt : Set
    sourceMatchedMeasuredEQE : normalizedPhotonFluxReceipt
    radiativeDarkCurrentReceipt : Set
    observedDarkCurrent : radiativeDarkCurrentReceipt
    measuredMPPReceipt : Set
    observedMPP : measuredMPPReceipt

-- Source names remain intentionally in the source-dependent record.
-- No witness of ElasticToPVPhysicalWeld is asserted in this module.
