module DASHI.Physics.Foundations.KernelGeometryEmergenceObligations where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Algebra.Quantum.SignatureDerivation as Signature
import DASHI.Promotion.GRBoundaryClarification as ExistingGRBoundary

------------------------------------------------------------------------
-- A scalar load does not determine a relativistic stress tensor.

record KernelLoad : Set where
  constructor kernelLoad
  field
    scalarDensity : Nat

open KernelLoad public

record StressProfile : Set where
  constructor stressProfile
  field
    energyDensity : Nat
    isotropicPressure : Nat
    anisotropicStress : Nat
    momentumFlux : Nat

open StressProfile public

stressProfileA : StressProfile
stressProfileA = stressProfile 5 1 0 0

stressProfileB : StressProfile
stressProfileB = stressProfile 5 3 2 1

sameDensityAllowsDifferentTensorData :
  energyDensity stressProfileA ≡ energyDensity stressProfileB
sameDensityAllowsDifferentTensorData = refl

------------------------------------------------------------------------
-- Finite symmetric rank-two component carrier.

data SymmetricTensorComponent4 : Set where
  component00 : SymmetricTensorComponent4
  component01 : SymmetricTensorComponent4
  component02 : SymmetricTensorComponent4
  component03 : SymmetricTensorComponent4
  component11 : SymmetricTensorComponent4
  component12 : SymmetricTensorComponent4
  component13 : SymmetricTensorComponent4
  component22 : SymmetricTensorComponent4
  component23 : SymmetricTensorComponent4
  component33 : SymmetricTensorComponent4

StressInformationTensor : Set
StressInformationTensor = SymmetricTensorComponent4 → Nat

zeroStressInformationTensor : StressInformationTensor
zeroStressInformationTensor component = 0

zeroTensorHasZeroEnergyDensity :
  zeroStressInformationTensor component00 ≡ 0
zeroTensorHasZeroEnergyDensity = refl

------------------------------------------------------------------------
-- Required continuum-emergence obligations.

data GeometryEmergenceObligation : Set where
  continuumManifoldObligation : GeometryEmergenceObligation
  lorentzianMetricObligation : GeometryEmergenceObligation
  tensorSourceObligation : GeometryEmergenceObligation
  bianchiIdentityObligation : GeometryEmergenceObligation
  covariantConservationObligation : GeometryEmergenceObligation
  diffeomorphismInvarianceObligation : GeometryEmergenceObligation
  equivalencePrincipleObligation : GeometryEmergenceObligation
  geodesicLimitObligation : GeometryEmergenceObligation
  gravitationalRadiationObligation : GeometryEmergenceObligation
  einsteinDynamicsObligation : GeometryEmergenceObligation
  controlledCorrectionObligation : GeometryEmergenceObligation

canonicalGeometryEmergenceObligations : List GeometryEmergenceObligation
canonicalGeometryEmergenceObligations =
  continuumManifoldObligation
  ∷ lorentzianMetricObligation
  ∷ tensorSourceObligation
  ∷ bianchiIdentityObligation
  ∷ covariantConservationObligation
  ∷ diffeomorphismInvarianceObligation
  ∷ equivalencePrincipleObligation
  ∷ geodesicLimitObligation
  ∷ gravitationalRadiationObligation
  ∷ einsteinDynamicsObligation
  ∷ controlledCorrectionObligation
  ∷ []

data ObligationState : Set where
  obligationRecorded : ObligationState
  obligationDischarged : ObligationState
  externalAuthorityRequired : ObligationState

record GeometryObligationReceipt : Set where
  constructor geometryObligationReceipt
  field
    obligation : GeometryEmergenceObligation
    state : ObligationState
    note : String

open GeometryObligationReceipt public

canonicalGeometryObligationReceipts : List GeometryObligationReceipt
canonicalGeometryObligationReceipts =
  geometryObligationReceipt continuumManifoldObligation obligationRecorded
    "A coarse-graining map must construct a continuum manifold."
  ∷ geometryObligationReceipt lorentzianMetricObligation obligationRecorded
    "The coarse geometry must carry a Lorentzian metric rather than a scalar congestion field."
  ∷ geometryObligationReceipt tensorSourceObligation obligationRecorded
    "Kernel data must produce energy, momentum, pressure, and anisotropic stress."
  ∷ geometryObligationReceipt bianchiIdentityObligation obligationRecorded
    "The emergent curvature tensor must satisfy the differential Bianchi identity."
  ∷ geometryObligationReceipt covariantConservationObligation obligationRecorded
    "The emergent source must satisfy covariant conservation."
  ∷ geometryObligationReceipt diffeomorphismInvarianceObligation obligationRecorded
    "Continuum predictions must be invariant under coordinate changes."
  ∷ geometryObligationReceipt equivalencePrincipleObligation obligationRecorded
    "Matter coupling must recover universal local free fall."
  ∷ geometryObligationReceipt geodesicLimitObligation obligationRecorded
    "Wave packets or probes must converge to geodesic motion in the appropriate limit."
  ∷ geometryObligationReceipt gravitationalRadiationObligation obligationRecorded
    "The metric sector must contain propagating transverse gravitational degrees of freedom."
  ∷ geometryObligationReceipt einsteinDynamicsObligation obligationRecorded
    "The effective field equation must recover Einstein dynamics with controlled conventions."
  ∷ geometryObligationReceipt controlledCorrectionObligation obligationRecorded
    "Higher-order corrections must be bounded in the claimed infrared regime."
  ∷ []

existingSignatureAxiomSurface : Set₁
existingSignatureAxiomSurface = Signature.SignatureDerivationAxioms

existingGRBoundarySurface : Set₁
existingGRBoundarySurface = ExistingGRBoundary.GRBoundaryClarificationIndex

------------------------------------------------------------------------
-- Joint adapter boundary.

record KernelGeometryAdapter : Set where
  constructor kernelGeometryAdapter
  field
    continuumManifoldConstructed : Bool
    lorentzianMetricConstructed : Bool
    tensorSourceConstructed : Bool
    bianchiIdentityProved : Bool
    covariantConservationProved : Bool
    equivalencePrincipleRecovered : Bool
    geodesicLimitRecovered : Bool
    gravitationalRadiationRecovered : Bool
    einsteinEquationRecovered : Bool
    correctionBoundProved : Bool

open KernelGeometryAdapter public

currentKernelGeometryAdapter : KernelGeometryAdapter
currentKernelGeometryAdapter =
  kernelGeometryAdapter
    false false false false false false false false false false

record KernelGeometryBoundary : Set where
  constructor kernelGeometryBoundary
  field
    scalarCongestionRuleIsEinsteinEquation : Bool
    scalarCongestionRuleIsEinsteinEquationIsFalse :
      scalarCongestionRuleIsEinsteinEquation ≡ false

    fewerAdmissiblePathsAloneDeriveGeodesicBending : Bool
    fewerAdmissiblePathsAloneDeriveGeodesicBendingIsFalse :
      fewerAdmissiblePathsAloneDeriveGeodesicBending ≡ false

    cosmologicalConstantIsMerelyAnInfraredHeader : Bool
    cosmologicalConstantIsMerelyAnInfraredHeaderIsFalse :
      cosmologicalConstantIsMerelyAnInfraredHeader ≡ false

    signatureAxiomSuppliesEinsteinDynamics : Bool
    signatureAxiomSuppliesEinsteinDynamicsIsFalse :
      signatureAxiomSuppliesEinsteinDynamics ≡ false

    currentAdapterPromotesGeneralRelativity : Bool
    currentAdapterPromotesGeneralRelativityIsFalse :
      currentAdapterPromotesGeneralRelativity ≡ false

open KernelGeometryBoundary public

canonicalKernelGeometryBoundary : KernelGeometryBoundary
canonicalKernelGeometryBoundary =
  kernelGeometryBoundary false refl false refl false refl false refl false refl
