module DASHI.Physics.Plasma.LoureiroKREHMHermiteEquationDepthExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

-- Deep source-shaped coordinate owner for Viriato/KREHM.
-- Exact continuous equations remain source-owned; this file encodes their
-- operator structure, Hermite coupling and closure obligations without claiming
-- a full analytic rederivation in DASHI.

data KREHMField : Set where
  electrostaticPotential
  parallelVectorPotential
  electronDensity
  parallelElectronFlow
  reducedElectronDistribution
  : KREHMField

data KREHMOperator : Set where
  perpendicularPoissonBracket
  parallelDerivative
  perpendicularLaplacian
  resistiveDiffusion
  electronInertia
  HermiteStreamingUp
  HermiteStreamingDown
  collisions
  : KREHMOperator

record RMHDLimitEquation : Set where
  constructor rmhd-limit-equation
  field
    lhs : String
    rhs : String
    sourceReference : String

open RMHDLimitEquation public

rmhdVorticity : RMHDLimitEquation
rmhdVorticity = rmhd-limit-equation
  "d_t nabla_perp^2 Phi + [Phi,nabla_perp^2 Phi]"
  "v_A d_z nabla_perp^2 Psi + [Psi,nabla_perp^2 Psi]"
  "Viriato Eq. 15"

rmhdFlux : RMHDLimitEquation
rmhdFlux = rmhd-limit-equation
  "d_t Psi + [Phi,Psi]"
  "eta nabla_perp^2 Psi + v_A d_z Phi"
  "Viriato Eq. 16"

record HermiteHierarchyShape : Set where
  constructor hermite-hierarchy-shape
  field
    coefficient : String
    lowerNeighbourCoupling : String
    upperNeighbourCoupling : String
    collisionalDamping : String
    hierarchyStartsAt : String
    sourceReference : String

open HermiteHierarchyShape public

kreHmHermiteHierarchy : HermiteHierarchyShape
kreHmHermiteHierarchy = hermite-hierarchy-shape
  "g_m"
  "parallel streaming couples g_m to g_(m-1)"
  "parallel streaming couples g_m to g_(m+1)"
  "collision operator damps high-m moments"
  "KREHM reduced distribution hierarchy after low moments are separated"
  "Viriato Sec. 2.1.1 and Sec. 3"

record HermiteClosureReceipt : Set where
  constructor hermite-closure-receipt
  field
    retainedHighestMoment : String
    missingNextMoment : String
    closureRequirement : String
    asymptoticCondition : String
    neglectedTermsReading : String

open HermiteClosureReceipt public

canonicalHermiteClosure : HermiteClosureReceipt
canonicalHermiteClosure = hermite-closure-receipt
  "M"
  "g_(M+1)"
  "numerics require a prescription for g_(M+1) after truncating the exactly equivalent infinite Hermite hierarchy"
  "choose M large enough that g_M lies in the collisional/Hermite dissipation range"
  "then omitted energy-balance terms are expected to be exponentially small"

record KREHMDepthBoundary : Set where
  constructor krehm-depth-boundary
  field
    infiniteHermiteExpansionLosesInformation : Bool
    infiniteHermiteExpansionLosesInformationIsFalse : infiniteHermiteExpansionLosesInformation ≡ false
    finiteMomentTruncationRequiresClosure : Bool
    finiteMomentTruncationRequiresClosureIsTrue : finiteMomentTruncationRequiresClosure ≡ true
    RMHDLimitIsFullKREHM : Bool
    RMHDLimitIsFullKREHMIsFalse : RMHDLimitIsFullKREHM ≡ false
    tearingBenchmarkAtEtaZeroStillCanReconnectViaElectronInertia : Bool
    tearingBenchmarkAtEtaZeroStillCanReconnectViaElectronInertiaIsTrue : tearingBenchmarkAtEtaZeroStillCanReconnectViaElectronInertia ≡ true

canonicalKREHMDepthBoundary : KREHMDepthBoundary
canonicalKREHMDepthBoundary = krehm-depth-boundary false refl true refl false refl true refl

data KREHMReverseTarget : Set where
  acquireNormalization
  acquireFullKREHMEquationSet
  acquireHermiteBasisConvention
  acquireClosureFormula
  acquireCollisionOperator
  acquireEnergyBalance
  acquireTearingBenchmarkParameters
  : KREHMReverseTarget
