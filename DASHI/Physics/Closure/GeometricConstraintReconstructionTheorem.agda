module DASHI.Physics.Closure.GeometricConstraintReconstructionTheorem where

-- Reconstruction boundary replacing an unrelated pre-bundled constraint law.
-- A model must reconstruct its canonical gauge/constraint package from the
-- forced contraction/quadratic/signature geometry, and prove that the
-- reconstructed package transports to the concrete constraint representation.
-- Closure is then derived by the existing checked package theorem.

open import Agda.Primitive using (Setω)

open import DASHI.Physics.Constraints.Closure using (ClosureLaw)
open import DASHI.Physics.Constraints.ConcreteInstance as CI
open import DASHI.Physics.Closure.CanonicalConstraintGaugePackage as CCGP
open import DASHI.Physics.Closure.ConstraintClosureFromCanonicalPackage as CCFP
open import DASHI.Physics.Closure.ContractionQuadraticToSignatureBridgeTheorem as CQSB

record GeometryConstraintReconstruction
  (geometry : CQSB.ContractionQuadraticToSignatureBridgeTheorem) : Setω where
  field
    reconstructPackage : CCGP.CanonicalConstraintGaugePackage
    reconstructionTransport :
      CCFP.ConstraintClosureTransport reconstructPackage

  reconstructedClosure : ClosureLaw CI.CS CI.L
  reconstructedClosure =
    CCFP.transportedClosureLaw reconstructPackage reconstructionTransport

closureFromForcedGeometryReconstruction :
  ∀ {geometry} →
  GeometryConstraintReconstruction geometry →
  ClosureLaw CI.CS CI.L
closureFromForcedGeometryReconstruction reconstruction =
  GeometryConstraintReconstruction.reconstructedClosure reconstruction

record CanonicalGeometricConstraintClosure : Setω where
  field
    forcedGeometry : CQSB.ContractionQuadraticToSignatureBridgeTheorem
    reconstruction : GeometryConstraintReconstruction forcedGeometry

  closureLaw : ClosureLaw CI.CS CI.L
  closureLaw = closureFromForcedGeometryReconstruction reconstruction

-- This theorem intentionally has no canonical inhabitant here.  Constructing
-- one requires the actual Hamiltonian/momentum generators and their gauge
-- representation to be reconstructed from the forced quadratic/cone geometry,
-- rather than imported independently.
record IntrinsicConstraintGeneratorDerivation
  (geometry : CQSB.ContractionQuadraticToSignatureBridgeTheorem) : Setω where
  field
    reconstructed : GeometryConstraintReconstruction geometry
    HamiltonianGeneratedFromGeometry : Set
    MomentumGeneratedFromGeometry : Set
    bracketsGeneratedFromGeometry : Set
    hamiltonianGeneratedFromGeometry : HamiltonianGeneratedFromGeometry
    momentumGeneratedFromGeometry : MomentumGeneratedFromGeometry
    bracketsGeneratedFromGeometry : bracketsGeneratedFromGeometry
