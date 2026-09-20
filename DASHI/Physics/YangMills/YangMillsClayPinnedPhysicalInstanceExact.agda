module DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalInstanceExact where

------------------------------------------------------------------------
-- INSPECTABLE PHYSICAL PROJECTIONS OF THE PINNED LITERAL CONSTRUCTION
------------------------------------------------------------------------

open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact as Physical
import DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalConstructionExact as Pinned
import DASHI.Physics.YangMills.YangMillsSIScalingEndpointExact as SI

pinnedPhysicalFiniteMeasure :
  ∀ {G X Cutoff Configuration Scalar Observable Position
      CurvaturePolynomial LocalOperator OPECoefficient StressTensor
      HilbertSpace Hamiltonian VacuumState}
    {S :
      Top.LiteralYangMillsSemantics
        (Physical.physicalLiteralCarriers
          G X Cutoff Configuration Scalar Observable Position
          CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          HilbertSpace Hamiltonian VacuumState)}
    (pinned :
      Pinned.PinnedYangMillsConstruction S)
    (group : G)
    (cutoff : Cutoff) →
  Physical.PhysicalFiniteYMMeasure Configuration Scalar
pinnedPhysicalFiniteMeasure pinned group cutoff =
  Pinned.finiteMeasure (Pinned.finite pinned) group cutoff

pinnedPhysicalFiniteDensity :
  ∀ {G X Cutoff Configuration Scalar Observable Position
      CurvaturePolynomial LocalOperator OPECoefficient StressTensor
      HilbertSpace Hamiltonian VacuumState}
    {S :
      Top.LiteralYangMillsSemantics
        (Physical.physicalLiteralCarriers
          G X Cutoff Configuration Scalar Observable Position
          CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          HilbertSpace Hamiltonian VacuumState)}
    (pinned :
      Pinned.PinnedYangMillsConstruction S)
    (group : G)
    (cutoff : Cutoff) →
  Configuration → Scalar
pinnedPhysicalFiniteDensity pinned group cutoff =
  Physical.density
    (pinnedPhysicalFiniteMeasure pinned group cutoff)

pinnedPhysicalFiniteExpectation :
  ∀ {G X Cutoff Configuration Scalar Observable Position
      CurvaturePolynomial LocalOperator OPECoefficient StressTensor
      HilbertSpace Hamiltonian VacuumState}
    {S :
      Top.LiteralYangMillsSemantics
        (Physical.physicalLiteralCarriers
          G X Cutoff Configuration Scalar Observable Position
          CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          HilbertSpace Hamiltonian VacuumState)}
    (pinned :
      Pinned.PinnedYangMillsConstruction S)
    (group : G)
    (cutoff : Cutoff) →
  (Configuration → Scalar) → Scalar
pinnedPhysicalFiniteExpectation pinned group cutoff =
  Physical.normalizedExpectation
    (pinnedPhysicalFiniteMeasure pinned group cutoff)

pinnedPhysicalContinuumMeasure :
  ∀ {G X Cutoff Configuration Scalar Observable Position
      CurvaturePolynomial LocalOperator OPECoefficient StressTensor
      HilbertSpace Hamiltonian VacuumState}
    {S :
      Top.LiteralYangMillsSemantics
        (Physical.physicalLiteralCarriers
          G X Cutoff Configuration Scalar Observable Position
          CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          HilbertSpace Hamiltonian VacuumState)}
    (pinned :
      Pinned.PinnedYangMillsConstruction S)
    (group : G) →
  Physical.PhysicalContinuumYMMeasure Observable Scalar
pinnedPhysicalContinuumMeasure pinned group =
  Pinned.continuumMeasure (Pinned.continuum pinned) group

pinnedPhysicalContinuumExpectation :
  ∀ {G X Cutoff Configuration Scalar Observable Position
      CurvaturePolynomial LocalOperator OPECoefficient StressTensor
      HilbertSpace Hamiltonian VacuumState}
    {S :
      Top.LiteralYangMillsSemantics
        (Physical.physicalLiteralCarriers
          G X Cutoff Configuration Scalar Observable Position
          CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          HilbertSpace Hamiltonian VacuumState)}
    (pinned :
      Pinned.PinnedYangMillsConstruction S)
    (group : G) →
  Observable → Scalar
pinnedPhysicalContinuumExpectation pinned group =
  Physical.expectation
    (pinnedPhysicalContinuumMeasure pinned group)

pinnedPhysicalSchwinger :
  ∀ {G X Cutoff Configuration Scalar Observable Position
      CurvaturePolynomial LocalOperator OPECoefficient StressTensor
      HilbertSpace Hamiltonian VacuumState}
    {S :
      Top.LiteralYangMillsSemantics
        (Physical.physicalLiteralCarriers
          G X Cutoff Configuration Scalar Observable Position
          CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          HilbertSpace Hamiltonian VacuumState)}
    (pinned :
      Pinned.PinnedYangMillsConstruction S)
    (group : G) →
  Observable → Position → Position → Scalar
pinnedPhysicalSchwinger pinned group =
  Physical.schwinger
    (Pinned.schwinger (Pinned.continuum pinned) group)

pinnedPhysicalSIMass :
  ∀ {G X Cutoff Configuration Observable Position
      CurvaturePolynomial LocalOperator OPECoefficient StressTensor
      HilbertSpace Hamiltonian VacuumState}
    {S :
      Top.LiteralYangMillsSemantics
        (Physical.physicalLiteralCarriers
          G X Cutoff Configuration ℚ Observable Position
          CurvaturePolynomial LocalOperator OPECoefficient StressTensor
          HilbertSpace Hamiltonian VacuumState)}
    (pinned :
      Pinned.PinnedYangMillsConstruction S)
    (group : G) →
  SI.SIIndexedQuantity ℚ SI.SI.Mass
pinnedPhysicalSIMass pinned group =
  SI.SIYangMillsMassGap.massGap
    (Pinned.pinnedSIMassGap pinned group)

physicalPinnedProjectionCompilerLevel : ProofLevel
physicalPinnedProjectionCompilerLevel = machineChecked
