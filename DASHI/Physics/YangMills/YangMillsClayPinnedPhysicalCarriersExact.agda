module DASHI.Physics.YangMills.YangMillsClayPinnedPhysicalCarriersExact where

------------------------------------------------------------------------
-- CONCRETE PHYSICAL CARRIERS FOR THE LITERAL CLAY OBJECT
--
-- The preferred literal carriers are not opaque measure/schwinger Sets:
--
--   FiniteMeasure    = normalized-Haar density data
--   ContinuumMeasure = actual continuum expectation functional
--   SchwingerFamily  = actual correlation functional
--
-- Hence the physical objects are chosen before the Clay semantics/predicates.
------------------------------------------------------------------------

open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top

record PhysicalFiniteYMMeasure
    (Configuration Scalar : Set) : Set where
  constructor physicalFiniteMeasure
  field
    density : Configuration → Scalar

    -- Product-Haar / constrained-Haar integration on the actual finite
    -- configuration carrier.  The weighted Eq.(1.71) refinement lane is the
    -- intended producer.
    haarIntegral : (Configuration → Scalar) → Scalar

    multiply divide : Scalar → Scalar → Scalar

    partitionFunction : Scalar

open PhysicalFiniteYMMeasure public

normalizedExpectation :
  ∀ {Configuration Scalar} →
  PhysicalFiniteYMMeasure Configuration Scalar →
  (Configuration → Scalar) → Scalar
normalizedExpectation measure observable =
  divide measure
    (haarIntegral measure
      (λ configuration →
        multiply measure
          (density measure configuration)
          (observable configuration)))
    (partitionFunction measure)

record PhysicalContinuumYMMeasure
    (Observable Scalar : Set) : Set where
  constructor physicalContinuumMeasure
  field
    expectation : Observable → Scalar

open PhysicalContinuumYMMeasure public

record PhysicalSchwingerFamily
    (Observable Position Scalar : Set) : Set where
  constructor physicalSchwingerFamily
  field
    schwinger :
      Observable → Position → Position → Scalar

open PhysicalSchwingerFamily public

------------------------------------------------------------------------
-- Literal carrier constructor.
------------------------------------------------------------------------

physicalLiteralCarriers :
  (CompactSimpleGroup
   Spacetime
   Cutoff
   Configuration
   Scalar
   Observable
   Position
   CurvaturePolynomial
   LocalOperator
   OPECoefficient
   StressTensor
   HilbertSpace
   Hamiltonian
   VacuumState : Set) →
  Top.LiteralYangMillsCarriers
physicalLiteralCarriers
  CompactSimpleGroup
  Spacetime
  Cutoff
  Configuration
  Scalar
  Observable
  Position
  CurvaturePolynomial
  LocalOperator
  OPECoefficient
  StressTensor
  HilbertSpace
  Hamiltonian
  VacuumState = record
  { Top.LiteralYangMillsCarriers.CompactSimpleGroup =
      CompactSimpleGroup
  ; Top.LiteralYangMillsCarriers.Spacetime =
      Spacetime
  ; Top.LiteralYangMillsCarriers.Cutoff =
      Cutoff
  ; Top.LiteralYangMillsCarriers.FiniteMeasure =
      PhysicalFiniteYMMeasure Configuration Scalar
  ; Top.LiteralYangMillsCarriers.ContinuumMeasure =
      PhysicalContinuumYMMeasure Observable Scalar
  ; Top.LiteralYangMillsCarriers.SchwingerFamily =
      PhysicalSchwingerFamily Observable Position Scalar
  ; Top.LiteralYangMillsCarriers.Observable =
      Observable
  ; Top.LiteralYangMillsCarriers.Position =
      Position
  ; Top.LiteralYangMillsCarriers.CurvaturePolynomial =
      CurvaturePolynomial
  ; Top.LiteralYangMillsCarriers.LocalOperator =
      LocalOperator
  ; Top.LiteralYangMillsCarriers.OPECoefficient =
      OPECoefficient
  ; Top.LiteralYangMillsCarriers.StressTensor =
      StressTensor
  ; Top.LiteralYangMillsCarriers.HilbertSpace =
      HilbertSpace
  ; Top.LiteralYangMillsCarriers.Hamiltonian =
      Hamiltonian
  ; Top.LiteralYangMillsCarriers.VacuumState =
      VacuumState
  }

------------------------------------------------------------------------
-- Convenience projections: the finite/continuum/schwinger meanings are now
-- literal data, not semantic postulates.
------------------------------------------------------------------------

literalFiniteDensity :
  ∀ {G X Cutoff Configuration Scalar Observable Position
      CurvaturePolynomial LocalOperator OPECoefficient StressTensor
      HilbertSpace Hamiltonian VacuumState} →
  Top.FiniteMeasure
    (physicalLiteralCarriers
      G X Cutoff Configuration Scalar Observable Position
      CurvaturePolynomial LocalOperator OPECoefficient StressTensor
      HilbertSpace Hamiltonian VacuumState) →
  Configuration → Scalar
literalFiniteDensity = density

literalFiniteExpectation :
  ∀ {G X Cutoff Configuration Scalar Observable Position
      CurvaturePolynomial LocalOperator OPECoefficient StressTensor
      HilbertSpace Hamiltonian VacuumState} →
  Top.FiniteMeasure
    (physicalLiteralCarriers
      G X Cutoff Configuration Scalar Observable Position
      CurvaturePolynomial LocalOperator OPECoefficient StressTensor
      HilbertSpace Hamiltonian VacuumState) →
  (Configuration → Scalar) → Scalar
literalFiniteExpectation = normalizedExpectation

literalContinuumExpectation :
  ∀ {G X Cutoff Configuration Scalar Observable Position
      CurvaturePolynomial LocalOperator OPECoefficient StressTensor
      HilbertSpace Hamiltonian VacuumState} →
  Top.ContinuumMeasure
    (physicalLiteralCarriers
      G X Cutoff Configuration Scalar Observable Position
      CurvaturePolynomial LocalOperator OPECoefficient StressTensor
      HilbertSpace Hamiltonian VacuumState) →
  Observable → Scalar
literalContinuumExpectation = expectation

literalSchwingerCorrelation :
  ∀ {G X Cutoff Configuration Scalar Observable Position
      CurvaturePolynomial LocalOperator OPECoefficient StressTensor
      HilbertSpace Hamiltonian VacuumState} →
  Top.SchwingerFamily
    (physicalLiteralCarriers
      G X Cutoff Configuration Scalar Observable Position
      CurvaturePolynomial LocalOperator OPECoefficient StressTensor
      HilbertSpace Hamiltonian VacuumState) →
  Observable → Position → Position → Scalar
literalSchwingerCorrelation = schwinger

physicalLiteralCarrierConstructionLevel : ProofLevel
physicalLiteralCarrierConstructionLevel = machineChecked

physicalFiniteMeasureMeaningLevel : ProofLevel
physicalFiniteMeasureMeaningLevel = machineChecked

physicalContinuumMeasureMeaningLevel : ProofLevel
physicalContinuumMeasureMeaningLevel = machineChecked

physicalSchwingerMeaningLevel : ProofLevel
physicalSchwingerMeaningLevel = machineChecked
