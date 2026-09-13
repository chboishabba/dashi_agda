{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5PreferredOSGramFromExpectationExact where

------------------------------------------------------------------------
-- PREFERRED T5 OS-GRAM CONSTRUCTION FROM THE EXPECTATION PRODUCER
--
-- The mature T5 expectation producer already fixes the selected diagonal
-- measure sequence and continuum candidate.  Therefore the preferred OS-Gram
-- object should be constructed from that producer rather than chosen
-- independently and welded back afterwards.
--
-- On this route the Gram carrier's finite measures and continuum measure are
-- definitionally the same physical objects consumed by the quantitative
-- continuum closure compiler.  No post-hoc same-object theorem is required.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5

record PhysicalOSGramFromExpectationInputs
    (Measure Observable Scalar : Set) : Set₂ where
  field
    expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar

    TestFamily : Set
    decodeFamily : TestFamily →
      Gram.PhysicalOSFiniteTestFamily Observable Scalar

    admissibleFamily : ∀ family →
      Gram.AdmissiblePhysicalTestFamily
        (T5.physicalMeasureConvergenceDataFromProducer expectationData)
        (decodeFamily family)

    Nonnegative : Scalar → Set

    finiteGramNonnegative : ∀ cutoff family →
      Nonnegative
        (Gram.physicalReflectedGramQuadraticForm
          (Gram.operations
            (T5.physicalMeasureConvergenceDataFromProducer expectationData))
          (Gram.measureSequence
            (T5.physicalMeasureConvergenceDataFromProducer expectationData)
            cutoff)
          (decodeFamily family))

    nonnegativeConeClosed : ∀ sequence target →
      Gram.Converges
        (Gram.scalarConvergence
          (T5.physicalMeasureConvergenceDataFromProducer expectationData))
        sequence target →
      (∀ cutoff → Nonnegative (sequence cutoff)) →
      Nonnegative target

open PhysicalOSGramFromExpectationInputs public

compilePhysicalMeasureToOSGramData :
  ∀ {Measure Observable Scalar} →
  PhysicalOSGramFromExpectationInputs Measure Observable Scalar →
  Gram.PhysicalMeasureToOSGramData Measure Observable Scalar
compilePhysicalMeasureToOSGramData inputs = record
  { Gram.PhysicalMeasureToOSGramData.convergenceData =
      T5.physicalMeasureConvergenceDataFromProducer (expectationData inputs)
  ; Gram.PhysicalMeasureToOSGramData.TestFamily = TestFamily inputs
  ; Gram.PhysicalMeasureToOSGramData.decodeFamily = decodeFamily inputs
  ; Gram.PhysicalMeasureToOSGramData.admissibleFamily = admissibleFamily inputs
  ; Gram.PhysicalMeasureToOSGramData.Nonnegative = Nonnegative inputs
  ; Gram.PhysicalMeasureToOSGramData.finiteGramNonnegative =
      finiteGramNonnegative inputs
  ; Gram.PhysicalMeasureToOSGramData.nonnegativeConeClosed =
      nonnegativeConeClosed inputs
  }

compiledGramFiniteMeasureIsDiagonal :
  ∀ {Measure Observable Scalar}
    (inputs : PhysicalOSGramFromExpectationInputs
      Measure Observable Scalar)
    cutoff →
  Gram.measureSequence
    (Gram.convergenceData (compilePhysicalMeasureToOSGramData inputs)) cutoff
  ≡ T5.diagonalMeasure (expectationData inputs) cutoff
compiledGramFiniteMeasureIsDiagonal inputs cutoff = refl

compiledGramContinuumMeasureIsExpectationContinuum :
  ∀ {Measure Observable Scalar}
    (inputs : PhysicalOSGramFromExpectationInputs
      Measure Observable Scalar) →
  Gram.continuumMeasure
    (Gram.convergenceData (compilePhysicalMeasureToOSGramData inputs))
  ≡ T5.continuumMeasure (T5.thermodynamic (expectationData inputs))
compiledGramContinuumMeasureIsExpectationContinuum inputs = refl

physicalOSGramFromExpectationCompilerLevel : ProofLevel
physicalOSGramFromExpectationCompilerLevel = machineChecked

physicalGramMeasureSameObjectCompilerLevel : ProofLevel
physicalGramMeasureSameObjectCompilerLevel = machineChecked

-- The surviving physical inputs are the admissible finite test-family
-- realization and finite-cutoff Gram positivity/nonnegative-cone closure.
-- They do not include a separate measure-sequence identity payment.
physicalOSGramAdmissibilityInputsLevel : ProofLevel
physicalOSGramAdmissibilityInputsLevel = conditional

physicalFiniteGramPositivityInputsLevel : ProofLevel
physicalFiniteGramPositivityInputsLevel = conditional
