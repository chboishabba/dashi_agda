{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5QuantitativeContinuumClosureCompilerExact where

------------------------------------------------------------------------
-- QUANTITATIVE T5 DATA -> FINITE-TO-CONTINUUM OS CLOSURE
--
-- The repository already owns the finite-family OS Gram convergence compiler,
-- tail-controlled expectation convergence, moment/UI reductions and a typed
-- compactness surface.  None of those facts by themselves inhabits the broad
-- historical FiniteToContinuumOSClosure record.
--
-- This module removes the accidental duplication.  The finite measure sequence
-- and continuum candidate are taken definitionally from the existing
-- PhysicalExpectationProducerData.  Reflection positivity is taken from the
-- existing complete OS-Gram carrier, rather than introduced as a fresh
-- unrelated predicate.  What remains primitive is exactly the real-analysis
-- measure-limit theorem, sequential closure of the physical measure properties,
-- the Gram/measure same-object weld, and the continuum Schwinger axioms.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit
import DASHI.Physics.YangMills.BalabanClayT5OSGramTopologyExact as OS
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5QuantitativeTailMomentCompactnessExact as Quant

record PhysicalContinuumClosureAnalyticInputs
    (Measure Observable Scalar Marginal Schwinger : Set) : Set₂ where
  field
    quantitative :
      Quant.QuantitativeT5PhysicalInputs Measure Observable Scalar Marginal

    schwingerMap : Measure → Schwinger

    -- The actual measure-level continuum theorem.  Expectation convergence and
    -- marginal compactness are already represented inside `quantitative`; this
    -- field is the missing promotion from those local/compactness facts to the
    -- selected diagonal measure sequence converging to the selected continuum
    -- measure in one declared measure topology.
    measureLimit : Limit.SequentialLimit Measure
    diagonalConvergesToContinuum :
      Limit.Converges measureLimit
        (T5.diagonalMeasure (Quant.expectationData quantitative))
        (T5.continuumMeasure
          (T5.thermodynamic (Quant.expectationData quantitative)))

    -- Physical measure properties which must survive that same topology.
    Normalized Positive GaugeInvariant : Measure → Set

    finiteNormalized : ∀ cutoff →
      Normalized (T5.diagonalMeasure
        (Quant.expectationData quantitative) cutoff)
    finitePositive : ∀ cutoff →
      Positive (T5.diagonalMeasure
        (Quant.expectationData quantitative) cutoff)
    finiteGaugeInvariant : ∀ cutoff →
      GaugeInvariant (T5.diagonalMeasure
        (Quant.expectationData quantitative) cutoff)

    normalizedClosed : ∀ sequence target →
      Limit.Converges measureLimit sequence target →
      (∀ cutoff → Normalized (sequence cutoff)) → Normalized target
    positiveClosed : ∀ sequence target →
      Limit.Converges measureLimit sequence target →
      (∀ cutoff → Positive (sequence cutoff)) → Positive target
    gaugeInvariantClosed : ∀ sequence target →
      Limit.Converges measureLimit sequence target →
      (∀ cutoff → GaugeInvariant (sequence cutoff)) → GaugeInvariant target

    -- Same-object weld between the complete OS-Gram sequence and the selected
    -- quantitative diagonal measure sequence.  This is stronger and safer than
    -- an untyped `osGramUsesExpectationProducer : Set` receipt.
    gramFiniteMeasureAgrees : ∀ cutoff →
      Gram.measureSequence
        (Gram.convergenceData (Quant.osGramData quantitative)) cutoff
      ≡ T5.diagonalMeasure (Quant.expectationData quantitative) cutoff

    gramContinuumMeasureAgrees :
      Gram.continuumMeasure
        (Gram.convergenceData (Quant.osGramData quantitative))
      ≡ T5.continuumMeasure
          (T5.thermodynamic (Quant.expectationData quantitative))

    -- The complete reflected-Gram positivity predicate must itself be closed
    -- under the selected measure topology.  Complete finite-family Gram
    -- convergence is already machine-compiled upstream; this is the remaining
    -- measure-topology compatibility theorem.
    gramReflectionClosedUnderMeasureLimit : ∀ sequence target →
      Limit.Converges measureLimit sequence target →
      (∀ cutoff →
        OS.GramReflectionPositive
          (Gram.physicalMeasureTopologyControlsOSGram
            (Quant.osGramData quantitative))
          (sequence cutoff)) →
      OS.GramReflectionPositive
        (Gram.physicalMeasureTopologyControlsOSGram
          (Quant.osGramData quantitative)) target

    -- Continuum Schwinger-side axioms not manufactured by measure compactness.
    EuclideanCovariant ReflectionPositive Symmetric Tempered Regular Clustered :
      Schwinger → Set

    continuumEuclideanCovariant :
      EuclideanCovariant
        (schwingerMap
          (T5.continuumMeasure
            (T5.thermodynamic (Quant.expectationData quantitative))))
    continuumSymmetric :
      Symmetric
        (schwingerMap
          (T5.continuumMeasure
            (T5.thermodynamic (Quant.expectationData quantitative))))
    continuumTempered :
      Tempered
        (schwingerMap
          (T5.continuumMeasure
            (T5.thermodynamic (Quant.expectationData quantitative))))
    continuumRegular :
      Regular
        (schwingerMap
          (T5.continuumMeasure
            (T5.thermodynamic (Quant.expectationData quantitative))))
    continuumClustered :
      Clustered
        (schwingerMap
          (T5.continuumMeasure
            (T5.thermodynamic (Quant.expectationData quantitative))))

    gramReflectionImpliesSchwingerReflection : ∀ measure →
      OS.GramReflectionPositive
        (Gram.physicalMeasureTopologyControlsOSGram
          (Quant.osGramData quantitative)) measure →
      ReflectionPositive (schwingerMap measure)

open PhysicalContinuumClosureAnalyticInputs public

gramTopology :
  ∀ {Measure Observable Scalar Marginal Schwinger} →
  PhysicalContinuumClosureAnalyticInputs
    Measure Observable Scalar Marginal Schwinger →
  OS.OSGramLimitData Measure
    (Gram.TestFamily ∘ Quant.osGramData ∘ quantitative) Scalar
gramTopology inputs =
  Gram.physicalMeasureTopologyControlsOSGram
    (Quant.osGramData (quantitative inputs))

-- Use an eta-expanded result type here to avoid introducing any alternative
-- physical carrier; this is exactly the upstream complete Gram object.
physicalFiniteGramReflectionPositive :
  ∀ {Measure Observable Scalar Marginal Schwinger}
    (inputs : PhysicalContinuumClosureAnalyticInputs
      Measure Observable Scalar Marginal Schwinger)
    cutoff →
  OS.GramReflectionPositive
    (Gram.physicalMeasureTopologyControlsOSGram
      (Quant.osGramData (quantitative inputs)))
    (T5.diagonalMeasure
      (Quant.expectationData (quantitative inputs)) cutoff)
physicalFiniteGramReflectionPositive inputs cutoff =
  subst
    (OS.GramReflectionPositive
      (Gram.physicalMeasureTopologyControlsOSGram
        (Quant.osGramData (quantitative inputs))))
    (gramFiniteMeasureAgrees inputs cutoff)
    (λ family →
      OS.finiteGramNonnegative
        (Gram.physicalMeasureTopologyControlsOSGram
          (Quant.osGramData (quantitative inputs))) cutoff family)

physicalContinuumGramReflectionPositive :
  ∀ {Measure Observable Scalar Marginal Schwinger}
    (inputs : PhysicalContinuumClosureAnalyticInputs
      Measure Observable Scalar Marginal Schwinger) →
  OS.GramReflectionPositive
    (Gram.physicalMeasureTopologyControlsOSGram
      (Quant.osGramData (quantitative inputs)))
    (T5.continuumMeasure
      (T5.thermodynamic (Quant.expectationData (quantitative inputs))))
physicalContinuumGramReflectionPositive inputs =
  subst
    (OS.GramReflectionPositive
      (Gram.physicalMeasureTopologyControlsOSGram
        (Quant.osGramData (quantitative inputs))))
    (gramContinuumMeasureAgrees inputs)
    (Gram.physicalContinuumReflectionPositive
      (Quant.osGramData (quantitative inputs)))

compileFiniteToContinuumOSClosure :
  ∀ {Measure Observable Scalar Marginal Schwinger} →
  PhysicalContinuumClosureAnalyticInputs
    Measure Observable Scalar Marginal Schwinger →
  Limit.FiniteToContinuumOSClosure Measure Schwinger
compileFiniteToContinuumOSClosure inputs = record
  { Limit.FiniteToContinuumOSClosure.finiteMeasures =
      T5.diagonalMeasure (Quant.expectationData (quantitative inputs))
  ; Limit.FiniteToContinuumOSClosure.continuumMeasure =
      T5.continuumMeasure
        (T5.thermodynamic (Quant.expectationData (quantitative inputs)))
  ; Limit.FiniteToContinuumOSClosure.schwinger = schwingerMap inputs
  ; Limit.FiniteToContinuumOSClosure.measureLimit = measureLimit inputs
  ; Limit.FiniteToContinuumOSClosure.continuumIsLimit =
      diagonalConvergesToContinuum inputs
  ; Limit.FiniteToContinuumOSClosure.Normalized = Normalized inputs
  ; Limit.FiniteToContinuumOSClosure.Positive = Positive inputs
  ; Limit.FiniteToContinuumOSClosure.GaugeInvariant = GaugeInvariant inputs
  ; Limit.FiniteToContinuumOSClosure.ReflectionPositiveMeasure =
      OS.GramReflectionPositive
        (Gram.physicalMeasureTopologyControlsOSGram
          (Quant.osGramData (quantitative inputs)))
  ; Limit.FiniteToContinuumOSClosure.EuclideanCovariant =
      EuclideanCovariant inputs
  ; Limit.FiniteToContinuumOSClosure.ReflectionPositive =
      ReflectionPositive inputs
  ; Limit.FiniteToContinuumOSClosure.Symmetric = Symmetric inputs
  ; Limit.FiniteToContinuumOSClosure.Tempered = Tempered inputs
  ; Limit.FiniteToContinuumOSClosure.Regular = Regular inputs
  ; Limit.FiniteToContinuumOSClosure.Clustered = Clustered inputs
  ; Limit.FiniteToContinuumOSClosure.finiteNormalized = finiteNormalized inputs
  ; Limit.FiniteToContinuumOSClosure.finitePositive = finitePositive inputs
  ; Limit.FiniteToContinuumOSClosure.finiteGaugeInvariant =
      finiteGaugeInvariant inputs
  ; Limit.FiniteToContinuumOSClosure.finiteReflectionPositive =
      physicalFiniteGramReflectionPositive inputs
  ; Limit.FiniteToContinuumOSClosure.normalizedClosed = normalizedClosed inputs
  ; Limit.FiniteToContinuumOSClosure.positiveClosed = positiveClosed inputs
  ; Limit.FiniteToContinuumOSClosure.gaugeInvariantClosed =
      gaugeInvariantClosed inputs
  ; Limit.FiniteToContinuumOSClosure.reflectionPositiveClosed =
      gramReflectionClosedUnderMeasureLimit inputs
  ; Limit.FiniteToContinuumOSClosure.continuumEuclideanCovariant =
      continuumEuclideanCovariant inputs
  ; Limit.FiniteToContinuumOSClosure.continuumSymmetric =
      continuumSymmetric inputs
  ; Limit.FiniteToContinuumOSClosure.continuumTempered =
      continuumTempered inputs
  ; Limit.FiniteToContinuumOSClosure.continuumRegular =
      continuumRegular inputs
  ; Limit.FiniteToContinuumOSClosure.continuumClustered =
      continuumClustered inputs
  ; Limit.FiniteToContinuumOSClosure.measureReflectionImpliesSchwingerReflection =
      gramReflectionImpliesSchwingerReflection inputs
  }

quantitativeContinuumClosureCompilerLevel : ProofLevel
quantitativeContinuumClosureCompilerLevel = machineChecked

-- These are now the actual analytic source classes above the mature quantitative
-- T5 machinery.  They remain conditional until literal physical inhabitants are
-- supplied; the compiler does not manufacture them.
physicalMeasureLimitConvergenceLevel : ProofLevel
physicalMeasureLimitConvergenceLevel = conditional

physicalMeasurePropertySequentialClosureLevel : ProofLevel
physicalMeasurePropertySequentialClosureLevel = conditional

physicalGramMeasureSameObjectLevel : ProofLevel
physicalGramMeasureSameObjectLevel = conditional

physicalGramReflectionMeasureTopologyClosureLevel : ProofLevel
physicalGramReflectionMeasureTopologyClosureLevel = conditional

physicalContinuumSchwingerAxiomInputsLevel : ProofLevel
physicalContinuumSchwingerAxiomInputsLevel = conditional
