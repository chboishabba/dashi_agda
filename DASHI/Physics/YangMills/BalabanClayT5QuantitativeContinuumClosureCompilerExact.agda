{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5QuantitativeContinuumClosureCompilerExact where

open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit
import DASHI.Physics.YangMills.BalabanClayT5OSGramTopologyExact as OS
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5QuantitativeTailMomentCompactnessExact as Quant

------------------------------------------------------------------------
-- Mature quantitative T5 data already supplies expectation convergence,
-- complete finite-family Gram convergence, moment/UI reductions and compactness
-- inputs.  This record contains only the remaining measure-level closure and
-- continuum-axiom laws needed to build the historical broad OS closure object.
------------------------------------------------------------------------

record PhysicalContinuumClosureAnalyticInputs
    (Measure Observable Scalar Marginal Schwinger : Set) : Set₂ where
  field
    quantitative :
      Quant.QuantitativeT5PhysicalInputs Measure Observable Scalar Marginal

    schwingerMap : Measure → Schwinger

    measureLimit : Limit.SequentialLimit Measure
    diagonalConvergesToContinuum :
      Limit.Converges measureLimit
        (T5.diagonalMeasure (Quant.expectationData quantitative))
        (T5.continuumMeasure
          (T5.thermodynamic (Quant.expectationData quantitative)))

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

    gramFiniteMeasureAgrees : ∀ cutoff →
      Gram.measureSequence
        (Gram.convergenceData (Quant.osGramData quantitative)) cutoff
      ≡ T5.diagonalMeasure (Quant.expectationData quantitative) cutoff

    gramContinuumMeasureAgrees :
      Gram.continuumMeasure
        (Gram.convergenceData (Quant.osGramData quantitative))
      ≡ T5.continuumMeasure
          (T5.thermodynamic (Quant.expectationData quantitative))

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
  { finiteMeasures =
      T5.diagonalMeasure (Quant.expectationData (quantitative inputs))
  ; continuumMeasure =
      T5.continuumMeasure
        (T5.thermodynamic (Quant.expectationData (quantitative inputs)))
  ; schwinger = schwingerMap inputs
  ; measureLimit = measureLimit inputs
  ; continuumIsLimit = diagonalConvergesToContinuum inputs
  ; Normalized = Normalized inputs
  ; Positive = Positive inputs
  ; GaugeInvariant = GaugeInvariant inputs
  ; ReflectionPositiveMeasure =
      OS.GramReflectionPositive
        (Gram.physicalMeasureTopologyControlsOSGram
          (Quant.osGramData (quantitative inputs)))
  ; EuclideanCovariant = EuclideanCovariant inputs
  ; ReflectionPositive = ReflectionPositive inputs
  ; Symmetric = Symmetric inputs
  ; Tempered = Tempered inputs
  ; Regular = Regular inputs
  ; Clustered = Clustered inputs
  ; finiteNormalized = finiteNormalized inputs
  ; finitePositive = finitePositive inputs
  ; finiteGaugeInvariant = finiteGaugeInvariant inputs
  ; finiteReflectionPositive = physicalFiniteGramReflectionPositive inputs
  ; normalizedClosed = normalizedClosed inputs
  ; positiveClosed = positiveClosed inputs
  ; gaugeInvariantClosed = gaugeInvariantClosed inputs
  ; reflectionPositiveClosed = gramReflectionClosedUnderMeasureLimit inputs
  ; continuumEuclideanCovariant = continuumEuclideanCovariant inputs
  ; continuumSymmetric = continuumSymmetric inputs
  ; continuumTempered = continuumTempered inputs
  ; continuumRegular = continuumRegular inputs
  ; continuumClustered = continuumClustered inputs
  ; measureReflectionImpliesSchwingerReflection =
      gramReflectionImpliesSchwingerReflection inputs
  }

quantitativeContinuumClosureCompilerLevel : ProofLevel
quantitativeContinuumClosureCompilerLevel = machineChecked

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
