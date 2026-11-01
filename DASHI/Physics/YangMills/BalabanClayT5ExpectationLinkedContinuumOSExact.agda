{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5ExpectationLinkedContinuumOSExact where

------------------------------------------------------------------------
-- EXPECTATION-LINKED FINITE-TO-CONTINUUM OS CARRIER
--
-- The preferred quantitative T5 producer already contains one continuum
-- measure and proves selected-diagonal expectation convergence to expectations
-- under that exact target.  The preferred OS-Gram compiler uses the same target
-- definitionally.  This carrier therefore records the continuum link at the
-- strength actually consumed downstream: convergence on a declared determining
-- bounded observable class, not a separately postulated weak convergence of
-- measures.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5OSGramTopologyExact as OS
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5PreferredOSGramFromExpectationExact as PreferredGram
import DASHI.Physics.YangMills.BalabanClayT5DirectExpectationPropertyClosureExact as Direct

record ExpectationLinkedFiniteToContinuumOS
    (Measure Observable Scalar Schwinger Action : Set) : Set₂ where
  field
    gramInputs :
      PreferredGram.PhysicalOSGramFromExpectationInputs
        Measure Observable Scalar

    scalarAuthority :
      Direct.ScalarExpectationClosureAuthority
        (PreferredGram.expectationData gramInputs)

    propertySemantics :
      Direct.SelectedExpectationPropertySemantics
        (PreferredGram.expectationData gramInputs)
        scalarAuthority Action

    -- The continuum link is test-class based.  Membership must imply the exact
    -- boundedness predicate consumed by the expectation producer.
    DeterminingObservable : Observable → Set
    determiningObservableBounded : ∀ observable →
      DeterminingObservable observable →
      T5.BoundedObservable
        (T5.thermodynamic (PreferredGram.expectationData gramInputs)) observable

    schwinger : Measure → Schwinger

    EuclideanCovariant ReflectionPositive Symmetric Tempered Regular Clustered :
      Schwinger → Set

    continuumEuclideanCovariant :
      EuclideanCovariant
        (schwinger
          (T5.continuumMeasure
            (T5.thermodynamic (PreferredGram.expectationData gramInputs))))

    continuumSymmetric :
      Symmetric
        (schwinger
          (T5.continuumMeasure
            (T5.thermodynamic (PreferredGram.expectationData gramInputs))))

    continuumTempered :
      Tempered
        (schwinger
          (T5.continuumMeasure
            (T5.thermodynamic (PreferredGram.expectationData gramInputs))))

    continuumRegular :
      Regular
        (schwinger
          (T5.continuumMeasure
            (T5.thermodynamic (PreferredGram.expectationData gramInputs))))

    continuumClustered :
      Clustered
        (schwinger
          (T5.continuumMeasure
            (T5.thermodynamic (PreferredGram.expectationData gramInputs))))

    gramReflectionImpliesSchwingerReflection : ∀ measure →
      OS.GramReflectionPositive
        (Gram.physicalMeasureTopologyControlsOSGram
          (PreferredGram.compilePhysicalMeasureToOSGramData gramInputs)) measure →
      ReflectionPositive (schwinger measure)

open ExpectationLinkedFiniteToContinuumOS public

expectationData :
  ∀ {Measure Observable Scalar Schwinger Action} →
  ExpectationLinkedFiniteToContinuumOS
    Measure Observable Scalar Schwinger Action →
  T5.PhysicalExpectationProducerData Measure Observable Scalar
expectationData closure = PreferredGram.expectationData (gramInputs closure)

finiteMeasures :
  ∀ {Measure Observable Scalar Schwinger Action} →
  ExpectationLinkedFiniteToContinuumOS
    Measure Observable Scalar Schwinger Action →
  Nat → Measure
finiteMeasures closure = T5.diagonalMeasure (expectationData closure)

continuumMeasure :
  ∀ {Measure Observable Scalar Schwinger Action} →
  ExpectationLinkedFiniteToContinuumOS
    Measure Observable Scalar Schwinger Action → Measure
continuumMeasure closure =
  T5.continuumMeasure (T5.thermodynamic (expectationData closure))

selectedDeterminingExpectationConverges :
  ∀ {Measure Observable Scalar Schwinger Action}
    (closure : ExpectationLinkedFiniteToContinuumOS
      Measure Observable Scalar Schwinger Action)
    observable →
  DeterminingObservable closure observable →
  Gram.Converges (T5.scalarConvergence (T5.thermodynamic (expectationData closure)))
    (λ cutoff →
      Gram.expectation (T5.operations (T5.thermodynamic (expectationData closure)))
        (finiteMeasures closure cutoff) observable)
    (Gram.expectation (T5.operations (T5.thermodynamic (expectationData closure)))
      (continuumMeasure closure) observable)
selectedDeterminingExpectationConverges closure observable determining =
  Direct.boundedSelectedExpectationConverges
    (expectationData closure) observable
    (determiningObservableBounded closure observable determining)

continuumNormalized :
  ∀ {Measure Observable Scalar Schwinger Action}
    (closure : ExpectationLinkedFiniteToContinuumOS
      Measure Observable Scalar Schwinger Action) →
  Direct.ContinuumNormalized (propertySemantics closure)
continuumNormalized closure =
  Direct.continuumNormalizedFromSelectedExpectations (propertySemantics closure)

continuumPositive :
  ∀ {Measure Observable Scalar Schwinger Action}
    (closure : ExpectationLinkedFiniteToContinuumOS
      Measure Observable Scalar Schwinger Action) →
  Direct.ContinuumPositive (propertySemantics closure)
continuumPositive closure =
  Direct.continuumPositiveFromSelectedExpectations (propertySemantics closure)

continuumActionInvariant :
  ∀ {Measure Observable Scalar Schwinger Action}
    (closure : ExpectationLinkedFiniteToContinuumOS
      Measure Observable Scalar Schwinger Action) →
  Direct.ContinuumActionInvariant (propertySemantics closure)
continuumActionInvariant closure =
  Direct.continuumActionInvariantFromSelectedExpectations (propertySemantics closure)

continuumGramReflectionPositive :
  ∀ {Measure Observable Scalar Schwinger Action}
    (closure : ExpectationLinkedFiniteToContinuumOS
      Measure Observable Scalar Schwinger Action) →
  OS.GramReflectionPositive
    (Gram.physicalMeasureTopologyControlsOSGram
      (PreferredGram.compilePhysicalMeasureToOSGramData (gramInputs closure)))
    (continuumMeasure closure)
continuumGramReflectionPositive closure =
  subst
    (OS.GramReflectionPositive
      (Gram.physicalMeasureTopologyControlsOSGram
        (PreferredGram.compilePhysicalMeasureToOSGramData (gramInputs closure))))
    (PreferredGram.compiledGramContinuumMeasureIsExpectationContinuum
      (gramInputs closure))
    (Gram.physicalContinuumReflectionPositive
      (PreferredGram.compilePhysicalMeasureToOSGramData (gramInputs closure)))

continuumReflectionPositive :
  ∀ {Measure Observable Scalar Schwinger Action}
    (closure : ExpectationLinkedFiniteToContinuumOS
      Measure Observable Scalar Schwinger Action) →
  ReflectionPositive closure (schwinger closure (continuumMeasure closure))
continuumReflectionPositive closure =
  gramReflectionImpliesSchwingerReflection closure
    (continuumMeasure closure)
    (continuumGramReflectionPositive closure)

record ExpectationLinkedContinuumOSAxioms
    {Measure Observable Scalar Schwinger Action : Set}
    (closure : ExpectationLinkedFiniteToContinuumOS
      Measure Observable Scalar Schwinger Action) : Set₁ where
  field
    normalized : Direct.ContinuumNormalized (propertySemantics closure)
    positive : Direct.ContinuumPositive (propertySemantics closure)
    actionInvariant : Direct.ContinuumActionInvariant (propertySemantics closure)
    euclideanCovariant :
      EuclideanCovariant closure (schwinger closure (continuumMeasure closure))
    reflectionPositive :
      ReflectionPositive closure (schwinger closure (continuumMeasure closure))
    symmetric : Symmetric closure (schwinger closure (continuumMeasure closure))
    tempered : Tempered closure (schwinger closure (continuumMeasure closure))
    regular : Regular closure (schwinger closure (continuumMeasure closure))
    clustered : Clustered closure (schwinger closure (continuumMeasure closure))

open ExpectationLinkedContinuumOSAxioms public

assembleExpectationLinkedContinuumOSAxioms :
  ∀ {Measure Observable Scalar Schwinger Action}
    (closure : ExpectationLinkedFiniteToContinuumOS
      Measure Observable Scalar Schwinger Action) →
  ExpectationLinkedContinuumOSAxioms closure
assembleExpectationLinkedContinuumOSAxioms closure = record
  { normalized = continuumNormalized closure
  ; positive = continuumPositive closure
  ; actionInvariant = continuumActionInvariant closure
  ; euclideanCovariant = continuumEuclideanCovariant closure
  ; reflectionPositive = continuumReflectionPositive closure
  ; symmetric = continuumSymmetric closure
  ; tempered = continuumTempered closure
  ; regular = continuumRegular closure
  ; clustered = continuumClustered closure
  }

expectationLinkedContinuumOSCarrierLevel : ProofLevel
expectationLinkedContinuumOSCarrierLevel = machineChecked

expectationLinkedContinuumOSAxiomAssemblyLevel : ProofLevel
expectationLinkedContinuumOSAxiomAssemblyLevel = machineChecked

-- This replaces global measure compactness on the preferred producer route by
-- the exact representation fact actually consumed: the determining continuum
-- observables are among the selected bounded tests whose expectations converge.
selectedDeterminingBoundedTestMeaningLevel : ProofLevel
selectedDeterminingBoundedTestMeaningLevel = conditional

gramToSchwingerReflectionMeaningLevel : ProofLevel
gramToSchwingerReflectionMeaningLevel = conditional
