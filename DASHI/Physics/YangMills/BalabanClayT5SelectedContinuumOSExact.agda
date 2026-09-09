{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5SelectedContinuumOSExact where

------------------------------------------------------------------------
-- SELECTED FINITE-TO-CONTINUUM OS CARRIER
--
-- This is the preferred continuum carrier.  It stores exactly one selected
-- measure sequence, one selected continuum target, their convergence relation,
-- and the physical continuum OS properties.  It deliberately does not choose
-- a limit for arbitrary sequences or assert arbitrary sequence convergence.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5SelectedSequentialConvergenceExact as Selected

record SelectedFiniteToContinuumOS
    (Measure Schwinger : Set) : Set₁ where
  field
    finiteMeasures : Nat → Measure
    continuumMeasure : Measure
    schwinger : Measure → Schwinger

    convergence : Selected.SequentialConvergence Measure
    continuumIsSelectedLimit :
      Selected.Converges convergence finiteMeasures continuumMeasure

    Normalized Positive GaugeInvariant ReflectionPositiveMeasure : Measure → Set
    EuclideanCovariant ReflectionPositive Symmetric Tempered Regular Clustered :
      Schwinger → Set

    continuumNormalized : Normalized continuumMeasure
    continuumPositive : Positive continuumMeasure
    continuumGaugeInvariant : GaugeInvariant continuumMeasure
    continuumReflectionPositiveMeasure : ReflectionPositiveMeasure continuumMeasure

    continuumEuclideanCovariant : EuclideanCovariant (schwinger continuumMeasure)
    continuumReflectionPositive : ReflectionPositive (schwinger continuumMeasure)
    continuumSymmetric : Symmetric (schwinger continuumMeasure)
    continuumTempered : Tempered (schwinger continuumMeasure)
    continuumRegular : Regular (schwinger continuumMeasure)
    continuumClustered : Clustered (schwinger continuumMeasure)

open SelectedFiniteToContinuumOS public

record SelectedContinuumOSAxioms
    {Measure Schwinger : Set}
    (closure : SelectedFiniteToContinuumOS Measure Schwinger) : Set₁ where
  field
    normalized : Normalized closure (continuumMeasure closure)
    positive : Positive closure (continuumMeasure closure)
    gaugeInvariant : GaugeInvariant closure (continuumMeasure closure)
    euclideanCovariant :
      EuclideanCovariant closure (schwinger closure (continuumMeasure closure))
    reflectionPositive :
      ReflectionPositive closure (schwinger closure (continuumMeasure closure))
    symmetric : Symmetric closure (schwinger closure (continuumMeasure closure))
    tempered : Tempered closure (schwinger closure (continuumMeasure closure))
    regular : Regular closure (schwinger closure (continuumMeasure closure))
    clustered : Clustered closure (schwinger closure (continuumMeasure closure))

open SelectedContinuumOSAxioms public

assembleSelectedContinuumOSAxioms :
  ∀ {Measure Schwinger}
    (closure : SelectedFiniteToContinuumOS Measure Schwinger) →
  SelectedContinuumOSAxioms closure
assembleSelectedContinuumOSAxioms closure = record
  { normalized = continuumNormalized closure
  ; positive = continuumPositive closure
  ; gaugeInvariant = continuumGaugeInvariant closure
  ; euclideanCovariant = continuumEuclideanCovariant closure
  ; reflectionPositive = continuumReflectionPositive closure
  ; symmetric = continuumSymmetric closure
  ; tempered = continuumTempered closure
  ; regular = continuumRegular closure
  ; clustered = continuumClustered closure
  }

selectedContinuumOSCarrierLevel : ProofLevel
selectedContinuumOSCarrierLevel = machineChecked

selectedContinuumOSAxiomAssemblyLevel : ProofLevel
selectedContinuumOSAxiomAssemblyLevel = machineChecked
