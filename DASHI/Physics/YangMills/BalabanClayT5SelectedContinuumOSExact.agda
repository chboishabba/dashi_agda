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

------------------------------------------------------------------------
-- PRE-GAP CORE CARRIER
--
-- Clustering is deliberately NOT part of this object.  The mass-gap route
-- obtains continuum clustering from P1 finite clustering + P2 selected
-- expectation convergence.  Keeping it out of the core prevents H2 from
-- assuming the conclusion produced by B.
------------------------------------------------------------------------

record SelectedFiniteToContinuumOSCore
    (Measure Schwinger : Set) : Set₁ where
  field
    finiteMeasuresCore : Nat → Measure
    continuumMeasureCore : Measure
    schwingerCore : Measure → Schwinger

    convergenceCore : Selected.SequentialConvergence Measure
    continuumIsSelectedLimitCore :
      Selected.Converges convergenceCore finiteMeasuresCore continuumMeasureCore

    NormalizedCore PositiveCore GaugeInvariantCore
      ReflectionPositiveMeasureCore : Measure → Set
    EuclideanCovariantCore ReflectionPositiveCore SymmetricCore
      TemperedCore RegularCore : Schwinger → Set

    continuumNormalizedCore : NormalizedCore continuumMeasureCore
    continuumPositiveCore : PositiveCore continuumMeasureCore
    continuumGaugeInvariantCore : GaugeInvariantCore continuumMeasureCore
    continuumReflectionPositiveMeasureCore :
      ReflectionPositiveMeasureCore continuumMeasureCore

    continuumEuclideanCovariantCore :
      EuclideanCovariantCore (schwingerCore continuumMeasureCore)
    continuumReflectionPositiveCore :
      ReflectionPositiveCore (schwingerCore continuumMeasureCore)
    continuumSymmetricCore :
      SymmetricCore (schwingerCore continuumMeasureCore)
    continuumTemperedCore :
      TemperedCore (schwingerCore continuumMeasureCore)
    continuumRegularCore :
      RegularCore (schwingerCore continuumMeasureCore)

open SelectedFiniteToContinuumOSCore public

record SelectedContinuumOSCoreAxioms
    {Measure Schwinger : Set}
    (core : SelectedFiniteToContinuumOSCore Measure Schwinger) : Set₁ where
  field
    normalizedCore : NormalizedCore core (continuumMeasureCore core)
    positiveCore : PositiveCore core (continuumMeasureCore core)
    gaugeInvariantCore :
      GaugeInvariantCore core (continuumMeasureCore core)
    euclideanCovariantCore :
      EuclideanCovariantCore core
        (schwingerCore core (continuumMeasureCore core))
    reflectionPositiveCore :
      ReflectionPositiveCore core
        (schwingerCore core (continuumMeasureCore core))
    symmetricCore :
      SymmetricCore core (schwingerCore core (continuumMeasureCore core))
    temperedCore :
      TemperedCore core (schwingerCore core (continuumMeasureCore core))
    regularCore :
      RegularCore core (schwingerCore core (continuumMeasureCore core))

open SelectedContinuumOSCoreAxioms public

assembleSelectedContinuumOSCoreAxioms :
  ∀ {Measure Schwinger}
    (core : SelectedFiniteToContinuumOSCore Measure Schwinger) →
  SelectedContinuumOSCoreAxioms core
assembleSelectedContinuumOSCoreAxioms core = record
  { normalizedCore = continuumNormalizedCore core
  ; positiveCore = continuumPositiveCore core
  ; gaugeInvariantCore = continuumGaugeInvariantCore core
  ; euclideanCovariantCore = continuumEuclideanCovariantCore core
  ; reflectionPositiveCore = continuumReflectionPositiveCore core
  ; symmetricCore = continuumSymmetricCore core
  ; temperedCore = continuumTemperedCore core
  ; regularCore = continuumRegularCore core
  }

record SelectedContinuumClustering
    {Measure Schwinger : Set}
    (core : SelectedFiniteToContinuumOSCore Measure Schwinger) : Set₁ where
  field
    ClusteredCore : Schwinger → Set
    continuumClusteredCore :
      ClusteredCore (schwingerCore core (continuumMeasureCore core))

open SelectedContinuumClustering public

-- Compatibility compiler.  Only this step re-attaches clustering.
corePlusClusteringToFullSelectedOS :
  ∀ {Measure Schwinger}
    (core : SelectedFiniteToContinuumOSCore Measure Schwinger) →
    SelectedContinuumClustering core →
    SelectedFiniteToContinuumOS Measure Schwinger
corePlusClusteringToFullSelectedOS core clustering = record
  { finiteMeasures = finiteMeasuresCore core
  ; continuumMeasure = continuumMeasureCore core
  ; schwinger = schwingerCore core
  ; convergence = convergenceCore core
  ; continuumIsSelectedLimit = continuumIsSelectedLimitCore core
  ; Normalized = NormalizedCore core
  ; Positive = PositiveCore core
  ; GaugeInvariant = GaugeInvariantCore core
  ; ReflectionPositiveMeasure = ReflectionPositiveMeasureCore core
  ; EuclideanCovariant = EuclideanCovariantCore core
  ; ReflectionPositive = ReflectionPositiveCore core
  ; Symmetric = SymmetricCore core
  ; Tempered = TemperedCore core
  ; Regular = RegularCore core
  ; Clustered = ClusteredCore clustering
  ; continuumNormalized = continuumNormalizedCore core
  ; continuumPositive = continuumPositiveCore core
  ; continuumGaugeInvariant = continuumGaugeInvariantCore core
  ; continuumReflectionPositiveMeasure =
      continuumReflectionPositiveMeasureCore core
  ; continuumEuclideanCovariant = continuumEuclideanCovariantCore core
  ; continuumReflectionPositive = continuumReflectionPositiveCore core
  ; continuumSymmetric = continuumSymmetricCore core
  ; continuumTempered = continuumTemperedCore core
  ; continuumRegular = continuumRegularCore core
  ; continuumClustered = continuumClusteredCore clustering
  }

selectedContinuumOSCoreCarrierLevel : ProofLevel
selectedContinuumOSCoreCarrierLevel = machineChecked

selectedContinuumOSCoreAxiomAssemblyLevel : ProofLevel
selectedContinuumOSCoreAxiomAssemblyLevel = machineChecked

selectedClusteringAttachmentLevel : ProofLevel
selectedClusteringAttachmentLevel = conditional

corePlusClusteringCompatibilityCompilerLevel : ProofLevel
corePlusClusteringCompatibilityCompilerLevel = machineChecked

selectedContinuumOSCarrierLevel : ProofLevel
selectedContinuumOSCarrierLevel = machineChecked

selectedContinuumOSAxiomAssemblyLevel : ProofLevel
selectedContinuumOSAxiomAssemblyLevel = machineChecked
