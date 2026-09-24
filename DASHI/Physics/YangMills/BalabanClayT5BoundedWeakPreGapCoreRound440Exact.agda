{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5BoundedWeakPreGapCoreRound440Exact where

------------------------------------------------------------------------
-- ROUND440 / PREFERRED PRE-GAP CONTINUUM CORE, SELECTED-CONVERGENCE ONLY
--
-- This is the direct successor to R437 on the Clay-facing route.
--
-- It removes the remaining legacy total-SequentialLimit detour:
--
--   global selected compact containment
--   + bounded-expectation weak topology / determining class
--      -> R439 full selected measure convergence
--   + finite weak-test normalization/positivity/gauge semantics
--   + continuum Schwinger analytic inputs
--   + physical Gram -> Schwinger reflection meaning
--      -> SelectedFiniteToContinuumOSCore.
--
-- Clustering is deliberately absent and is attached later from P1/B + P2.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5OSGramTopologyExact as OS
import DASHI.Physics.YangMills.BalabanClayT5PreferredOSGramFromExpectationExact as PreferredGram
import DASHI.Physics.YangMills.BalabanClayT5SelectedWeakExpectationClosureExact as Weak
import DASHI.Physics.YangMills.BalabanClayT5SelectedContinuumOSExact as Selected
import DASHI.Physics.YangMills.BalabanClayT5BoundedExpectationWeakTopologyRound438Exact as R438
import DASHI.Physics.YangMills.BalabanClayT5BoundedWeakCompactnessRound439Exact as R439

record BoundedWeakPreGapCoreInputs
    (Measure Observable Scalar Schwinger : Set) : Set₂ where
  field
    gramInputs :
      PreferredGram.PhysicalOSGramFromExpectationInputs
        Measure Observable Scalar

    schwinger : Measure → Schwinger

    Epsilon Witness Gauge : Set

    compactness :
      R439.BoundedWeakCompactnessInputs
        (PreferredGram.expectationData gramInputs)
        Epsilon Witness

    propertySemantics :
      Weak.SelectedWeakMeasurePropertySemantics
        (R438.compileBoundedExpectationWeakTopology
          (R439.weakTopologyAuthority compactness))
        Gauge

    finiteNormalized : ∀ cutoff →
      Weak.Normalized propertySemantics
        (T5.diagonalMeasure
          (PreferredGram.expectationData gramInputs) cutoff)

    finitePositive : ∀ cutoff →
      Weak.Positive propertySemantics
        (T5.diagonalMeasure
          (PreferredGram.expectationData gramInputs) cutoff)

    finiteGaugeInvariant : ∀ cutoff →
      Weak.ActionInvariant propertySemantics
        (T5.diagonalMeasure
          (PreferredGram.expectationData gramInputs) cutoff)

    EuclideanCovariant ReflectionPositive Symmetric Tempered Regular :
      Schwinger → Set

    continuumEuclideanCovariant :
      EuclideanCovariant
        (schwinger
          (T5.continuumMeasure
            (T5.thermodynamic
              (PreferredGram.expectationData gramInputs))))

    continuumSymmetric :
      Symmetric
        (schwinger
          (T5.continuumMeasure
            (T5.thermodynamic
              (PreferredGram.expectationData gramInputs))))

    continuumTempered :
      Tempered
        (schwinger
          (T5.continuumMeasure
            (T5.thermodynamic
              (PreferredGram.expectationData gramInputs))))

    continuumRegular :
      Regular
        (schwinger
          (T5.continuumMeasure
            (T5.thermodynamic
              (PreferredGram.expectationData gramInputs))))

    gramReflectionImpliesSchwingerReflection : ∀ measure →
      OS.GramReflectionPositive
        (Gram.physicalMeasureTopologyControlsOSGram
          (PreferredGram.compilePhysicalMeasureToOSGramData gramInputs))
        measure →
      ReflectionPositive (schwinger measure)

open BoundedWeakPreGapCoreInputs public

selectedPreGapContinuumCore :
  ∀ {Measure Observable Scalar Schwinger} →
  BoundedWeakPreGapCoreInputs
    Measure Observable Scalar Schwinger →
  Selected.SelectedFiniteToContinuumOSCore Measure Schwinger
selectedPreGapContinuumCore inputs = record
  { Selected.SelectedFiniteToContinuumOSCore.finiteMeasuresCore =
      T5.diagonalMeasure
        (PreferredGram.expectationData (gramInputs inputs))
  ; Selected.SelectedFiniteToContinuumOSCore.continuumMeasureCore =
      T5.continuumMeasure
        (T5.thermodynamic
          (PreferredGram.expectationData (gramInputs inputs)))
  ; Selected.SelectedFiniteToContinuumOSCore.schwingerCore =
      schwinger inputs
  ; Selected.SelectedFiniteToContinuumOSCore.convergenceCore =
      R438.boundedExpectationSequentialConvergence
        (PreferredGram.expectationData (gramInputs inputs))
  ; Selected.SelectedFiniteToContinuumOSCore.continuumIsSelectedLimitCore =
      R439.literalDiagonalConvergesToSelectedContinuum
        (compactness inputs)
  ; Selected.SelectedFiniteToContinuumOSCore.NormalizedCore =
      Weak.Normalized (propertySemantics inputs)
  ; Selected.SelectedFiniteToContinuumOSCore.PositiveCore =
      Weak.Positive (propertySemantics inputs)
  ; Selected.SelectedFiniteToContinuumOSCore.GaugeInvariantCore =
      Weak.ActionInvariant (propertySemantics inputs)
  ; Selected.SelectedFiniteToContinuumOSCore.ReflectionPositiveMeasureCore =
      OS.GramReflectionPositive
        (Gram.physicalMeasureTopologyControlsOSGram
          (PreferredGram.compilePhysicalMeasureToOSGramData
            (gramInputs inputs)))
  ; Selected.SelectedFiniteToContinuumOSCore.EuclideanCovariantCore =
      EuclideanCovariant inputs
  ; Selected.SelectedFiniteToContinuumOSCore.ReflectionPositiveCore =
      ReflectionPositive inputs
  ; Selected.SelectedFiniteToContinuumOSCore.SymmetricCore =
      Symmetric inputs
  ; Selected.SelectedFiniteToContinuumOSCore.TemperedCore =
      Tempered inputs
  ; Selected.SelectedFiniteToContinuumOSCore.RegularCore =
      Regular inputs
  ; Selected.SelectedFiniteToContinuumOSCore.continuumNormalizedCore =
      Weak.normalizedClosed
        (propertySemantics inputs)
        (T5.diagonalMeasure
          (PreferredGram.expectationData (gramInputs inputs)))
        (T5.continuumMeasure
          (T5.thermodynamic
            (PreferredGram.expectationData (gramInputs inputs))))
        (R439.literalDiagonalConvergesToSelectedContinuum
          (compactness inputs))
        (finiteNormalized inputs)
  ; Selected.SelectedFiniteToContinuumOSCore.continuumPositiveCore =
      Weak.positiveClosed
        (propertySemantics inputs)
        (T5.diagonalMeasure
          (PreferredGram.expectationData (gramInputs inputs)))
        (T5.continuumMeasure
          (T5.thermodynamic
            (PreferredGram.expectationData (gramInputs inputs))))
        (R439.literalDiagonalConvergesToSelectedContinuum
          (compactness inputs))
        (finitePositive inputs)
  ; Selected.SelectedFiniteToContinuumOSCore.continuumGaugeInvariantCore =
      Weak.actionInvariantClosed
        (propertySemantics inputs)
        (T5.diagonalMeasure
          (PreferredGram.expectationData (gramInputs inputs)))
        (T5.continuumMeasure
          (T5.thermodynamic
            (PreferredGram.expectationData (gramInputs inputs))))
        (R439.literalDiagonalConvergesToSelectedContinuum
          (compactness inputs))
        (finiteGaugeInvariant inputs)
  ; Selected.SelectedFiniteToContinuumOSCore.continuumReflectionPositiveMeasureCore =
      Gram.physicalContinuumReflectionPositive
        (PreferredGram.compilePhysicalMeasureToOSGramData
          (gramInputs inputs))
  ; Selected.SelectedFiniteToContinuumOSCore.continuumEuclideanCovariantCore =
      continuumEuclideanCovariant inputs
  ; Selected.SelectedFiniteToContinuumOSCore.continuumReflectionPositiveCore =
      gramReflectionImpliesSchwingerReflection inputs
        (T5.continuumMeasure
          (T5.thermodynamic
            (PreferredGram.expectationData (gramInputs inputs))))
        (Gram.physicalContinuumReflectionPositive
          (PreferredGram.compilePhysicalMeasureToOSGramData
            (gramInputs inputs)))
  ; Selected.SelectedFiniteToContinuumOSCore.continuumSymmetricCore =
      continuumSymmetric inputs
  ; Selected.SelectedFiniteToContinuumOSCore.continuumTemperedCore =
      continuumTempered inputs
  ; Selected.SelectedFiniteToContinuumOSCore.continuumRegularCore =
      continuumRegular inputs
  }

round440PreGapCoreCompilerLevel : ProofLevel
round440PreGapCoreCompilerLevel = machineChecked

round440GlobalMomentCompactContainmentLevel : ProofLevel
round440GlobalMomentCompactContainmentLevel = conditional

round440BoundedDeterminingClassMeaningLevel : ProofLevel
round440BoundedDeterminingClassMeaningLevel = conditional

round440FiniteWeakTestClassPhysicalMeaningLevel : ProofLevel
round440FiniteWeakTestClassPhysicalMeaningLevel = conditional

round440ContinuumSchwingerAnalyticInputsLevel : ProofLevel
round440ContinuumSchwingerAnalyticInputsLevel = conditional

round440GramToSchwingerReflectionMeaningLevel : ProofLevel
round440GramToSchwingerReflectionMeaningLevel = conditional

round440FullSelectedMeasureConvergenceLevel : ProofLevel
round440FullSelectedMeasureConvergenceLevel = machineChecked

round440LegacyTotalSequentialLimitRequired : Bool
round440LegacyTotalSequentialLimitRequired = false

round440ClusteringRequiredForPreGapCore : Bool
round440ClusteringRequiredForPreGapCore = false

round440IndependentMeasureContinuityTheoremRequired : Bool
round440IndependentMeasureContinuityTheoremRequired = false
