{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5WeakMeasureSemanticsRound437Exact where

------------------------------------------------------------------------
-- ROUND437 / ONE WEAK TEST-CLASS SEMANTICS PAYS H2c PROPERTY CLOSURE
--
-- R436 fixes the selected weak expectation topology on the exact T5 physical
-- family.  The selected weak property compiler already proves sequential
-- closure of normalization, positivity and action/gauge invariance.
--
-- R437 makes those the preferred R428 measure predicates.  Hence H2c no longer
-- consists of three independent continuum closure theorems.  The physical seam
-- is the finite Yang--Mills meaning of the unit / positive / gauge test class.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5OSGramTopologyExact as OS
import DASHI.Physics.YangMills.BalabanClayT5PreferredOSGramFromExpectationExact as PreferredGram
import DASHI.Physics.YangMills.BalabanClayT5SelectedWeakExpectationClosureExact as Weak
import DASHI.Physics.YangMills.BalabanClayT5SelectedWeakTopologyMeaningRound435Exact as R435
import DASHI.Physics.YangMills.BalabanClayT5GlobalContainmentWeakTopologyRound436Exact as R436
import DASHI.Physics.YangMills.BalabanClayT5PreferredSameFamilyMeasureRecoveryRound428Exact as R428
import DASHI.Physics.YangMills.BalabanClayT5SelectedContinuumOSExact as Selected

record WeakMeasureSemanticsInputs
    (Measure Observable Scalar Schwinger : Set) : Set₂ where
  field
    gramInputs :
      PreferredGram.PhysicalOSGramFromExpectationInputs
        Measure Observable Scalar

    schwinger : Measure → Schwinger

    Epsilon Witness Gauge : Set

    globalCompactness :
      R436.GlobalContainmentWeakTopologyInputs
        (PreferredGram.expectationData gramInputs)
        Epsilon Witness

    propertySemantics :
      Weak.SelectedWeakMeasurePropertySemantics
        (R435.compileSelectedWeakExpectationTopology
          (R436.weakTopologyMeaning globalCompactness))
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

    gramReflectionImpliesSchwingerReflection : ∀ measure →
      OS.GramReflectionPositive
        (Gram.physicalMeasureTopologyControlsOSGram
          (PreferredGram.compilePhysicalMeasureToOSGramData gramInputs))
        measure →
      ReflectionPositive (schwinger measure)

open WeakMeasureSemanticsInputs public

asR428PreferredSameFamilyInputs :
  ∀ {Measure Observable Scalar Schwinger} →
  WeakMeasureSemanticsInputs Measure Observable Scalar Schwinger →
  R428.PreferredSameFamilyMeasureInputs
    Measure Observable Scalar Schwinger
asR428PreferredSameFamilyInputs inputs = record
  { R428.PreferredSameFamilyMeasureInputs.gramInputs =
      gramInputs inputs
  ; R428.PreferredSameFamilyMeasureInputs.schwinger =
      schwinger inputs
  ; R428.PreferredSameFamilyMeasureInputs.Epsilon =
      Epsilon inputs
  ; R428.PreferredSameFamilyMeasureInputs.Witness =
      Witness inputs
  ; R428.PreferredSameFamilyMeasureInputs.globalCompactness =
      globalCompactness inputs
  ; R428.PreferredSameFamilyMeasureInputs.Normalized =
      Weak.Normalized (propertySemantics inputs)
  ; R428.PreferredSameFamilyMeasureInputs.Positive =
      Weak.Positive (propertySemantics inputs)
  ; R428.PreferredSameFamilyMeasureInputs.GaugeInvariant =
      Weak.ActionInvariant (propertySemantics inputs)
  ; R428.PreferredSameFamilyMeasureInputs.finiteNormalized =
      finiteNormalized inputs
  ; R428.PreferredSameFamilyMeasureInputs.finitePositive =
      finitePositive inputs
  ; R428.PreferredSameFamilyMeasureInputs.finiteGaugeInvariant =
      finiteGaugeInvariant inputs
  ; R428.PreferredSameFamilyMeasureInputs.normalizedClosed =
      Weak.normalizedClosed (propertySemantics inputs)
  ; R428.PreferredSameFamilyMeasureInputs.positiveClosed =
      Weak.positiveClosed (propertySemantics inputs)
  ; R428.PreferredSameFamilyMeasureInputs.gaugeInvariantClosed =
      Weak.actionInvariantClosed (propertySemantics inputs)
  ; R428.PreferredSameFamilyMeasureInputs.EuclideanCovariant =
      EuclideanCovariant inputs
  ; R428.PreferredSameFamilyMeasureInputs.ReflectionPositive =
      ReflectionPositive inputs
  ; R428.PreferredSameFamilyMeasureInputs.Symmetric =
      Symmetric inputs
  ; R428.PreferredSameFamilyMeasureInputs.Tempered =
      Tempered inputs
  ; R428.PreferredSameFamilyMeasureInputs.Regular =
      Regular inputs
  ; R428.PreferredSameFamilyMeasureInputs.continuumEuclideanCovariant =
      continuumEuclideanCovariant inputs
  ; R428.PreferredSameFamilyMeasureInputs.continuumSymmetric =
      continuumSymmetric inputs
  ; R428.PreferredSameFamilyMeasureInputs.continuumTempered =
      continuumTempered inputs
  ; R428.PreferredSameFamilyMeasureInputs.continuumRegular =
      continuumRegular inputs
  ; R428.PreferredSameFamilyMeasureInputs.gramReflectionImpliesSchwingerReflection =
      gramReflectionImpliesSchwingerReflection inputs
  }

round437WeakMeasurePropertyCompilerLevel : ProofLevel
round437WeakMeasurePropertyCompilerLevel = machineChecked

round437NormalizationClosureLevel : ProofLevel
round437NormalizationClosureLevel = machineChecked

round437PositivityClosureLevel : ProofLevel
round437PositivityClosureLevel = machineChecked

round437GaugeInvarianceClosureLevel : ProofLevel
round437GaugeInvarianceClosureLevel = machineChecked

round437FiniteWeakTestClassPhysicalMeaningLevel : ProofLevel
round437FiniteWeakTestClassPhysicalMeaningLevel = conditional

round437IndependentMeasurePropertyClosureTheoremsRequired : Bool
round437IndependentMeasurePropertyClosureTheoremsRequired = false


selectedPreGapContinuumCore :
  ∀ {Measure Observable Scalar Schwinger}
    (inputs :
      WeakMeasureSemanticsInputs Measure Observable Scalar Schwinger) →
  Selected.SelectedFiniteToContinuumOSCore Measure Schwinger
selectedPreGapContinuumCore inputs =
  R428.selectedCore (asR428PreferredSameFamilyInputs inputs)

round437GlobalMomentCompactContainmentLevel : ProofLevel
round437GlobalMomentCompactContainmentLevel = conditional

round437SelectedWeakTopologyMeaningLevel : ProofLevel
round437SelectedWeakTopologyMeaningLevel = conditional

round437DeterminingClassUniquenessLevel : ProofLevel
round437DeterminingClassUniquenessLevel = machineChecked

round437FullMeasureConvergenceLevel : ProofLevel
round437FullMeasureConvergenceLevel = machineChecked

round437PreGapContinuumCoreCompilerLevel : ProofLevel
round437PreGapContinuumCoreCompilerLevel = machineChecked

round437ContinuumSchwingerCoreAnalyticInputsLevel : ProofLevel
round437ContinuumSchwingerCoreAnalyticInputsLevel = conditional

round437GramToSchwingerReflectionMeaningLevel : ProofLevel
round437GramToSchwingerReflectionMeaningLevel = conditional

round437ClusteringRequiredForPreGapCore : Bool
round437ClusteringRequiredForPreGapCore = false
