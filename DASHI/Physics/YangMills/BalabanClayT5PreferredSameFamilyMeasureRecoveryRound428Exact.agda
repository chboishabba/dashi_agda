{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5PreferredSameFamilyMeasureRecoveryRound428Exact where

------------------------------------------------------------------------
-- ROUND428 / PREFERRED SAME-FAMILY MEASURE + OS RECOVERY
--
-- This is the measure-level companion to the expectation-linked continuum
-- carrier.  The OS-Gram object is BUILT from the physical expectation producer,
-- so its finite measure sequence and continuum target are definitionally the
-- same T5 objects.  Consequently no post-hoc Gram/measure equality fields are
-- required.
--
-- Physical leaves retained here are genuinely continuum-level:
--
--   * convergence of the selected diagonal measures to the selected target;
--   * sequential closure of normalization/positivity/gauge invariance;
--   * continuum Euclidean/symmetry/tempered/regular/cluster properties;
--   * meaning of reflected-Gram positivity as Schwinger reflection positivity.
--
-- P2 bounded expectation convergence and complete Gram convergence are already
-- compiler output of the expectation/Gram producers.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit
import DASHI.Physics.YangMills.BalabanClayT5SelectedSequentialConvergenceExact as Sequential
import DASHI.Physics.YangMills.BalabanClayT5SelectedContinuumOSExact as Selected
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5OSGramTopologyExact as OS
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5PreferredOSGramFromExpectationExact as PreferredGram
import DASHI.Physics.YangMills.BalabanClayT5SameFamilyContinuumRecoveryRound425Exact as R425
import DASHI.Physics.YangMills.BalabanClayT5DiagonalCompactUniqueRound427Exact as R427

record PreferredSameFamilyMeasureInputs
    (Measure Observable Scalar Schwinger : Set) : Set₂ where
  field
    gramInputs :
      PreferredGram.PhysicalOSGramFromExpectationInputs
        Measure Observable Scalar

    schwinger : Measure → Schwinger

    compactUnique :
      R427.LiteralDiagonalCompactUniqueInputs
        (PreferredGram.expectationData gramInputs)

    Normalized Positive GaugeInvariant : Measure → Set

    finiteNormalized : ∀ cutoff →
      Normalized
        (T5.diagonalMeasure
          (PreferredGram.expectationData gramInputs) cutoff)

    finitePositive : ∀ cutoff →
      Positive
        (T5.diagonalMeasure
          (PreferredGram.expectationData gramInputs) cutoff)

    finiteGaugeInvariant : ∀ cutoff →
      GaugeInvariant
        (T5.diagonalMeasure
          (PreferredGram.expectationData gramInputs) cutoff)

    normalizedClosed : ∀ sequence target →
      Limit.Converges (R427.convergence compactUnique) sequence target →
      (∀ cutoff → Normalized (sequence cutoff)) →
      Normalized target

    positiveClosed : ∀ sequence target →
      Limit.Converges (R427.convergence compactUnique) sequence target →
      (∀ cutoff → Positive (sequence cutoff)) →
      Positive target

    gaugeInvariantClosed : ∀ sequence target →
      Limit.Converges (R427.convergence compactUnique) sequence target →
      (∀ cutoff → GaugeInvariant (sequence cutoff)) →
      GaugeInvariant target

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
          (PreferredGram.compilePhysicalMeasureToOSGramData gramInputs))
        measure →
      ReflectionPositive (schwinger measure)

open PreferredSameFamilyMeasureInputs public

selectedConvergence :
  ∀ {Measure Observable Scalar Schwinger}
    (inputs :
      PreferredSameFamilyMeasureInputs Measure Observable Scalar Schwinger) →
  Sequential.SequentialConvergence Measure
selectedConvergence inputs = record
  { Sequential.SequentialConvergence.Converges =
      Limit.Converges (R427.convergence (compactUnique inputs))
  }

selectedClosure :
  ∀ {Measure Observable Scalar Schwinger} →
  PreferredSameFamilyMeasureInputs Measure Observable Scalar Schwinger →
  Selected.SelectedFiniteToContinuumOS Measure Schwinger
selectedClosure inputs = record
  { Selected.SelectedFiniteToContinuumOS.finiteMeasures =
      T5.diagonalMeasure (PreferredGram.expectationData (gramInputs inputs))
  ; Selected.SelectedFiniteToContinuumOS.continuumMeasure =
      T5.continuumMeasure
        (T5.thermodynamic (PreferredGram.expectationData (gramInputs inputs)))
  ; Selected.SelectedFiniteToContinuumOS.schwinger =
      schwinger inputs
  ; Selected.SelectedFiniteToContinuumOS.convergence =
      selectedConvergence inputs
  ; Selected.SelectedFiniteToContinuumOS.continuumIsSelectedLimit =
      R427.literalDiagonalConvergesToContinuum (compactUnique inputs)
  ; Selected.SelectedFiniteToContinuumOS.Normalized =
      Normalized inputs
  ; Selected.SelectedFiniteToContinuumOS.Positive =
      Positive inputs
  ; Selected.SelectedFiniteToContinuumOS.GaugeInvariant =
      GaugeInvariant inputs
  ; Selected.SelectedFiniteToContinuumOS.ReflectionPositiveMeasure =
      OS.GramReflectionPositive
        (Gram.physicalMeasureTopologyControlsOSGram
          (PreferredGram.compilePhysicalMeasureToOSGramData (gramInputs inputs)))
  ; Selected.SelectedFiniteToContinuumOS.EuclideanCovariant =
      EuclideanCovariant inputs
  ; Selected.SelectedFiniteToContinuumOS.ReflectionPositive =
      ReflectionPositive inputs
  ; Selected.SelectedFiniteToContinuumOS.Symmetric =
      Symmetric inputs
  ; Selected.SelectedFiniteToContinuumOS.Tempered =
      Tempered inputs
  ; Selected.SelectedFiniteToContinuumOS.Regular =
      Regular inputs
  ; Selected.SelectedFiniteToContinuumOS.Clustered =
      Clustered inputs
  ; Selected.SelectedFiniteToContinuumOS.continuumNormalized =
      normalizedClosed inputs
        (T5.diagonalMeasure
          (PreferredGram.expectationData (gramInputs inputs)))
        (T5.continuumMeasure
          (T5.thermodynamic
            (PreferredGram.expectationData (gramInputs inputs))))
        (R427.literalDiagonalConvergesToContinuum (compactUnique inputs))
        (finiteNormalized inputs)
  ; Selected.SelectedFiniteToContinuumOS.continuumPositive =
      positiveClosed inputs
        (T5.diagonalMeasure
          (PreferredGram.expectationData (gramInputs inputs)))
        (T5.continuumMeasure
          (T5.thermodynamic
            (PreferredGram.expectationData (gramInputs inputs))))
        (R427.literalDiagonalConvergesToContinuum (compactUnique inputs))
        (finitePositive inputs)
  ; Selected.SelectedFiniteToContinuumOS.continuumGaugeInvariant =
      gaugeInvariantClosed inputs
        (T5.diagonalMeasure
          (PreferredGram.expectationData (gramInputs inputs)))
        (T5.continuumMeasure
          (T5.thermodynamic
            (PreferredGram.expectationData (gramInputs inputs))))
        (R427.literalDiagonalConvergesToContinuum (compactUnique inputs))
        (finiteGaugeInvariant inputs)
  ; Selected.SelectedFiniteToContinuumOS.continuumReflectionPositiveMeasure =
      Gram.physicalContinuumReflectionPositive
        (PreferredGram.compilePhysicalMeasureToOSGramData (gramInputs inputs))
  ; Selected.SelectedFiniteToContinuumOS.continuumEuclideanCovariant =
      continuumEuclideanCovariant inputs
  ; Selected.SelectedFiniteToContinuumOS.continuumReflectionPositive =
      gramReflectionImpliesSchwingerReflection inputs
        (T5.continuumMeasure
          (T5.thermodynamic
            (PreferredGram.expectationData (gramInputs inputs))))
        (Gram.physicalContinuumReflectionPositive
          (PreferredGram.compilePhysicalMeasureToOSGramData (gramInputs inputs)))
  ; Selected.SelectedFiniteToContinuumOS.continuumSymmetric =
      continuumSymmetric inputs
  ; Selected.SelectedFiniteToContinuumOS.continuumTempered =
      continuumTempered inputs
  ; Selected.SelectedFiniteToContinuumOS.continuumRegular =
      continuumRegular inputs
  ; Selected.SelectedFiniteToContinuumOS.continuumClustered =
      continuumClustered inputs
  }

record ReconstructionAuthority
    {Measure Observable Scalar Schwinger : Set}
    (inputs :
      PreferredSameFamilyMeasureInputs Measure Observable Scalar Schwinger)
    (Reconstructed : Set) : Set₁ where
  field
    reconstruct :
      Selected.SelectedContinuumOSAxioms (selectedClosure inputs) →
      Reconstructed

open ReconstructionAuthority public

sameFamilyRecovery :
  ∀ {Measure Observable Scalar Schwinger Reconstructed}
    (inputs :
      PreferredSameFamilyMeasureInputs Measure Observable Scalar Schwinger) →
  ReconstructionAuthority inputs Reconstructed →
  R425.SameFamilyContinuumRecovery
    Measure Observable Schwinger Scalar Reconstructed
sameFamilyRecovery inputs authority = record
  { R425.SameFamilyContinuumRecovery.physicalGramData =
      PreferredGram.compilePhysicalMeasureToOSGramData (gramInputs inputs)
  ; R425.SameFamilyContinuumRecovery.selectedClosure =
      selectedClosure inputs
  ; R425.SameFamilyContinuumRecovery.physicalMeasureSequenceAgrees =
      λ cutoff →
        PreferredGram.compiledGramFiniteMeasureIsDiagonal
          (gramInputs inputs) cutoff
  ; R425.SameFamilyContinuumRecovery.physicalContinuumMeasureAgrees =
      PreferredGram.compiledGramContinuumMeasureIsExpectationContinuum
        (gramInputs inputs)
  ; R425.SameFamilyContinuumRecovery.gramReflectionImpliesSelectedReflection =
      λ gramPositive →
        gramReflectionImpliesSchwingerReflection inputs
          (T5.continuumMeasure
            (T5.thermodynamic
              (PreferredGram.expectationData (gramInputs inputs))))
          gramPositive
  ; R425.SameFamilyContinuumRecovery.reconstructFromSelectedOSAxioms =
      reconstruct authority
  }

round428PreferredSameFamilyMeasureCompilerLevel : ProofLevel
round428PreferredSameFamilyMeasureCompilerLevel = machineChecked

round428GramMeasurePresentationWeldLevel : ProofLevel
round428GramMeasurePresentationWeldLevel = machineChecked

round428OSReconstructionAuthorityLevel : ProofLevel
round428OSReconstructionAuthorityLevel = standardImported

round428MeasureConvergenceLevel : ProofLevel
round428MeasureConvergenceLevel = machineChecked

round428EveryLiteralSubsequenceTightLevel : ProofLevel
round428EveryLiteralSubsequenceTightLevel = conditional

round428EveryExtractedClusterPointIsContinuumLevel : ProofLevel
round428EveryExtractedClusterPointIsContinuumLevel = conditional

round428MeasurePropertyClosureLevel : ProofLevel
round428MeasurePropertyClosureLevel = conditional

round428ContinuumSchwingerAxiomInputsLevel : ProofLevel
round428ContinuumSchwingerAxiomInputsLevel = conditional

round428GramToSchwingerReflectionMeaningLevel : ProofLevel
round428GramToSchwingerReflectionMeaningLevel = conditional

round428IndependentGramMeasureSameObjectPaymentRequired : Bool
round428IndependentGramMeasureSameObjectPaymentRequired = false
