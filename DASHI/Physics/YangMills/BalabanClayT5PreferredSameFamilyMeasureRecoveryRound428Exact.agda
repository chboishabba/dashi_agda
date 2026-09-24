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
--   * continuum Euclidean/symmetry/tempered/regular properties;
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

selectedCore :
  ∀ {Measure Observable Scalar Schwinger} →
  PreferredSameFamilyMeasureInputs Measure Observable Scalar Schwinger →
  Selected.SelectedFiniteToContinuumOSCore Measure Schwinger
selectedCore inputs = record
  { Selected.SelectedFiniteToContinuumOSCore.finiteMeasuresCore =
      T5.diagonalMeasure (PreferredGram.expectationData (gramInputs inputs))
  ; Selected.SelectedFiniteToContinuumOSCore.continuumMeasureCore =
      T5.continuumMeasure
        (T5.thermodynamic (PreferredGram.expectationData (gramInputs inputs)))
  ; Selected.SelectedFiniteToContinuumOSCore.schwingerCore =
      schwinger inputs
  ; Selected.SelectedFiniteToContinuumOSCore.convergenceCore =
      selectedConvergence inputs
  ; Selected.SelectedFiniteToContinuumOSCore.continuumIsSelectedLimitCore =
      R427.literalDiagonalConvergesToContinuum (compactUnique inputs)
  ; Selected.SelectedFiniteToContinuumOSCore.NormalizedCore =
      Normalized inputs
  ; Selected.SelectedFiniteToContinuumOSCore.PositiveCore =
      Positive inputs
  ; Selected.SelectedFiniteToContinuumOSCore.GaugeInvariantCore =
      GaugeInvariant inputs
  ; Selected.SelectedFiniteToContinuumOSCore.ReflectionPositiveMeasureCore =
      OS.GramReflectionPositive
        (Gram.physicalMeasureTopologyControlsOSGram
          (PreferredGram.compilePhysicalMeasureToOSGramData (gramInputs inputs)))
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
      normalizedClosed inputs
        (T5.diagonalMeasure
          (PreferredGram.expectationData (gramInputs inputs)))
        (T5.continuumMeasure
          (T5.thermodynamic
            (PreferredGram.expectationData (gramInputs inputs))))
        (R427.literalDiagonalConvergesToContinuum (compactUnique inputs))
        (finiteNormalized inputs)
  ; Selected.SelectedFiniteToContinuumOSCore.continuumPositiveCore =
      positiveClosed inputs
        (T5.diagonalMeasure
          (PreferredGram.expectationData (gramInputs inputs)))
        (T5.continuumMeasure
          (T5.thermodynamic
            (PreferredGram.expectationData (gramInputs inputs))))
        (R427.literalDiagonalConvergesToContinuum (compactUnique inputs))
        (finitePositive inputs)
  ; Selected.SelectedFiniteToContinuumOSCore.continuumGaugeInvariantCore =
      gaugeInvariantClosed inputs
        (T5.diagonalMeasure
          (PreferredGram.expectationData (gramInputs inputs)))
        (T5.continuumMeasure
          (T5.thermodynamic
            (PreferredGram.expectationData (gramInputs inputs))))
        (R427.literalDiagonalConvergesToContinuum (compactUnique inputs))
        (finiteGaugeInvariant inputs)
  ; Selected.SelectedFiniteToContinuumOSCore.continuumReflectionPositiveMeasureCore =
      Gram.physicalContinuumReflectionPositive
        (PreferredGram.compilePhysicalMeasureToOSGramData (gramInputs inputs))
  ; Selected.SelectedFiniteToContinuumOSCore.continuumEuclideanCovariantCore =
      continuumEuclideanCovariant inputs
  ; Selected.SelectedFiniteToContinuumOSCore.continuumReflectionPositiveCore =
      gramReflectionImpliesSchwingerReflection inputs
        (T5.continuumMeasure
          (T5.thermodynamic
            (PreferredGram.expectationData (gramInputs inputs))))
        (Gram.physicalContinuumReflectionPositive
          (PreferredGram.compilePhysicalMeasureToOSGramData (gramInputs inputs)))
  ; Selected.SelectedFiniteToContinuumOSCore.continuumSymmetricCore =
      continuumSymmetric inputs
  ; Selected.SelectedFiniteToContinuumOSCore.continuumTemperedCore =
      continuumTempered inputs
  ; Selected.SelectedFiniteToContinuumOSCore.continuumRegularCore =
      continuumRegular inputs
  }

record ReconstructionAuthority
    {Measure Observable Scalar Schwinger : Set}
    (inputs :
      PreferredSameFamilyMeasureInputs Measure Observable Scalar Schwinger)
    (Reconstructed : Set) : Set₁ where
  field
    reconstruct :
      Selected.SelectedContinuumOSCoreAxioms (selectedCore inputs) →
      Reconstructed

open ReconstructionAuthority public

sameFamilyCoreRecovery :
  ∀ {Measure Observable Scalar Schwinger Reconstructed}
    (inputs :
      PreferredSameFamilyMeasureInputs Measure Observable Scalar Schwinger) →
  ReconstructionAuthority inputs Reconstructed →
  R425.SameFamilyContinuumCoreRecovery
    Measure Observable Schwinger Scalar Reconstructed
sameFamilyCoreRecovery inputs authority = record
  { R425.SameFamilyContinuumCoreRecovery.physicalGramDataCore =
      PreferredGram.compilePhysicalMeasureToOSGramData (gramInputs inputs)
  ; R425.SameFamilyContinuumCoreRecovery.selectedCore =
      selectedCore inputs
  ; R425.SameFamilyContinuumCoreRecovery.physicalMeasureSequenceAgreesCore =
      λ cutoff →
        PreferredGram.compiledGramFiniteMeasureIsDiagonal
          (gramInputs inputs) cutoff
  ; R425.SameFamilyContinuumCoreRecovery.physicalContinuumMeasureAgreesCore =
      PreferredGram.compiledGramContinuumMeasureIsExpectationContinuum
        (gramInputs inputs)
  ; R425.SameFamilyContinuumCoreRecovery.gramReflectionImpliesSelectedReflectionCore =
      λ gramPositive →
        gramReflectionImpliesSchwingerReflection inputs
          (T5.continuumMeasure
            (T5.thermodynamic
              (PreferredGram.expectationData (gramInputs inputs))))
          gramPositive
  ; R425.SameFamilyContinuumCoreRecovery.reconstructFromSelectedOSCore =
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

round428ContinuumSchwingerCoreInputsLevel : ProofLevel
round428ContinuumSchwingerCoreInputsLevel = conditional

round428GramToSchwingerReflectionMeaningLevel : ProofLevel
round428GramToSchwingerReflectionMeaningLevel = conditional

round428IndependentGramMeasureSameObjectPaymentRequired : Bool
round428IndependentGramMeasureSameObjectPaymentRequired = false


round428ClusteringRequiredForCoreRecovery : Bool
round428ClusteringRequiredForCoreRecovery = false
