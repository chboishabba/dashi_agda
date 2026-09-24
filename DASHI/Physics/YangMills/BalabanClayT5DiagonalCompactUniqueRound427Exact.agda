{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5DiagonalCompactUniqueRound427Exact where

------------------------------------------------------------------------
-- ROUND427 / LITERAL T5 DIAGONAL: COMPACT + UNIQUE -> FULL CONVERGENCE
--
-- The quantitative continuum closure previously accepted
--
--   diagonalConvergesToContinuum
--
-- as one physical field.  Existing typed compactness machinery already proves
-- that conclusion from the genuinely physical data:
--
--   * every literal subsequence of the selected diagonal measure sequence is
--     tight;
--   * Prokhorov extracts a convergent further subsequence;
--   * every extracted cluster point is the selected continuum measure.
--
-- The standard compact+unique -> full convergence theorem then supplies the
-- whole-sequence limit.  The sequence and target are chosen definitionally
-- here, so no function-extensionality or post-hoc sequence equality is needed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5QuantitativeTailMomentCompactnessExact as Quant
import DASHI.Physics.YangMills.BalabanClayT5CompactUniqueFullSequenceExact as Compact
import DASHI.Physics.YangMills.BalabanClayT5SubsequenceProkhorovExtractionExact as Prokhorov

record LiteralDiagonalCompactUniqueInputs
    (Measure Observable Scalar Marginal : Set) : Set₂ where
  field
    quantitative :
      Quant.QuantitativeT5PhysicalInputs Measure Observable Scalar Marginal

    convergence : Limit.SequentialLimit Measure

    TightMeasureSequence : (Nat → Measure) → Set

    everyLiteralDiagonalSubsequenceTight :
      (subsequence :
        Compact.SubsequenceWitness
          (T5.diagonalMeasure (Quant.expectationData quantitative))) →
      TightMeasureSequence (Compact.values subsequence)

    prokhorovAuthority :
      Prokhorov.ProkhorovSubsequenceExtractionAuthority Measure

    everyExtractedDiagonalClusterPointIsContinuum :
      let selectedTightness : Prokhorov.PhysicalSubsequenceTightnessData Measure
          selectedTightness = record
            { Prokhorov.PhysicalSubsequenceTightnessData.convergence =
                convergence
            ; Prokhorov.PhysicalSubsequenceTightnessData.sequence =
                T5.diagonalMeasure (Quant.expectationData quantitative)
            ; Prokhorov.PhysicalSubsequenceTightnessData.TightMeasureSequence =
                TightMeasureSequence
            ; Prokhorov.PhysicalSubsequenceTightnessData.everyLiteralSubsequenceTight =
                everyLiteralDiagonalSubsequenceTight
            }
      in
      (subsequence :
        Compact.SubsequenceWitness
          (T5.diagonalMeasure (Quant.expectationData quantitative))) →
      Prokhorov.extractedClusterLimit
        prokhorovAuthority
        selectedTightness
        subsequence
      ≡
      T5.continuumMeasure
        (T5.thermodynamic (Quant.expectationData quantitative))

    compactUniqueFullConvergenceAuthority :
      Compact.CompactUniqueFullConvergenceAuthority Measure

  diagonalTightness :
    Prokhorov.PhysicalSubsequenceTightnessData Measure
  diagonalTightness = record
    { Prokhorov.PhysicalSubsequenceTightnessData.convergence =
        convergence
    ; Prokhorov.PhysicalSubsequenceTightnessData.sequence =
        T5.diagonalMeasure (Quant.expectationData quantitative)
    ; Prokhorov.PhysicalSubsequenceTightnessData.TightMeasureSequence =
        TightMeasureSequence
    ; Prokhorov.PhysicalSubsequenceTightnessData.everyLiteralSubsequenceTight =
        everyLiteralDiagonalSubsequenceTight
    }

open LiteralDiagonalCompactUniqueInputs public

diagonalCompactUniqueBridge :
  ∀ {Measure Observable Scalar Marginal} →
  (inputs :
    LiteralDiagonalCompactUniqueInputs Measure Observable Scalar Marginal) →
  Prokhorov.PhysicalCompactUniqueBridgeInputs Measure
diagonalCompactUniqueBridge inputs = record
  { Prokhorov.PhysicalCompactUniqueBridgeInputs.tightness =
      diagonalTightness inputs
  ; Prokhorov.PhysicalCompactUniqueBridgeInputs.target =
      T5.continuumMeasure
        (T5.thermodynamic
          (Quant.expectationData (quantitative inputs)))
  ; Prokhorov.PhysicalCompactUniqueBridgeInputs.prokhorovAuthority =
      prokhorovAuthority inputs
  ; Prokhorov.PhysicalCompactUniqueBridgeInputs.everyExtractedClusterPointIsTarget =
      everyExtractedDiagonalClusterPointIsContinuum inputs
  }

literalDiagonalConvergesToContinuum :
  ∀ {Measure Observable Scalar Marginal}
    (inputs :
      LiteralDiagonalCompactUniqueInputs Measure Observable Scalar Marginal) →
  Limit.Converges
    (convergence inputs)
    (T5.diagonalMeasure
      (Quant.expectationData (quantitative inputs)))
    (T5.continuumMeasure
      (T5.thermodynamic
        (Quant.expectationData (quantitative inputs))))
literalDiagonalConvergesToContinuum inputs =
  Compact.fullSequenceConverges
    (compactUniqueFullConvergenceAuthority inputs)
    (Prokhorov.compileSequentialCompactUniqueData
      (diagonalCompactUniqueBridge inputs))

round427DiagonalCompactUniqueCompilerLevel : ProofLevel
round427DiagonalCompactUniqueCompilerLevel = machineChecked

round427CompactUniqueFullConvergenceAuthorityLevel : ProofLevel
round427CompactUniqueFullConvergenceAuthorityLevel = standardImported

round427EveryLiteralSubsequenceTightLevel : ProofLevel
round427EveryLiteralSubsequenceTightLevel = conditional

round427EveryExtractedClusterPointIsContinuumLevel : ProofLevel
round427EveryExtractedClusterPointIsContinuumLevel = conditional

round427IndependentFullSequenceConvergenceInputRequired : Bool
round427IndependentFullSequenceConvergenceInputRequired = false
