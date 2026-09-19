{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5MarkovToProkhorovTightnessExact where

------------------------------------------------------------------------
-- SELECTED MOMENT + MARKOV/COERCIVITY -> PROKHOROV TIGHTNESS INPUT
--
-- Historical T5 compactness records carry separate Set-valued leaves named
--
--   coordinateMarkovBound
--   finiteUnionTailBound
--   finiteDimensionalTightness
--   gaugeInvariantMarginalTightness.
--
-- On the selected diagonal route these are not four independent analytic
-- payments.  The repository already owns:
--
--   literal selected polynomial moment bound
--       -> selected coercive Markov compact containment
--       -> one uniform compact-containment certificate
--       -> restriction of that certificate to every literal subsequence.
--
-- This module composes those theorem-bearing owners directly into the exact
-- SelectedSubsequenceTightnessData consumed by the selected Prokhorov
-- authority.  It deliberately introduces no finite-coordinate union bound:
-- one global coercive observable with compact sublevels controls escape from
-- the selected configuration-space compact witness in one shot.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5CoerciveMomentMarkovContainmentExact as Markov
import DASHI.Physics.YangMills.BalabanClayT1SelectedCoerciveContainmentRound212Exact as Coercive
import DASHI.Physics.YangMills.BalabanClayT5SelectedMomentCompactContainmentExact as Moment
import DASHI.Physics.YangMills.BalabanClayT5UniformTightnessSubsequenceInheritanceExact as Uniform
import DASHI.Physics.YangMills.BalabanClayT5SelectedSequentialConvergenceExact as Selected
import DASHI.Physics.YangMills.BalabanClayT5SelectedProkhorovExtractionExact as Prokhorov

record SelectedMarkovProkhorovTightnessInputs
    (Measure Observable Scalar Epsilon Witness : Set)
    (expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar)
    (authority :
      Markov.MarkovCompactContainmentAuthority
        Measure Observable Scalar Epsilon Witness) : Set₁ where
  field
    convergence : Selected.SequentialConvergence Measure

    coercive :
      Coercive.SelectedPhysicalCoerciveMomentInputs
        Measure Observable Scalar Epsilon Witness
        expectationData authority

open SelectedMarkovProkhorovTightnessInputs public

selectedContainmentInputs :
  ∀ {Measure Observable Scalar Epsilon Witness}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar}
    {authority :
      Markov.MarkovCompactContainmentAuthority
        Measure Observable Scalar Epsilon Witness} →
  SelectedMarkovProkhorovTightnessInputs
    Measure Observable Scalar Epsilon Witness expectationData authority →
  Moment.SelectedMomentCompactContainmentInputs
    Measure Observable Scalar Epsilon Witness expectationData
selectedContainmentInputs inputs =
  Coercive.compileSelectedPhysicalCoerciveContainment (coercive inputs)

selectedMarkovUniformTightness :
  ∀ {Measure Observable Scalar Epsilon Witness}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar}
    {authority :
      Markov.MarkovCompactContainmentAuthority
        Measure Observable Scalar Epsilon Witness}
    (inputs :
      SelectedMarkovProkhorovTightnessInputs
        Measure Observable Scalar Epsilon Witness expectationData authority) →
  Uniform.UniformTightnessCertificate
    Measure Epsilon Witness
    (Moment.Admissible (selectedContainmentInputs inputs))
    (Moment.Controls (selectedContainmentInputs inputs))
    (T5.diagonalMeasure expectationData)
selectedMarkovUniformTightness inputs =
  Moment.selectedDiagonalUniformTightnessCertificate
    (selectedContainmentInputs inputs)

compileSelectedMarkovProkhorovTightness :
  ∀ {Measure Observable Scalar Epsilon Witness}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar}
    {authority :
      Markov.MarkovCompactContainmentAuthority
        Measure Observable Scalar Epsilon Witness} →
  SelectedMarkovProkhorovTightnessInputs
    Measure Observable Scalar Epsilon Witness expectationData authority →
  Prokhorov.SelectedSubsequenceTightnessData Measure
compileSelectedMarkovProkhorovTightness
  {expectationData = expectationData} inputs = record
  { convergence = convergence inputs
  ; sequence = T5.diagonalMeasure expectationData
  ; TightMeasureSequence =
      Uniform.UniformTightnessCertificate
        _ _ _
        (Moment.Admissible (selectedContainmentInputs inputs))
        (Moment.Controls (selectedContainmentInputs inputs))
  ; everyLiteralSubsequenceTight = λ subsequence →
      Uniform.restrictUniformTightnessToSubsequence
        (selectedMarkovUniformTightness inputs)
        subsequence
  }

------------------------------------------------------------------------
-- If a standard Prokhorov authority is supplied, the same selected Markov
-- certificate now drives actual further-subsequence extraction directly.
------------------------------------------------------------------------

selectedMarkovFurtherSubsequence :
  ∀ {Measure Observable Scalar Epsilon Witness}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar}
    {authority :
      Markov.MarkovCompactContainmentAuthority
        Measure Observable Scalar Epsilon Witness}
    (prokhorov : Prokhorov.SelectedProkhorovAuthority Measure)
    (inputs :
      SelectedMarkovProkhorovTightnessInputs
        Measure Observable Scalar Epsilon Witness expectationData authority)
    (subsequence :
      DASHI.Physics.YangMills.BalabanClayT5CompactUniqueFullSequenceExact.SubsequenceWitness
        (T5.diagonalMeasure expectationData)) →
  DASHI.Physics.YangMills.BalabanClayT5CompactUniqueFullSequenceExact.SubsequenceWitness
    (DASHI.Physics.YangMills.BalabanClayT5CompactUniqueFullSequenceExact.values
      subsequence)
selectedMarkovFurtherSubsequence prokhorov inputs subsequence =
  Prokhorov.selectedFurther
    prokhorov
    (compileSelectedMarkovProkhorovTightness inputs)
    subsequence

selectedMarkovToUniformTightnessCompilerLevel : ProofLevel
selectedMarkovToUniformTightnessCompilerLevel = machineChecked

selectedUniformTightnessToProkhorovInputCompilerLevel : ProofLevel
selectedUniformTightnessToProkhorovInputCompilerLevel = machineChecked

selectedMarkovToProkhorovExtractionCompilerLevel : ProofLevel
selectedMarkovToProkhorovExtractionCompilerLevel = machineChecked

-- Standard theorem authority only; not a Yang--Mills analytic leaf.
prokhorovAuthorityLevel : ProofLevel
prokhorovAuthorityLevel = standardImported

-- Genuine remaining same-object physical/representation inputs.
selectedExpectationProbabilityIntegralSemanticsLevel : ProofLevel
selectedExpectationProbabilityIntegralSemanticsLevel = conditional

selectedCoerciveObservableGeometryLevel : ProofLevel
selectedCoerciveObservableGeometryLevel = conditional

selectedCompactSublevelGeometryLevel : ProofLevel
selectedCompactSublevelGeometryLevel = conditional
