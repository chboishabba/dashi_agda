{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5ClusterPointUniquenessRound430Exact where

------------------------------------------------------------------------
-- ROUND430 / P2 + DETERMINING EXPECTATIONS -> UNIQUE CLUSTER POINT
--
-- Do not ask H2 for a second opaque theorem saying every extracted cluster
-- point is the selected continuum measure.
--
-- For each literal subsequence:
--
--   measure convergence of the extracted further subsequence
--     -> convergence of each determining expectation to the cluster point;
--
--   P2 convergence on the original selected expectation producer
--     -> convergence of the same expectations along every literal nested
--        subsequence to the selected continuum target;
--
--   scalar Hausdorffness
--     -> equality of the two limiting expectations;
--
--   a measure-determining bounded cylinder class
--     -> equality of the two measures.
--
-- Thus H2b reduces to topology/meaning of the determining class.  H2a
-- (literal tightness of every subsequence) remains a separate physical theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5CompactUniqueFullSequenceExact as Compact
import DASHI.Physics.YangMills.BalabanClayT5SubsequenceProkhorovExtractionExact as Prokhorov
import DASHI.Physics.YangMills.BalabanClayT5DirectExpectationPropertyClosureExact as Direct
import DASHI.Physics.YangMills.BalabanClayT5DiagonalCompactUniqueRound427Exact as R427

record DeterminingExpectationUniquenessAuthority
    {Measure Observable Scalar : Set}
    (expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar)
    (tightness :
      Prokhorov.PhysicalSubsequenceTightnessData Measure)
    (prokhorov :
      Prokhorov.ProkhorovSubsequenceExtractionAuthority Measure) : Set₂ where
  field
    DeterminingObservable : Observable → Set

    determiningObservableBounded :
      ∀ observable →
      DeterminingObservable observable →
      T5.BoundedObservable (T5.thermodynamic expectationData) observable

    scalarAuthority :
      Direct.ScalarExpectationClosureAuthority expectationData

    -- Standard continuity of bounded cylinder expectations in the selected
    -- measure topology.
    measureConvergenceImpliesDeterminingExpectationConvergence :
      ∀ sequence target →
      Limit.Converges (Prokhorov.convergence tightness) sequence target →
      ∀ observable →
      DeterminingObservable observable →
      Gram.Converges
        (T5.scalarConvergence (T5.thermodynamic expectationData))
        (λ n →
          Gram.expectation
            (T5.operations (T5.thermodynamic expectationData))
            (sequence n)
            observable)
        (Gram.expectation
          (T5.operations (T5.thermodynamic expectationData))
          target
          observable)

    -- Standard fact that convergence of a scalar sequence is inherited by a
    -- literal nested subsequence.  The nested carriers are passed explicitly
    -- so the theorem cannot switch to an unrelated sequence.
    nestedSubsequencePreservesScalarConvergence :
      ∀ (subsequence :
          Compact.SubsequenceWitness (T5.diagonalMeasure expectationData))
        (further :
          Compact.SubsequenceWitness (Compact.values subsequence))
        observable target →
      Gram.Converges
        (T5.scalarConvergence (T5.thermodynamic expectationData))
        (λ n →
          Gram.expectation
            (T5.operations (T5.thermodynamic expectationData))
            (T5.diagonalMeasure expectationData n)
            observable)
        target →
      Gram.Converges
        (T5.scalarConvergence (T5.thermodynamic expectationData))
        (λ n →
          Gram.expectation
            (T5.operations (T5.thermodynamic expectationData))
            (Compact.values further n)
            observable)
        target

    determiningExpectationsSeparateMeasures :
      ∀ left right →
      (∀ observable →
        DeterminingObservable observable →
        Gram.expectation
          (T5.operations (T5.thermodynamic expectationData))
          left observable
        ≡
        Gram.expectation
          (T5.operations (T5.thermodynamic expectationData))
          right observable) →
      left ≡ right

open DeterminingExpectationUniquenessAuthority public

extractedClusterPointIsSelectedContinuum :
  ∀ {Measure Observable Scalar}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar}
    (tightness :
      Prokhorov.PhysicalSubsequenceTightnessData Measure)
    (prokhorov :
      Prokhorov.ProkhorovSubsequenceExtractionAuthority Measure)
    (authority :
      DeterminingExpectationUniquenessAuthority
        expectationData tightness prokhorov)
    (subsequence :
      Compact.SubsequenceWitness (T5.diagonalMeasure expectationData)) →
  Prokhorov.extractedClusterLimit prokhorov tightness subsequence
  ≡
  T5.continuumMeasure (T5.thermodynamic expectationData)
extractedClusterPointIsSelectedContinuum
    {expectationData = expectationData}
    tightness prokhorov authority subsequence =
  let
    further :
      Compact.SubsequenceWitness (Compact.values subsequence)
    further =
      Prokhorov.extractPhysicalFurtherSubsequence
        prokhorov tightness subsequence

    cluster : Measure
    cluster =
      Prokhorov.extractedClusterLimit prokhorov tightness subsequence

    continuum : Measure
    continuum =
      T5.continuumMeasure (T5.thermodynamic expectationData)

    equalOnDetermining :
      ∀ observable →
      DeterminingObservable authority observable →
      Gram.expectation
        (T5.operations (T5.thermodynamic expectationData))
        cluster observable
      ≡
      Gram.expectation
        (T5.operations (T5.thermodynamic expectationData))
        continuum observable
    equalOnDetermining observable determining =
      Direct.scalarLimitUnique (scalarAuthority authority)
        (λ n →
          Gram.expectation
            (T5.operations (T5.thermodynamic expectationData))
            (Compact.values further n)
            observable)
        (Gram.expectation
          (T5.operations (T5.thermodynamic expectationData))
          cluster observable)
        (Gram.expectation
          (T5.operations (T5.thermodynamic expectationData))
          continuum observable)
        (measureConvergenceImpliesDeterminingExpectationConvergence authority
          (Compact.values further)
          cluster
          (Prokhorov.physicalFurtherSubsequenceConverges
            prokhorov tightness subsequence)
          observable determining)
        (nestedSubsequencePreservesScalarConvergence authority
          subsequence further observable
          (Gram.expectation
            (T5.operations (T5.thermodynamic expectationData))
            continuum observable)
          (T5.boundedWeakConvergenceFromTail
            expectationData observable
            (determiningObservableBounded authority observable determining)))
  in
  determiningExpectationsSeparateMeasures authority
    cluster continuum equalOnDetermining

record LiteralT5CompactnessUniquenessInputs
    {Measure Observable Scalar : Set}
    (expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar) : Set₂ where
  field
    convergence : Limit.SequentialLimit Measure

    TightMeasureSequence : (Nat → Measure) → Set

    everyLiteralDiagonalSubsequenceTight :
      (subsequence :
        Compact.SubsequenceWitness
          (T5.diagonalMeasure expectationData)) →
      TightMeasureSequence (Compact.values subsequence)

    prokhorovAuthority :
      Prokhorov.ProkhorovSubsequenceExtractionAuthority Measure

    determiningUniqueness :
      let selectedTightness : Prokhorov.PhysicalSubsequenceTightnessData Measure
          selectedTightness = record
            { Prokhorov.PhysicalSubsequenceTightnessData.convergence =
                convergence
            ; Prokhorov.PhysicalSubsequenceTightnessData.sequence =
                T5.diagonalMeasure expectationData
            ; Prokhorov.PhysicalSubsequenceTightnessData.TightMeasureSequence =
                TightMeasureSequence
            ; Prokhorov.PhysicalSubsequenceTightnessData.everyLiteralSubsequenceTight =
                everyLiteralDiagonalSubsequenceTight
            }
      in
      DeterminingExpectationUniquenessAuthority
        expectationData
        selectedTightness
        prokhorovAuthority

    compactUniqueFullConvergenceAuthority :
      Compact.CompactUniqueFullConvergenceAuthority Measure

  literalTightness :
    Prokhorov.PhysicalSubsequenceTightnessData Measure
  literalTightness = record
    { Prokhorov.PhysicalSubsequenceTightnessData.convergence = convergence
    ; Prokhorov.PhysicalSubsequenceTightnessData.sequence =
        T5.diagonalMeasure expectationData
    ; Prokhorov.PhysicalSubsequenceTightnessData.TightMeasureSequence =
        TightMeasureSequence
    ; Prokhorov.PhysicalSubsequenceTightnessData.everyLiteralSubsequenceTight =
        everyLiteralDiagonalSubsequenceTight
    }

open LiteralT5CompactnessUniquenessInputs public

asR427CompactUniqueInputs :
  ∀ {Measure Observable Scalar}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar} →
  LiteralT5CompactnessUniquenessInputs expectationData →
  R427.LiteralDiagonalCompactUniqueInputs expectationData
asR427CompactUniqueInputs {expectationData = expectationData} inputs = record
  { R427.LiteralDiagonalCompactUniqueInputs.convergence =
      convergence inputs
  ; R427.LiteralDiagonalCompactUniqueInputs.TightMeasureSequence =
      TightMeasureSequence inputs
  ; R427.LiteralDiagonalCompactUniqueInputs.everyLiteralDiagonalSubsequenceTight =
      everyLiteralDiagonalSubsequenceTight inputs
  ; R427.LiteralDiagonalCompactUniqueInputs.prokhorovAuthority =
      prokhorovAuthority inputs
  ; R427.LiteralDiagonalCompactUniqueInputs.everyExtractedDiagonalClusterPointIsContinuum =
      extractedClusterPointIsSelectedContinuum
        (literalTightness inputs)
        (prokhorovAuthority inputs)
        (determiningUniqueness inputs)
  ; R427.LiteralDiagonalCompactUniqueInputs.compactUniqueFullConvergenceAuthority =
      compactUniqueFullConvergenceAuthority inputs
  }

round430ClusterPointUniquenessCompilerLevel : ProofLevel
round430ClusterPointUniquenessCompilerLevel = machineChecked

round430EveryExtractedClusterPointEqualityLevel : ProofLevel
round430EveryExtractedClusterPointEqualityLevel = machineChecked

round430MeasureExpectationContinuityAuthorityLevel : ProofLevel
round430MeasureExpectationContinuityAuthorityLevel = standardImported

round430ScalarSubsequenceAuthorityLevel : ProofLevel
round430ScalarSubsequenceAuthorityLevel = standardImported

round430DeterminingMeasureAuthorityLevel : ProofLevel
round430DeterminingMeasureAuthorityLevel = standardImported

round430DeterminingClassPhysicalMeaningLevel : ProofLevel
round430DeterminingClassPhysicalMeaningLevel = conditional

round430EveryLiteralSubsequenceTightLevel : ProofLevel
round430EveryLiteralSubsequenceTightLevel = conditional

round430IndependentClusterPointEqualityInputRequired : Bool
round430IndependentClusterPointEqualityInputRequired = false
