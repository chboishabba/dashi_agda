{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5SelectedWeakTopologyMeaningRound435Exact where

------------------------------------------------------------------------
-- ROUND435 / SAME T5 EXPECTATIONS = SELECTED WEAK MEASURE TOPOLOGY
--
-- One physical semantics seam should feed H2b, H2c and reflected-Gram closure:
--
--   measure convergence controls expectations of the SAME bounded T5 tests;
--   scalar convergence is Hausdorff and stable under literal subsequences;
--   those bounded expectations determine the physical measure.
--
-- R435 compiles that seam into both:
--   * SelectedWeakExpectationTopology; and
--   * R430's determining-expectation uniqueness authority.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5CompactUniqueFullSequenceExact as Compact
import DASHI.Physics.YangMills.BalabanClayT5SubsequenceProkhorovExtractionExact as Prokhorov
import DASHI.Physics.YangMills.BalabanClayT5SelectedSequentialConvergenceExact as Selected
import DASHI.Physics.YangMills.BalabanClayT5SelectedWeakExpectationClosureExact as Weak
import DASHI.Physics.YangMills.BalabanClayT5DirectExpectationPropertyClosureExact as Direct
import DASHI.Physics.YangMills.BalabanClayT5ClusterPointUniquenessRound430Exact as R430

record SelectedT5WeakTopologyMeaning
    {Measure Observable Scalar : Set}
    (expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar)
    (tightness :
      Prokhorov.PhysicalSubsequenceTightnessData Measure) : Set₂ where
  field
    scalarAuthority :
      Direct.ScalarExpectationClosureAuthority expectationData

    scalarConvergenceRestrictsToSubsequence :
      ∀ sequence target →
      Gram.Converges
        (T5.scalarConvergence (T5.thermodynamic expectationData))
        sequence target →
      (subsequence : Compact.SubsequenceWitness sequence) →
      Gram.Converges
        (T5.scalarConvergence (T5.thermodynamic expectationData))
        (Compact.values subsequence) target

    -- This is the central physical topology identification.
    measureConvergenceControlsBoundedExpectations :
      ∀ sequence target observable →
      Limit.Converges (Prokhorov.convergence tightness) sequence target →
      T5.BoundedObservable
        (T5.thermodynamic expectationData) observable →
      Gram.Converges
        (T5.scalarConvergence (T5.thermodynamic expectationData))
        (λ n →
          Gram.expectation
            (T5.operations (T5.thermodynamic expectationData))
            (sequence n) observable)
        (Gram.expectation
          (T5.operations (T5.thermodynamic expectationData))
          target observable)

    -- Physical determining-class meaning.  No clustering theorem is used.
    boundedExpectationsDetermineMeasures :
      ∀ left right →
      (∀ observable →
        T5.BoundedObservable
          (T5.thermodynamic expectationData) observable →
        Gram.expectation
          (T5.operations (T5.thermodynamic expectationData))
          left observable
        ≡
        Gram.expectation
          (T5.operations (T5.thermodynamic expectationData))
          right observable) →
      left ≡ right

open SelectedT5WeakTopologyMeaning public

selectedMeasureConvergence :
  ∀ {Measure}
    (tightness : Prokhorov.PhysicalSubsequenceTightnessData Measure) →
  Selected.SequentialConvergence Measure
selectedMeasureConvergence tightness = record
  { Selected.SequentialConvergence.Converges =
      Limit.Converges (Prokhorov.convergence tightness)
  }

compileSelectedWeakExpectationTopology :
  ∀ {Measure Observable Scalar}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar}
    {tightness :
      Prokhorov.PhysicalSubsequenceTightnessData Measure} →
  SelectedT5WeakTopologyMeaning expectationData tightness →
  Weak.SelectedWeakExpectationTopology
    Measure Observable Scalar (selectedMeasureConvergence tightness)
compileSelectedWeakExpectationTopology
    {expectationData = expectationData} {tightness = tightness}
    meaning = record
  { Weak.SelectedWeakExpectationTopology.expectation =
      Gram.expectation
        (T5.operations (T5.thermodynamic expectationData))
  ; Weak.SelectedWeakExpectationTopology.AdmissibleTest =
      T5.BoundedObservable (T5.thermodynamic expectationData)
  ; Weak.SelectedWeakExpectationTopology.ScalarConverges =
      Gram.Converges
        (T5.scalarConvergence (T5.thermodynamic expectationData))
  ; Weak.SelectedWeakExpectationTopology.scalarConstantConverges =
      Gram.constantConverges
        (T5.scalarConvergence (T5.thermodynamic expectationData))
  ; Weak.SelectedWeakExpectationTopology.scalarConvergenceCongruent =
      Direct.scalarConvergenceCongruent (scalarAuthority meaning)
  ; Weak.SelectedWeakExpectationTopology.scalarLimitUnique =
      Direct.scalarLimitUnique (scalarAuthority meaning)
  ; Weak.SelectedWeakExpectationTopology.scalarConvergenceRestrictsToSubsequence =
      scalarConvergenceRestrictsToSubsequence meaning
  ; Weak.SelectedWeakExpectationTopology.expectationContinuous =
      measureConvergenceControlsBoundedExpectations meaning
  }

asR430DeterminingExpectationAuthority :
  ∀ {Measure Observable Scalar}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar}
    {tightness :
      Prokhorov.PhysicalSubsequenceTightnessData Measure}
    {prokhorov :
      Prokhorov.ProkhorovSubsequenceExtractionAuthority Measure} →
  SelectedT5WeakTopologyMeaning expectationData tightness →
  R430.DeterminingExpectationUniquenessAuthority
    expectationData tightness prokhorov
asR430DeterminingExpectationAuthority
    {expectationData = expectationData}
    {tightness = tightness}
    meaning = record
  { R430.DeterminingExpectationUniquenessAuthority.DeterminingObservable =
      T5.BoundedObservable (T5.thermodynamic expectationData)
  ; R430.DeterminingExpectationUniquenessAuthority.determiningObservableBounded =
      λ observable bounded → bounded
  ; R430.DeterminingExpectationUniquenessAuthority.scalarAuthority =
      scalarAuthority meaning
  ; R430.DeterminingExpectationUniquenessAuthority.measureConvergenceImpliesDeterminingExpectationConvergence =
      measureConvergenceControlsBoundedExpectations meaning
  ; R430.DeterminingExpectationUniquenessAuthority.nestedSubsequencePreservesScalarConvergence =
      λ subsequence further observable target convergence →
        let
          topology = compileSelectedWeakExpectationTopology meaning
          first =
            Weak.scalarConvergenceRestrictsToSubsequence topology
              _ _ convergence
              (Weak.scalarSubsequenceWitness topology observable subsequence)
        in
        Weak.scalarConvergenceRestrictsToSubsequence topology
          _ _ first
          (Weak.scalarSubsequenceWitness topology observable further)
  ; R430.DeterminingExpectationUniquenessAuthority.determiningExpectationsSeparateMeasures =
      boundedExpectationsDetermineMeasures meaning
  }

round435SelectedWeakTopologyCompilerLevel : ProofLevel
round435SelectedWeakTopologyCompilerLevel = machineChecked

round435R430DeterminingAuthorityCompilerLevel : ProofLevel
round435R430DeterminingAuthorityCompilerLevel = machineChecked

round435ScalarTopologyAuthoritiesLevel : ProofLevel
round435ScalarTopologyAuthoritiesLevel = standardImported

round435SelectedMeasureWeakExpectationMeaningLevel : ProofLevel
round435SelectedMeasureWeakExpectationMeaningLevel = conditional

round435BoundedDeterminingClassMeaningLevel : ProofLevel
round435BoundedDeterminingClassMeaningLevel = conditional

round435IndependentClusterPointAgreementRequired : Bool
round435IndependentClusterPointAgreementRequired = false
