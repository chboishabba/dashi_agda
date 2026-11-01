{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayT5BoundedExpectationWeakTopologyRound438Exact where

------------------------------------------------------------------------
-- ROUND438 / DECLARE THE SELECTED WEAK TOPOLOGY BY BOUNDED T5 EXPECTATIONS
--
-- R435 still stored as a physical premise that measure convergence implies
-- convergence of the same bounded T5 expectations.  On the preferred weak
-- topology this implication should be definitional:
--
--   mu_n -> mu
--
-- means
--
--   for every bounded selected T5 observable F,
--   E_{mu_n}[F] -> E_mu[F].
--
-- This does NOT manufacture compactness, Prokhorov extraction, or the theorem
-- that the bounded cylinder class separates physical measures.  Those remain
-- genuine mathematical inputs.  It only removes one duplicated topology
-- continuity payment.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanClayT5ThermodynamicUniformIntegrabilityExact as T5
import DASHI.Physics.YangMills.BalabanClayT5CompactUniqueFullSequenceExact as LegacySubsequence
import DASHI.Physics.YangMills.BalabanClayT5SelectedSequentialConvergenceExact as Selected
import DASHI.Physics.YangMills.BalabanClayT5SelectedWeakExpectationClosureExact as Weak
import DASHI.Physics.YangMills.BalabanClayT5DirectExpectationPropertyClosureExact as Direct
import DASHI.Physics.YangMills.BalabanClayT5SelectedProkhorovExtractionExact as Prokhorov

BoundedExpectationConverges :
  ∀ {Measure Observable Scalar} →
  T5.PhysicalExpectationProducerData Measure Observable Scalar →
  (Nat → Measure) → Measure → Set
BoundedExpectationConverges expectationData sequence target =
  ∀ observable →
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

boundedExpectationSequentialConvergence :
  ∀ {Measure Observable Scalar} →
  T5.PhysicalExpectationProducerData Measure Observable Scalar →
  Selected.SequentialConvergence Measure
boundedExpectationSequentialConvergence expectationData = record
  { Selected.SequentialConvergence.Converges =
      BoundedExpectationConverges expectationData
  }

record BoundedExpectationWeakTopologyAuthority
    {Measure Observable Scalar : Set}
    (expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar) : Set₂ where
  field
    scalarAuthority :
      Direct.ScalarExpectationClosureAuthority expectationData

    scalarConvergenceRestrictsToSubsequence :
      ∀ sequence target →
      Gram.Converges
        (T5.scalarConvergence (T5.thermodynamic expectationData))
        sequence target →
      (subsequence : LegacySubsequence.SubsequenceWitness sequence) →
      Gram.Converges
        (T5.scalarConvergence (T5.thermodynamic expectationData))
        (LegacySubsequence.values subsequence) target

    -- This is the remaining determining-class theorem.
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

open BoundedExpectationWeakTopologyAuthority public

compileBoundedExpectationWeakTopology :
  ∀ {Measure Observable Scalar}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar} →
  BoundedExpectationWeakTopologyAuthority expectationData →
  Weak.SelectedWeakExpectationTopology
    Measure Observable Scalar
    (boundedExpectationSequentialConvergence expectationData)
compileBoundedExpectationWeakTopology
    {expectationData = expectationData} authority = record
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
      Direct.scalarConvergenceCongruent (scalarAuthority authority)
  ; Weak.SelectedWeakExpectationTopology.scalarLimitUnique =
      Direct.scalarLimitUnique (scalarAuthority authority)
  ; Weak.SelectedWeakExpectationTopology.scalarConvergenceRestrictsToSubsequence =
      scalarConvergenceRestrictsToSubsequence authority
  ; Weak.SelectedWeakExpectationTopology.expectationContinuous =
      λ sequence target observable convergence bounded →
        convergence observable bounded
  }

------------------------------------------------------------------------
-- Literal selected tightness in exactly this declared weak topology.
------------------------------------------------------------------------

record BoundedWeakSelectedTightness
    {Measure Observable Scalar : Set}
    (expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar) : Set₂ where
  field
    TightMeasureSequence : (Nat → Measure) → Set

    everyLiteralDiagonalSubsequenceTight :
      (subsequence :
        LegacySubsequence.SubsequenceWitness
          (T5.diagonalMeasure expectationData)) →
      TightMeasureSequence (LegacySubsequence.values subsequence)

open BoundedWeakSelectedTightness public

asSelectedSubsequenceTightnessData :
  ∀ {Measure Observable Scalar}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar} →
  BoundedWeakSelectedTightness expectationData →
  Prokhorov.SelectedSubsequenceTightnessData Measure
asSelectedSubsequenceTightnessData
    {expectationData = expectationData} tightness = record
  { Prokhorov.SelectedSubsequenceTightnessData.convergence =
      boundedExpectationSequentialConvergence expectationData
  ; Prokhorov.SelectedSubsequenceTightnessData.sequence =
      T5.diagonalMeasure expectationData
  ; Prokhorov.SelectedSubsequenceTightnessData.TightMeasureSequence =
      TightMeasureSequence tightness
  ; Prokhorov.SelectedSubsequenceTightnessData.everyLiteralSubsequenceTight =
      everyLiteralDiagonalSubsequenceTight tightness
  }

------------------------------------------------------------------------
-- P2 + weak-topology extraction -> unique selected continuum cluster point.
------------------------------------------------------------------------

extractedClusterPointIsSelectedContinuum :
  ∀ {Measure Observable Scalar}
    {expectationData :
      T5.PhysicalExpectationProducerData Measure Observable Scalar}
    (authority :
      BoundedExpectationWeakTopologyAuthority expectationData)
    (tightness :
      BoundedWeakSelectedTightness expectationData)
    (prokhorov :
      Prokhorov.SelectedProkhorovAuthority Measure)
    (subsequence :
      LegacySubsequence.SubsequenceWitness
        (T5.diagonalMeasure expectationData)) →
  Prokhorov.clusterLimit prokhorov
    (asSelectedSubsequenceTightnessData tightness)
    subsequence
  ≡
  T5.continuumMeasure (T5.thermodynamic expectationData)
extractedClusterPointIsSelectedContinuum
    {expectationData = expectationData}
    authority tightness prokhorov subsequence =
  let
    topology = compileBoundedExpectationWeakTopology authority
    tightData = asSelectedSubsequenceTightnessData tightness
    further = Prokhorov.selectedFurther prokhorov tightData subsequence

    cluster =
      Prokhorov.clusterLimit prokhorov tightData subsequence

    continuum =
      T5.continuumMeasure (T5.thermodynamic expectationData)

    equalOnBounded :
      ∀ observable →
      T5.BoundedObservable
        (T5.thermodynamic expectationData) observable →
      Gram.expectation
        (T5.operations (T5.thermodynamic expectationData))
        cluster observable
      ≡
      Gram.expectation
        (T5.operations (T5.thermodynamic expectationData))
        continuum observable
    equalOnBounded observable bounded =
      let
        clusterConvergence =
          Prokhorov.extractedConverges prokhorov
            tightData subsequence

        clusterExpectationConvergence =
          clusterConvergence observable bounded

        fullExpectationConvergence =
          T5.boundedWeakConvergenceFromTail
            expectationData observable bounded

        firstRestriction =
          Weak.scalarConvergenceRestrictsToSubsequence topology
            _ _ fullExpectationConvergence
            (Weak.scalarSubsequenceWitness topology observable subsequence)

        secondRestriction =
          Weak.scalarConvergenceRestrictsToSubsequence topology
            _ _ firstRestriction
            (Weak.scalarSubsequenceWitness topology observable further)
      in
      Weak.scalarLimitUnique topology
        _
        (Gram.expectation
          (T5.operations (T5.thermodynamic expectationData))
          cluster observable)
        (Gram.expectation
          (T5.operations (T5.thermodynamic expectationData))
          continuum observable)
        clusterExpectationConvergence
        secondRestriction
  in
  boundedExpectationsDetermineMeasures authority
    cluster continuum equalOnBounded

round438BoundedWeakTopologyCompilerLevel : ProofLevel
round438BoundedWeakTopologyCompilerLevel = machineChecked

round438ExpectationContinuityByDefinitionLevel : ProofLevel
round438ExpectationContinuityByDefinitionLevel = machineChecked

round438ClusterPointUniquenessCompilerLevel : ProofLevel
round438ClusterPointUniquenessCompilerLevel = machineChecked

round438ScalarSubsequenceAuthorityLevel : ProofLevel
round438ScalarSubsequenceAuthorityLevel = standardImported

round438SelectedProkhorovAuthorityLevel : ProofLevel
round438SelectedProkhorovAuthorityLevel = standardImported

round438BoundedDeterminingClassMeaningLevel : ProofLevel
round438BoundedDeterminingClassMeaningLevel = conditional

round438IndependentMeasureContinuityTheoremRequired : Bool
round438IndependentMeasureContinuityTheoremRequired = false
