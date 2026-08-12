module DASHI.Cognition.PNF.CorpusLearningEconomy where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.ComplexityArithmetic

------------------------------------------------------------------------
-- Corpus learning should make repeated-domain compilation cheaper.
--
-- This is an upper-bound theorem, not a promise about wall-clock time.  The
-- runtime must demonstrate that an enlarged reusable context actually reduces
-- unresolved lookup/resolution work for the SAME identified workload/task.
-- Equal token counts are a throughput normalisation condition, not workload
-- identity: two unrelated 20k-token documents may have very different semantic
-- difficulty.
------------------------------------------------------------------------

record CompilationWork : Set where
  constructor compilationWork
  field
    fixedNumericWork : Nat
    unresolvedResolutionWork : Nat

open CompilationWork public

totalCompilationWork : CompilationWork → Nat
totalCompilationWork work =
  fixedNumericWork work +ᶜ unresolvedResolutionWork work

record ReuseLearningStep (before after : CompilationWork) : Set where
  constructor reuseLearningStep
  field
    fixedWorkUnchanged : fixedNumericWork after ≡ fixedNumericWork before
    unresolvedWorkNotIncreased :
      unresolvedResolutionWork after ≤ᶜ unresolvedResolutionWork before

open ReuseLearningStep public

learningCannotIncreaseDeclaredWorkBound :
  ∀ {before after} →
  ReuseLearningStep before after →
  totalCompilationWork after ≤ᶜ totalCompilationWork before
learningCannotIncreaseDeclaredWorkBound {before} {after} step
  rewrite fixedWorkUnchanged step =
    +ᶜ-monotone-left
      (unresolvedWorkNotIncreased step)
      (fixedNumericWork before)

------------------------------------------------------------------------
-- Comparable repeated-workload receipt.
--
-- workloadId is an opaque runtime identity for the controlled workload.  In the
-- implementation this should be derived from the numeric observation/task/
-- compiler-configuration carrier, not guessed from token count.  The same
-- workload identity plus exact token equality makes the before/after learning
-- comparison meaningful; chronological document order alone does not.
------------------------------------------------------------------------

record CorpusReuseReceipt : Set where
  constructor corpusReuseReceipt
  field
    workloadId : String
    beforeTokenWorkloadUnits : Nat
    afterTokenWorkloadUnits : Nat
    sameTokenWorkload : afterTokenWorkloadUnits ≡ beforeTokenWorkloadUnits
    before : CompilationWork
    after : CompilationWork
    learningStep : ReuseLearningStep before after
    reusedLexicalUnits : Nat
    reusedEntityUnits : Nat
    reusedExternalAlignmentUnits : Nat

open CorpusReuseReceipt public

record CorpusReuseComparison : Set where
  constructor corpusReuseComparison
  field
    beforeReceipt : CorpusReuseReceipt
    afterReceipt : CorpusReuseReceipt
    sameIdentifiedWorkload :
      workloadId beforeReceipt ≡ workloadId afterReceipt
    sameBeforeTokenCarrier :
      beforeTokenWorkloadUnits beforeReceipt
      ≡ beforeTokenWorkloadUnits afterReceipt

open CorpusReuseComparison public

data CacheSizeAloneProvesRuntimeImprovement : Set where

data TokenCountAloneProvesComparableWorkload : Set where

data ChronologicalOrderProvesLearningImprovement : Set where

cacheSizeAloneDoesNotProveRuntimeImprovement :
  CacheSizeAloneProvesRuntimeImprovement → ⊥
cacheSizeAloneDoesNotProveRuntimeImprovement ()

tokenCountAloneDoesNotProveComparableWorkload :
  TokenCountAloneProvesComparableWorkload → ⊥
tokenCountAloneDoesNotProveComparableWorkload ()

chronologicalOrderAloneDoesNotProveLearningImprovement :
  ChronologicalOrderProvesLearningImprovement → ⊥
chronologicalOrderAloneDoesNotProveLearningImprovement ()

record CorpusLearningBoundary : Set where
  constructor corpusLearningBoundary
  field
    laterDocumentsMayReuseEarlierProofBearingStructure : Bool
    laterDocumentsMayReuseEarlierProofBearingStructureIsTrue :
      laterDocumentsMayReuseEarlierProofBearingStructure ≡ true
    reuseMayChangeCanonicalSemanticIdentity : Bool
    reuseMayChangeCanonicalSemanticIdentityIsFalse :
      reuseMayChangeCanonicalSemanticIdentity ≡ false
    repeatedDomainWorkShouldBeMonotoneNonIncreasing : Bool
    repeatedDomainWorkShouldBeMonotoneNonIncreasingIsTrue :
      repeatedDomainWorkShouldBeMonotoneNonIncreasing ≡ true
    equalTokenCountAloneMakesWorkloadsComparable : Bool
    equalTokenCountAloneMakesWorkloadsComparableIsFalse :
      equalTokenCountAloneMakesWorkloadsComparable ≡ false
    chronologicalDocumentOrderProvesLearningImprovement : Bool
    chronologicalDocumentOrderProvesLearningImprovementIsFalse :
      chronologicalDocumentOrderProvesLearningImprovement ≡ false

open CorpusLearningBoundary public

canonicalCorpusLearningBoundary : CorpusLearningBoundary
canonicalCorpusLearningBoundary =
  corpusLearningBoundary
    true refl
    false refl
    true refl
    false refl
    false refl
