module DASHI.Cognition.PNF.CorpusLearningEconomy where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.ComplexityArithmetic

------------------------------------------------------------------------
-- Corpus learning should make repeated-domain compilation cheaper.
--
-- This is an upper-bound theorem, not a promise about wall-clock time.  The
-- runtime must demonstrate that an enlarged reusable context actually reduces
-- unresolved lookup/resolution work for the same token workload.
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
-- A stronger runtime target: when at least one formerly unresolved unit is
-- reused and fixed work is unchanged, the declared work bound should strictly
-- improve.  The tiny local arithmetic kernel does not define strict order, so
-- the runtime records the before/after totals and the non-increase theorem above
-- remains the proof-level invariant.
------------------------------------------------------------------------

record CorpusReuseReceipt : Set where
  constructor corpusReuseReceipt
  field
    tokenWorkloadUnits : Nat
    before : CompilationWork
    after : CompilationWork
    sameTokenWorkload : Nat
    sameTokenWorkloadIsExact : sameTokenWorkload ≡ tokenWorkloadUnits
    learningStep : ReuseLearningStep before after
    reusedLexicalUnits : Nat
    reusedEntityUnits : Nat
    reusedExternalAlignmentUnits : Nat

open CorpusReuseReceipt public

data CacheSizeAloneProvesRuntimeImprovement : Set where

cacheSizeAloneDoesNotProveRuntimeImprovement :
  CacheSizeAloneProvesRuntimeImprovement → ⊥
cacheSizeAloneDoesNotProveRuntimeImprovement ()

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

open CorpusLearningBoundary public

canonicalCorpusLearningBoundary : CorpusLearningBoundary
canonicalCorpusLearningBoundary =
  corpusLearningBoundary true refl false refl true refl
