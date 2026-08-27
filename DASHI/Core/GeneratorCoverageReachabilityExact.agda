module DASHI.Core.GeneratorCoverageReachabilityExact where

------------------------------------------------------------------------
-- LOCAL MOVE COVERAGE IS NOT GLOBAL STATE-SPACE COVERAGE
--
-- A transition vocabulary can be completely witnessed somewhere in a sampled
-- system while some ordered pair of states remains unreachable.  This module
-- keeps those two quantifier patterns distinct.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Core.TrajectoryResidueExact as Path

LabeledStep : Set → Set → Set₁
LabeledStep State Generator = Generator → State → State → Set

ErasedStep :
  ∀ {State Generator : Set} →
  LabeledStep State Generator →
  State → State → Set
ErasedStep {Generator = Generator} step x y =
  Σ Generator (λ generator → step generator x y)

GeneratorWitnessed :
  ∀ {State Generator : Set} →
  LabeledStep State Generator →
  Generator →
  Set
GeneratorWitnessed {State = State} step generator =
  Σ State (λ x → Σ State (λ y → step generator x y))

AllGeneratorsWitnessed :
  ∀ {State Generator : Set} →
  LabeledStep State Generator →
  Set
AllGeneratorsWitnessed {Generator = Generator} step =
  (generator : Generator) → GeneratorWitnessed step generator

UniversallyReachable :
  ∀ {State Generator : Set} →
  LabeledStep State Generator →
  Set
UniversallyReachable step =
  ∀ x y → Path.Trace (ErasedStep step) x y

------------------------------------------------------------------------
-- Exact non-entailment witness theorem.
--
-- To refute the implication in a concrete transition system, it is enough to
-- supply (i) complete generator coverage and (ii) one unreachable ordered pair.
------------------------------------------------------------------------

coverageWithUnreachablePairRefutesUniversalEntailment :
  ∀ {State Generator : Set}
    {step : LabeledStep State Generator}
    {x y : State} →
  AllGeneratorsWitnessed step →
  ¬ Path.Trace (ErasedStep step) x y →
  ¬ (AllGeneratorsWitnessed step → UniversallyReachable step)
coverageWithUnreachablePairRefutesUniversalEntailment coverage noPath entailment =
  noPath (entailment coverage _ _)

record GeneratorCoverageBoundary : Set where
  constructor generatorCoverageBoundary
  field
    localGeneratorCoverageTypedSeparatelyFromReachability : Bool
    localGeneratorCoverageTypedSeparatelyFromReachabilityIsTrue :
      localGeneratorCoverageTypedSeparatelyFromReachability ≡ true

    completeObservedMoveVocabularyAutomaticallyMeansUniversalReachability : Bool
    completeObservedMoveVocabularyAutomaticallyMeansUniversalReachabilityIsFalse :
      completeObservedMoveVocabularyAutomaticallyMeansUniversalReachability ≡ false

canonicalGeneratorCoverageBoundary : GeneratorCoverageBoundary
canonicalGeneratorCoverageBoundary =
  generatorCoverageBoundary true refl false refl
