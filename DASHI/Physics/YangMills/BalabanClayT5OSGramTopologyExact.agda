module DASHI.Physics.YangMills.BalabanClayT5OSGramTopologyExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT5LimitAndNontrivialityExact as Limit

------------------------------------------------------------------------
-- Literature normalization.
--
-- K. Osterwalder and R. Schrader,
-- "Axioms for Euclidean Green's functions",
-- Communications in Mathematical Physics 31 (1973), 83--112.
-- DOI: 10.1007/BF01645738
--
-- K. Osterwalder and R. Schrader,
-- "Axioms for Euclidean Green's functions II",
-- Communications in Mathematical Physics 42 (1975), 281--305.
-- DOI: 10.1007/BF01608978
--
-- P. Menotti and A. Pelissetto,
-- "General proof of Osterwalder-Schrader positivity for the Wilson action",
-- Communications in Mathematical Physics 113 (1987), 369--373.
-- DOI: 10.1007/BF01221251
--
-- Reflection positivity is positivity of every finite reflected Gram quadratic
-- form.  Pointwise convergence of individual correlators is not used here.
-- The convergence premise is explicitly the convergence of each complete Gram
-- quadratic form in a scalar topology whose nonnegative cone is sequentially
-- closed.
------------------------------------------------------------------------

record OSGramLimitData (Schwinger TestFamily Scalar : Set) : Set₁ where
  field
    finiteSchwinger : Nat → Schwinger
    continuumSchwinger : Schwinger

    -- A TestFamily packages a finite positive-time family together with its
    -- complex coefficients.  The resulting scalar is the full reflected Gram
    -- quadratic form, including all cross terms.
    reflectedGramQuadraticForm : Schwinger → TestFamily → Scalar

    scalarLimit : Limit.SequentialLimit Scalar
    Nonnegative : Scalar → Set

    -- This is the topology-strength requirement.  It is stronger than merely
    -- asserting pointwise convergence of the underlying correlators.
    gramQuadraticFormConverges : ∀ testFamily →
      Limit.Converges scalarLimit
        (λ cutoff → reflectedGramQuadraticForm
          (finiteSchwinger cutoff) testFamily)
        (reflectedGramQuadraticForm continuumSchwinger testFamily)

    finiteGramNonnegative : ∀ cutoff testFamily →
      Nonnegative
        (reflectedGramQuadraticForm (finiteSchwinger cutoff) testFamily)

    nonnegativeConeClosed : ∀ sequence target →
      Limit.Converges scalarLimit sequence target →
      (∀ cutoff → Nonnegative (sequence cutoff)) →
      Nonnegative target

open OSGramLimitData public

GramReflectionPositive :
  ∀ {Schwinger TestFamily Scalar} →
  OSGramLimitData Schwinger TestFamily Scalar → Schwinger → Set
GramReflectionPositive dataSet schwinger = ∀ testFamily →
  Nonnegative dataSet
    (reflectedGramQuadraticForm dataSet schwinger testFamily)

continuumGramNonnegative :
  ∀ {Schwinger TestFamily Scalar}
    (dataSet : OSGramLimitData Schwinger TestFamily Scalar)
    testFamily →
  Nonnegative dataSet
    (reflectedGramQuadraticForm dataSet
      (continuumSchwinger dataSet) testFamily)
continuumGramNonnegative dataSet testFamily =
  nonnegativeConeClosed dataSet
    (λ cutoff → reflectedGramQuadraticForm dataSet
      (finiteSchwinger dataSet cutoff) testFamily)
    (reflectedGramQuadraticForm dataSet
      (continuumSchwinger dataSet) testFamily)
    (gramQuadraticFormConverges dataSet testFamily)
    (λ cutoff → finiteGramNonnegative dataSet cutoff testFamily)

continuumReflectionPositiveFromGramTopology :
  ∀ {Schwinger TestFamily Scalar}
    (dataSet : OSGramLimitData Schwinger TestFamily Scalar) →
  GramReflectionPositive dataSet (continuumSchwinger dataSet)
continuumReflectionPositiveFromGramTopology dataSet =
  continuumGramNonnegative dataSet

record MeasureToSchwingerGramClosure
    (Measure Schwinger TestFamily Scalar : Set) : Set₁ where
  field
    measureSequence : Nat → Measure
    continuumMeasure : Measure
    schwinger : Measure → Schwinger

    gramLimit : OSGramLimitData Schwinger TestFamily Scalar

    finiteSchwingerMatches : ∀ cutoff →
      finiteSchwinger gramLimit cutoff ≡ schwinger (measureSequence cutoff)
    continuumSchwingerMatches :
      continuumSchwinger gramLimit ≡ schwinger continuumMeasure

open MeasureToSchwingerGramClosure public

measureLimitReflectionPositive :
  ∀ {Measure Schwinger TestFamily Scalar}
    (dataSet : MeasureToSchwingerGramClosure
      Measure Schwinger TestFamily Scalar) →
  GramReflectionPositive (gramLimit dataSet)
    (schwinger dataSet (continuumMeasure dataSet))
measureLimitReflectionPositive dataSet =
  subst
    (GramReflectionPositive (gramLimit dataSet))
    (continuumSchwingerMatches dataSet)
    (continuumReflectionPositiveFromGramTopology (gramLimit dataSet))

osGramQuadraticFormClosureLevel : ProofLevel
osGramQuadraticFormClosureLevel = machineChecked

osNonnegativeConeClosureLevel : ProofLevel
osNonnegativeConeClosureLevel = machineChecked

measureToSchwingerGramClosureLevel : ProofLevel
measureToSchwingerGramClosureLevel = machineChecked

-- The literal continuum producer must prove convergence of these finite Gram
-- quadratic forms uniformly over each admitted test family.  Pointwise or weak
-- convergence without that theorem is deliberately insufficient.
physicalOSGramTopologyIdentificationLevel : ProofLevel
physicalOSGramTopologyIdentificationLevel = conditional
