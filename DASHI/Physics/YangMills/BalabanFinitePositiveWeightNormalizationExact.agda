module DASHI.Physics.YangMills.BalabanFinitePositiveWeightNormalizationExact where

------------------------------------------------------------------------
-- NONNEGATIVE FINITE WEIGHTS + ONE POSITIVE WITNESS -> PROBABILITY LAW
--
-- This is the generic finite partition-function normalization needed by the
-- corrected Gate4 coarse-law route.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List)
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; Positive; NonNegative; nonNegative; _*_; _≤_)
import Data.Rational.Properties as ℚP
open import Relation.Binary.PropositionalEquality using (sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanPhysicalBlockFibreSumsExact as Sums
import DASHI.Physics.YangMills.BalabanFiniteProbabilityPartitionDisintegrationExact as Finite
import DASHI.Physics.YangMills.BalabanClayGate4ReferenceFibrePositiveMassExact as PositiveMass
import DASHI.Physics.YangMills.BalabanClayGate4RationalPositiveMassReciprocalExact as Reciprocal

record FinitePositiveWeightFamily (State : Set) : Set₁ where
  field
    states : List State
    rawWeight : State → ℚ

    rawWeightNonnegative : ∀ state →
      0ℚ ≤ rawWeight state

    positiveWitness : State
    positiveWitnessInStates :
      PositiveMass._∈_ positiveWitness states
    positiveWitnessWeight :
      Positive (rawWeight positiveWitness)

open FinitePositiveWeightFamily public

totalMass :
  ∀ {State} →
  FinitePositiveWeightFamily State → ℚ
totalMass dataSet =
  Sums.sumRational (states dataSet) (rawWeight dataSet)

totalMassPositive :
  ∀ {State}
    (dataSet : FinitePositiveWeightFamily State) →
  Positive (totalMass dataSet)
totalMassPositive dataSet =
  Finite.sumRationalPositiveAtMember
    (states dataSet)
    (rawWeight dataSet)
    (positiveWitness dataSet)
    (positiveWitnessInStates dataSet)
    (rawWeightNonnegative dataSet)
    (positiveWitnessWeight dataSet)

normalizingReciprocal :
  ∀ {State} →
  FinitePositiveWeightFamily State → ℚ
normalizingReciprocal dataSet =
  Reciprocal.safeRationalReciprocal (totalMass dataSet)

normalizingReciprocalNonnegative :
  ∀ {State}
    (dataSet : FinitePositiveWeightFamily State) →
  0ℚ ≤ normalizingReciprocal dataSet
normalizingReciprocalNonnegative dataSet =
  Reciprocal.safeRationalReciprocalNonnegative
    (totalMass dataSet)
    (totalMassPositive dataSet)

normalizedWeight :
  ∀ {State} →
  FinitePositiveWeightFamily State →
  State → ℚ
normalizedWeight dataSet state =
  normalizingReciprocal dataSet * rawWeight dataSet state

normalizedWeightNonnegative :
  ∀ {State}
    (dataSet : FinitePositiveWeightFamily State)
    state →
  0ℚ ≤ normalizedWeight dataSet state
normalizedWeightNonnegative dataSet state =
  let
    instance
      reciprocalNN : NonNegative (normalizingReciprocal dataSet)
      reciprocalNN = nonNegative
        (normalizingReciprocalNonnegative dataSet)

      rawNN : NonNegative (rawWeight dataSet state)
      rawNN = nonNegative
        (rawWeightNonnegative dataSet state)
  in
  ℚP.nonNegative⁻¹ _

normalizedWeightMassOne :
  ∀ {State}
    (dataSet : FinitePositiveWeightFamily State) →
  Sums.sumRational (states dataSet)
    (normalizedWeight dataSet)
  ≡ 1ℚ
normalizedWeightMassOne dataSet =
  trans
    (Sums.sumRationalScale
      (normalizingReciprocal dataSet)
      (states dataSet)
      (rawWeight dataSet))
    (Reciprocal.safeRationalReciprocalTimesPositive
      (totalMass dataSet)
      (totalMassPositive dataSet))

finitePositiveMassCompilerLevel : ProofLevel
finitePositiveMassCompilerLevel = machineChecked

finiteWeightNormalizationCompilerLevel : ProofLevel
finiteWeightNormalizationCompilerLevel = machineChecked
