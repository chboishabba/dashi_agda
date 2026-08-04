module DASHI.Physics.YangMills.BalabanClayT5CumulantLowerBoundNontrivialityExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions",
-- Communications in Mathematical Physics 31 (1973), 83--112.
-- DOI: 10.1007/BF01645738.
--
-- Konrad Osterwalder and Robert Schrader,
-- "Axioms for Euclidean Green's Functions II",
-- Communications in Mathematical Physics 42 (1975), 281--305.
-- DOI: 10.1007/BF01608978.
--
-- DASHI CONTRIBUTION
--
-- Replace a direct continuum nonzero-fourth-cumulant assumption by the finite
-- estimate that an RG calculation can actually prove.  If a fixed positive
-- eta satisfies
--
--   eta <= kappa_4^(n)
--
-- at every cutoff, the cumulants converge, and the closed order interval
-- [eta,infinity) is sequentially closed, then
--
--   eta <= kappa_4
--
-- in the continuum.  Positivity of eta excludes kappa_4=0.  This supplies the
-- non-Gaussian witness used by the existing T5 limit theorem from a uniform
-- finite-cutoff lower bound rather than from an independent continuum field.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

data Empty : Set where

record UniformCumulantLowerBoundData (Scalar : Set) : Set₁ where
  field
    zero eta : Scalar
    finiteCumulant : Nat → Scalar
    continuumCumulant : Scalar

    LessEqual : Scalar → Scalar → Set
    Positive : Scalar → Set
    Converges : (Nat → Scalar) → Scalar → Set

    finiteCumulantsConverge :
      Converges finiteCumulant continuumCumulant

    finiteUniformLowerBound : ∀ cutoff →
      LessEqual eta (finiteCumulant cutoff)

    lowerOrderIntervalClosed :
      ∀ sequence target →
      Converges sequence target →
      (∀ cutoff → LessEqual eta (sequence cutoff)) →
      LessEqual eta target

    etaPositive : Positive eta
    positiveCannotLieBelowZero : ∀ value →
      Positive value → LessEqual value zero → Empty

open UniformCumulantLowerBoundData public

continuumCumulantRetainsLowerBound :
  ∀ {Scalar} →
  (dataSet : UniformCumulantLowerBoundData Scalar) →
  LessEqual dataSet
    (eta dataSet) (continuumCumulant dataSet)
continuumCumulantRetainsLowerBound dataSet =
  lowerOrderIntervalClosed dataSet
    (finiteCumulant dataSet)
    (continuumCumulant dataSet)
    (finiteCumulantsConverge dataSet)
    (finiteUniformLowerBound dataSet)

ContinuumCumulantNonzero :
  ∀ {Scalar} → UniformCumulantLowerBoundData Scalar → Set
ContinuumCumulantNonzero dataSet =
  continuumCumulant dataSet ≡ zero dataSet → Empty

uniformFiniteLowerBoundForcesContinuumNonzero :
  ∀ {Scalar} →
  (dataSet : UniformCumulantLowerBoundData Scalar) →
  ContinuumCumulantNonzero dataSet
uniformFiniteLowerBoundForcesContinuumNonzero dataSet continuumIsZero =
  positiveCannotLieBelowZero dataSet
    (eta dataSet)
    (etaPositive dataSet)
    (substituteRight continuumIsZero
      (continuumCumulantRetainsLowerBound dataSet))
  where
  substituteRight :
    ∀ {left right target} →
    right ≡ target →
    LessEqual dataSet left right →
    LessEqual dataSet left target
  substituteRight refl bound = bound

record GaussianVanishingData (Measure Observable Scalar : Set) : Set₁ where
  field
    continuumMeasure : Measure
    witnessObservable : Observable
    fourthConnectedCumulant : Measure → Observable → Scalar
    zero : Scalar

    GeneralizedGaussian : Measure → Set
    gaussianFourthCumulantVanishes :
      GeneralizedGaussian continuumMeasure →
      fourthConnectedCumulant continuumMeasure witnessObservable ≡ zero

open GaussianVanishingData public

Not : Set → Set
Not proposition = proposition → Empty

continuumCumulantLowerBoundExcludesGaussian :
  ∀ {Measure Observable Scalar}
    (lowerBound : UniformCumulantLowerBoundData Scalar)
    (gaussianData : GaussianVanishingData Measure Observable Scalar) →
  continuumCumulant lowerBound
    ≡ fourthConnectedCumulant gaussianData
        (continuumMeasure gaussianData)
        (witnessObservable gaussianData) →
  zero lowerBound ≡ zero gaussianData →
  Not (GeneralizedGaussian gaussianData
    (continuumMeasure gaussianData))
continuumCumulantLowerBoundExcludesGaussian
    lowerBound gaussianData cumulantIdentification zeroIdentification gaussian =
  uniformFiniteLowerBoundForcesContinuumNonzero lowerBound
    (transitiveEquality
      cumulantIdentification
      (transitiveEquality
        (gaussianFourthCumulantVanishes gaussianData gaussian)
        (reverseEquality zeroIdentification)))
  where
  transitiveEquality : ∀ {A : Set} {x y z : A} →
    x ≡ y → y ≡ z → x ≡ z
  transitiveEquality refl second = second

  reverseEquality : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
  reverseEquality refl = refl

uniformCumulantLimitLowerBoundLevel : ProofLevel
uniformCumulantLimitLowerBoundLevel = machineChecked

finiteCumulantToContinuumNontrivialityLevel : ProofLevel
finiteCumulantToContinuumNontrivialityLevel = machineChecked

continuumNonGaussianFromCumulantLevel : ProofLevel
continuumNonGaussianFromCumulantLevel = machineChecked
