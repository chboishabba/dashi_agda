module DASHI.Physics.YangMills.BalabanClayT5ConfiguredGeometricTailExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; 0ℚ; 1ℚ; _+_; _*_; _≤_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (trans; cong)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literature normalization.
--
-- Tadeusz Bałaban, "Renormalization Group Approach to Lattice Gauge Field
-- Theories. II. Cluster Expansions", Communications in Mathematical Physics
-- 116 (1988), 1--22. DOI: 10.1007/BF01239022
--
-- Roman Kotecký and David Preiss, "Cluster Expansion for Abstract Polymer
-- Models", Communications in Mathematical Physics 103 (1986), 491--498.
-- DOI: 10.1007/BF01211762
--
-- Konrad Osterwalder and Robert Schrader, "Axioms for Euclidean Green's
-- Functions II", Communications in Mathematical Physics 42 (1975), 281--305.
-- DOI: 10.1007/BF01608978
--
-- Relationship: the cluster sources provide connected-tail architecture and OS
-- provides the continuum target.  The explicit dyadic tail below is the DASHI
-- numerical carrier produced after the rooted 1/16 activity estimate.
------------------------------------------------------------------------

halfℚ quarterℚ : ℚ
halfℚ = + 1 / 2
quarterℚ = + 1 / 4

powHalf : Nat → ℚ
powHalf zero = 1ℚ
powHalf (suc n) = halfℚ * powHalf n

rootedShellTail : Nat → ℚ
rootedShellTail n = quarterℚ * powHalf n

powHalfStepExact : ∀ n → powHalf (suc n) ≡ halfℚ * powHalf n
powHalfStepExact n = refl

rootedShellTailLemma : ∀ p → quarterℚ * (halfℚ * p) ≡ halfℚ * (quarterℚ * p)
rootedShellTailLemma = ℚRing.solve-∀

rootedShellTailStepExact : ∀ n →
  rootedShellTail (suc n) ≡ halfℚ * rootedShellTail n
rootedShellTailStepExact n =
  trans
    (cong (quarterℚ *_) (powHalfStepExact n))
    (rootedShellTailLemma (powHalf n))

------------------------------------------------------------------------
-- Physical cluster-tail instance.  Once the boundary-crossing diameter theorem
-- identifies a minimum shell index, all volume dependence is carried by the
-- explicit rootedShellTail sequence.
------------------------------------------------------------------------

record ConfiguredBoundaryClusterTail
    (Cutoff Volume Observable Scalar : Set) : Set₁ where
  field
    rational : ℚ → Scalar
    Distance : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    expectation : Cutoff → Volume → Observable → Scalar
    thermodynamicExpectation : Cutoff → Observable → Scalar
    reflectedProduct : Observable → Observable → Observable

    boundaryShellIndex : Cutoff → Volume → Nat

    onlyBoundaryCrossingClustersContribute : ∀ (cutoff : Cutoff) (volume : Volume) (left right : Observable) → Set
    boundaryCrossingClusterMinimalDiameter : ∀ (cutoff : Cutoff) (volume : Volume) → Set

    boundaryCrossingClusterExponentialBound : ∀ (cutoff : Cutoff) (volume : Volume) (left right : Observable) →
      LessEqual
        (Distance
          (expectation cutoff volume (reflectedProduct left right))
          (thermodynamicExpectation cutoff (reflectedProduct left right)))
        (rational (rootedShellTail (boundaryShellIndex cutoff volume)))

    boundaryShellIndexEscapes : ∀ (cutoff : Cutoff) → Set
    geometricTailVanishes : Set

open ConfiguredBoundaryClusterTail public

finiteVolumeReflectedPairDifferenceBoundConfigured =
  boundaryCrossingClusterExponentialBound

finiteVolumePairTailVanishesConfigured :
  ∀ {Cutoff Volume Observable Scalar}
    (dataSet : ConfiguredBoundaryClusterTail Cutoff Volume Observable Scalar)
    cutoff → Set
finiteVolumePairTailVanishesConfigured dataSet cutoff =
  boundaryShellIndexEscapes dataSet cutoff × geometricTailVanishes dataSet
  where
  open import Data.Product using (_×_)

------------------------------------------------------------------------
-- Continuum diagonal tail: every one-step defect receives an explicit dyadic
-- majorant.  Summability is reduced to the same geometric sequence.
------------------------------------------------------------------------

record ConfiguredContinuumStepTail
    (Cutoff Observable Scalar : Set) : Set₁ where
  field
    rational : ℚ → Scalar
    Distance : Scalar → Scalar → Scalar
    LessEqual : Scalar → Scalar → Set

    expectation : Cutoff → Observable → Scalar
    nextCutoff : Cutoff → Cutoff
    cutoffDepth : Cutoff → Nat

    oneStepObservableExpectationDifferenceBound : ∀ (cutoff : Cutoff) (observable : Observable) →
      LessEqual
        (Distance (expectation cutoff observable)
          (expectation (nextCutoff cutoff) observable))
        (rational (rootedShellTail (cutoffDepth cutoff)))

    cutoffDepthEscapes : Set
    geometricSeriesSummable : Set
    continuumPairTailSummable : ∀ (left right : Observable) → Set
    diagonalPairTailVanishes : ∀ (left right : Observable) → Set

open ConfiguredContinuumStepTail public

oneStepLocalizationDefectSummableConfigured = geometricSeriesSummable

------------------------------------------------------------------------
-- Exponential moments and tightness.  The analytic estimate is isolated to one
-- uniform exponential-moment bound; polynomial moments, uniform integrability
-- and finite-dimensional tightness are downstream consequences.
------------------------------------------------------------------------

record ConfiguredExponentialMomentTail
    (Cutoff Observable Scalar Marginal Measure : Set) : Set₂ where
  field
    lambda : Scalar
    exponentialMomentBound : Observable → Scalar
    RenormalizedObservable : Observable → Set

    uniformExponentialMomentBoundLiteral : ∀ (observable : Observable) →
      RenormalizedObservable observable → Set

    powerBelowFactorialExponentialLiteral : ∀ (degree : Nat) (observable : Observable) → Set
    reflectedProductYoungBoundLiteral : ∀ (left right : Observable) → Set
    reflectedProductExponentialMomentBoundLiteral : ∀ (left right : Observable) → Set
    uniformIntegrabilityOfReflectedProductsLiteral : ∀ (left right : Observable) → Set

    finiteDimensionalMarginal : Nat → Marginal
    continuumMeasure : Measure

    momentTailBoundImpliesFiniteMarginalTightness : ∀ (dimension : Nat) → Set
    finiteDimensionalMarginalTightLiteral : ∀ (dimension : Nat) → Set
    projectiveFamilyConsistencyLiteral : ∀ (lower upper : Nat) → Set
    prokhorovTightnessForGaugeInvariantMarginalsLiteral : Set
    continuumMeasureSubsequenceExistsLiteral : Set
    clusteringImpliesContinuumMeasureUniqueness : Set

open ConfiguredExponentialMomentTail public

configuredDyadicTailArithmeticLevel : ProofLevel
configuredDyadicTailArithmeticLevel = machineChecked

configuredBoundaryTailReductionLevel : ProofLevel
configuredBoundaryTailReductionLevel = machineChecked

configuredContinuumTailReductionLevel : ProofLevel
configuredContinuumTailReductionLevel = machineChecked

physicalClusterDiameterInputsLevel : ProofLevel
physicalClusterDiameterInputsLevel = conditional

physicalExponentialMomentCompactnessInputsLevel : ProofLevel
physicalExponentialMomentCompactnessInputsLevel = conditional
