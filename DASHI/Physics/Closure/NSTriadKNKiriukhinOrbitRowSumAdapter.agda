module DASHI.Physics.Closure.NSTriadKNKiriukhinOrbitRowSumAdapter where

------------------------------------------------------------------------
-- PROVENANCE
-- Author: Oleg Kiriukhin.
-- Title: "Orbit-Level Transfer Matrix for the 3D Fourier-Galerkin
-- Navier-Stokes System on the Periodic Torus: Explicit Orbit-Triad
-- Incidence Bounds and Deterministic Row-Sum Estimates".
-- Venue/year: arXiv:2604.12188v1, submitted 14 April 2026; manuscript
-- dated March 2026.
-- DOI: 10.48550/arXiv.2604.12188.
-- Uses: Proposition 4.9, Proposition 5.1, Proposition 6.2, Theorem 6.5,
-- Remarks 5.3, 6.4, and 6.6.
-- Relationship: exposes the cited raw orbit-row theorem and its precise
-- range and limitations. It does not promote the paper's raw row estimate
-- into a shell, helical, column, symmetric-part, or operator theorem without
-- the explicit adapters represented below.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat.Base using (_≤_)

record RationalExponent : Set where
  constructor exponent
  field
    numerator denominator : Nat

open RationalExponent public

threeHalves fiveHalves two three : RationalExponent
threeHalves = exponent 3 2
fiveHalves = exponent 5 2
two = exponent 2 1
three = exponent 3 1

data KiriukhinSobolevWindow : Set where
  paperWindow cutoffUniformWindow officialOverlapWindow :
    KiriukhinSobolevWindow

record KiriukhinRawOrbitCarrier
    {c m o s r : Level} : Set (lsuc (c ⊔ m ⊔ o ⊔ s ⊔ r)) where
  field
    Cutoff : Set c
    Mode : Set m
    Orbit : Set o
    State : Set s
    Scalar : Set r

    zero : Scalar
    add multiply : Scalar → Scalar → Scalar
    absolute : Scalar → Scalar
    leq : Scalar → Scalar → Set r

    cutoffMember : Cutoff → Mode → Set
    nonzeroMode : Mode → Set
    orbitOf : Mode → Orbit
    orbitRepresentative : Orbit → Mode
    orbitCardinality : Orbit → Nat
    modeNorm : Mode → Scalar

    rawOrbitTransfer : Cutoff → State → Orbit → Orbit → Scalar
    rawOrbitRowAbsoluteSum : Cutoff → State → Orbit → Scalar
    rawOrbitColumnAbsoluteSum : Cutoff → State → Orbit → Scalar

    sobolevNormBound : State → Scalar
    rowProfile : RationalExponent → Orbit → Scalar
    cubicNormBound : State → Scalar

open KiriukhinRawOrbitCarrier public

record KiriukhinRawOrbitRowTheorem
    {c m o s r : Level}
    (C : KiriukhinRawOrbitCarrier {c} {m} {o} {s} {r}) :
    Set (lsuc (c ⊔ m ⊔ o ⊔ s ⊔ r)) where
  field
    cubicGalerkinConventionMatches : Set
    fullOctahedralOrbitConventionMatches : Set
    orderedTriadConventionMatches : Set
    orbitCardinalityNormalizationMatches : Set
    lerayConventionMatches : Set
    realityMateConventionMatches : Set
    zeroModeExclusionMatches : Set

    exactModeLevelTriadCountAvailable : Set
    faceNormalizedPatchDecompositionAvailable : Set
    twoSquaresPatchBoundAvailable : Set
    orbitTriadIncidenceNFourPlusEpsilonAvailable : Set
    orbitEnstrophyIdentityAvailable : Set
    rawMatrixAntisymmetricSymmetricSplitAvailable : Set

    paperExponent : RationalExponent
    paperExponentInRange : Set

    deterministicRawOrbitRowEstimate :
      ∀ cutoff state orbit →
      leq C
        (rawOrbitRowAbsoluteSum C cutoff state orbit)
        (multiply C
          (cubicNormBound C state)
          (rowProfile C paperExponent orbit))

    cutoffUniformForTwoBelowSBelowThree : Set
    officialOverlapRequiresFiveHalvesBelowSBelowThree : Set
    upperEndpointThreeNotIncluded : Set

    rawRowOnly : Set
    noRawColumnEstimateClaimed : Set
    noSymmetricPartOperatorEstimateClaimed : Set
    extensionBeyondSBelowThreeRequiresDiscreteInput : Set

open KiriukhinRawOrbitRowTheorem public

record KiriukhinAdapterObligations
    {c m o s r : Level}
    (C : KiriukhinRawOrbitCarrier {c} {m} {o} {s} {r}) :
    Set (lsuc (c ⊔ m ⊔ o ⊔ s ⊔ r)) where
  field
    sourceTheorem : KiriukhinRawOrbitRowTheorem C
    repositoryRawKernelIdentified : Set
    cubicCutoffBridgeClosed : Set
    orbitNormalizationBridgeClosed : Set
    euclideanToDyadicShellBridgeClosed : Set
    sevenClassPartitionBridgeClosed : Set
    helicalResolutionBridgeClosed : Set
    weightedColumnOrDualTrilinearBoundClosed : Set

open KiriukhinAdapterObligations public

kiriukhinRawRowSourceAvailable : Bool
kiriukhinRawRowSourceAvailable = true

kiriukhinRawRowSourceAvailableIsTrue :
  kiriukhinRawRowSourceAvailable ≡ true
kiriukhinRawRowSourceAvailableIsTrue = refl

kiriukhinOfficialAdapterClosed : Bool
kiriukhinOfficialAdapterClosed = false

kiriukhinOfficialAdapterClosedIsFalse :
  kiriukhinOfficialAdapterClosed ≡ false
kiriukhinOfficialAdapterClosedIsFalse = refl

kiriukhinColumnSourceAvailable : Bool
kiriukhinColumnSourceAvailable = false

kiriukhinColumnSourceAvailableIsFalse :
  kiriukhinColumnSourceAvailable ≡ false
kiriukhinColumnSourceAvailableIsFalse = refl
