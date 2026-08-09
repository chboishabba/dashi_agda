module DASHI.Biology.EisensteinThreeSixSymmetryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Serge Lang,
-- "Algebraic Number Theory", second edition, Springer, 1994.
-- DOI: 10.1007/978-1-4612-0853-2.
--
-- DASHI CONTRIBUTION
--
-- Separate the canonical threefold phase cycle
--
--   1 -> omega -> omega^2 -> 1
--
-- from the six units of the Eisenstein integers
--
--   +/-1, +/-omega, +/-omega^2.
--
-- The three phases encode three equally spaced alternatives with no
-- privileged middle.  The six units add sign/opposition.  Neither statement
-- identifies a ternary state count with a six-coordinate state space.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.EisensteinNineRingInterferenceExact as E

data TernaryPhase : Set where
  phaseOne phaseOmega phaseOmegaSquared : TernaryPhase

nextPhase : TernaryPhase → TernaryPhase
nextPhase phaseOne = phaseOmega
nextPhase phaseOmega = phaseOmegaSquared
nextPhase phaseOmegaSquared = phaseOne

threePhaseCycleCloses :
  (phase : TernaryPhase) →
  nextPhase (nextPhase (nextPhase phase)) ≡ phase
threePhaseCycleCloses phaseOne = refl
threePhaseCycleCloses phaseOmega = refl
threePhaseCycleCloses phaseOmegaSquared = refl

phaseAmplitude : TernaryPhase → E.Eisenstein
phaseAmplitude phaseOne = E.one
phaseAmplitude phaseOmega = E.omega
phaseAmplitude phaseOmegaSquared = E.omegaSquared

symmetricPhaseResultant : E.Eisenstein
symmetricPhaseResultant =
  E.add
    (phaseAmplitude phaseOne)
    (E.add
      (phaseAmplitude phaseOmega)
      (phaseAmplitude phaseOmegaSquared))

symmetricPhaseResultantRealIsZero :
  E.realCoordinate symmetricPhaseResultant ≡ E.0ℚ
symmetricPhaseResultantRealIsZero = E.threePhaseCancellationReal

symmetricPhaseResultantOmegaIsZero :
  E.omegaCoordinate symmetricPhaseResultant ≡ E.0ℚ
symmetricPhaseResultantOmegaIsZero = E.threePhaseCancellationOmega

data Opposition : Set where
  positive negative : Opposition

data EisensteinUnit : Set where
  plusOne minusOne
  plusOmega minusOmega
  plusOmegaSquared minusOmegaSquared : EisensteinUnit

unitPhase : EisensteinUnit → TernaryPhase
unitPhase plusOne = phaseOne
unitPhase minusOne = phaseOne
unitPhase plusOmega = phaseOmega
unitPhase minusOmega = phaseOmega
unitPhase plusOmegaSquared = phaseOmegaSquared
unitPhase minusOmegaSquared = phaseOmegaSquared

unitOpposition : EisensteinUnit → Opposition
unitOpposition plusOne = positive
unitOpposition minusOne = negative
unitOpposition plusOmega = positive
unitOpposition minusOmega = negative
unitOpposition plusOmegaSquared = positive
unitOpposition minusOmegaSquared = negative

phaseAndOppositionDetermineUnit :
  TernaryPhase → Opposition → EisensteinUnit
phaseAndOppositionDetermineUnit phaseOne positive = plusOne
phaseAndOppositionDetermineUnit phaseOne negative = minusOne
phaseAndOppositionDetermineUnit phaseOmega positive = plusOmega
phaseAndOppositionDetermineUnit phaseOmega negative = minusOmega
phaseAndOppositionDetermineUnit phaseOmegaSquared positive = plusOmegaSquared
phaseAndOppositionDetermineUnit phaseOmegaSquared negative = minusOmegaSquared

recoverUnit :
  (unit : EisensteinUnit) →
  phaseAndOppositionDetermineUnit
    (unitPhase unit)
    (unitOpposition unit)
  ≡ unit
recoverUnit plusOne = refl
recoverUnit minusOne = refl
recoverUnit plusOmega = refl
recoverUnit minusOmega = refl
recoverUnit plusOmegaSquared = refl
recoverUnit minusOmegaSquared = refl

ternaryPhaseCount : Nat
ternaryPhaseCount = 3

oppositionCount : Nat
oppositionCount = 2

eisensteinUnitCount : Nat
eisensteinUnitCount = ternaryPhaseCount * oppositionCount

eisensteinUnitCountIsSix : eisensteinUnitCount ≡ 6
eisensteinUnitCountIsSix = refl

record ThreeSixBoundary : Set where
  constructor threeSixBoundary
  field
    threeMeansSymmetricPhaseCycle : Bool
    threeMeansSymmetricPhaseCycleIsTrue :
      threeMeansSymmetricPhaseCycle ≡ true
    sixMeansPhaseWithOpposition : Bool
    sixMeansPhaseWithOppositionIsTrue :
      sixMeansPhaseWithOpposition ≡ true
    zeroResultantMeansNoAlternativesExist : Bool
    zeroResultantMeansNoAlternativesExistIsFalse :
      zeroResultantMeansNoAlternativesExist ≡ false
    ternaryPhasesAreOrderedMinusZeroPlusScale : Bool
    ternaryPhasesAreOrderedMinusZeroPlusScaleIsFalse :
      ternaryPhasesAreOrderedMinusZeroPlusScale ≡ false
    abstractPhaseCarrierIsPhysicalQuantumPhase : Bool
    abstractPhaseCarrierIsPhysicalQuantumPhaseIsFalse :
      abstractPhaseCarrierIsPhysicalQuantumPhase ≡ false

canonicalThreeSixBoundary : ThreeSixBoundary
canonicalThreeSixBoundary =
  threeSixBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
