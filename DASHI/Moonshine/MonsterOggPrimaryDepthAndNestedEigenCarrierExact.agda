module DASHI.Moonshine.MonsterOggPrimaryDepthAndNestedEigenCarrierExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- John H. Conway and Simon P. Norton,
-- "Monstrous Moonshine",
-- Bulletin of the London Mathematical Society 11 (1979), 308--339.
-- DOI: 10.1112/blms/11.3.308.
--
-- John F. R. Duncan and Ken Ono,
-- "The Jack Daniels Problem",
-- Journal of Number Theory 161 (2016), 230--239.
-- DOI: 10.1016/j.jnt.2015.06.001.
--
-- John F. R. Duncan and Holly Swisher,
-- "Modular Functions and the Monstrous Exponents",
-- arXiv:2602.09135.  No DOI asserted for the preprint.
--
-- DASHI CONTRIBUTION
--
-- Record the exact two-axis profile for every Monster/Ogg prime:
--
--   p      = horizontal cyclic phase resolution;
--   v_p(M) = vertical p-primary depth.
--
-- For odd primes, phase inversion has one fixed label and (p-1)/2 oriented
-- pairs.  A typed nested-eigencarrier contract is supplied without claiming
-- that an actual Monster/modular carrier satisfying it has already been built.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Fin.Base using (Fin)

import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Foundations.Base369CompletedRelationalDigitExact as Cell

monsterPrimaryDepth : Lane.MonsterPrimeLane → Nat
monsterPrimaryDepth Lane.p2 = 46
monsterPrimaryDepth Lane.p3 = 20
monsterPrimaryDepth Lane.p5 = 9
monsterPrimaryDepth Lane.p7 = 6
monsterPrimaryDepth Lane.p11 = 2
monsterPrimaryDepth Lane.p13 = 3
monsterPrimaryDepth Lane.p17 = 1
monsterPrimaryDepth Lane.p19 = 1
monsterPrimaryDepth Lane.p23 = 1
monsterPrimaryDepth Lane.p29 = 1
monsterPrimaryDepth Lane.p31 = 1
monsterPrimaryDepth Lane.p41 = 1
monsterPrimaryDepth Lane.p47 = 1
monsterPrimaryDepth Lane.p59 = 1
monsterPrimaryDepth Lane.p71 = 1

record OggWidthDepthProfile (prime : Lane.MonsterPrimeLane) : Set where
  constructor mkOggWidthDepthProfile
  field
    phaseResolution : Nat
    primaryDepth : Nat
    phaseResolutionExact :
      phaseResolution ≡ Lane.monsterPrimeLaneToNat prime
    primaryDepthExact :
      primaryDepth ≡ monsterPrimaryDepth prime

open OggWidthDepthProfile public

canonicalOggWidthDepthProfile :
  (prime : Lane.MonsterPrimeLane) →
  OggWidthDepthProfile prime
canonicalOggWidthDepthProfile prime =
  mkOggWidthDepthProfile
    (Lane.monsterPrimeLaneToNat prime)
    (monsterPrimaryDepth prime)
    refl
    refl

data OddOggPrime : Set where
  odd3 odd5 odd7 odd11 odd13 odd17 odd19 odd23
    odd29 odd31 odd41 odd47 odd59 odd71 : OddOggPrime

oddToLane : OddOggPrime → Lane.MonsterPrimeLane
oddToLane odd3 = Lane.p3
oddToLane odd5 = Lane.p5
oddToLane odd7 = Lane.p7
oddToLane odd11 = Lane.p11
oddToLane odd13 = Lane.p13
oddToLane odd17 = Lane.p17
oddToLane odd19 = Lane.p19
oddToLane odd23 = Lane.p23
oddToLane odd29 = Lane.p29
oddToLane odd31 = Lane.p31
oddToLane odd41 = Lane.p41
oddToLane odd47 = Lane.p47
oddToLane odd59 = Lane.p59
oddToLane odd71 = Lane.p71

phasePairCount : OddOggPrime → Nat
phasePairCount odd3 = 1
phasePairCount odd5 = 2
phasePairCount odd7 = 3
phasePairCount odd11 = 5
phasePairCount odd13 = 6
phasePairCount odd17 = 8
phasePairCount odd19 = 9
phasePairCount odd23 = 11
phasePairCount odd29 = 14
phasePairCount odd31 = 15
phasePairCount odd41 = 20
phasePairCount odd47 = 23
phasePairCount odd59 = 29
phasePairCount odd71 = 35

oddPhaseDecompositionExact :
  (prime : OddOggPrime) →
  Lane.monsterPrimeLaneToNat (oddToLane prime)
  ≡ 1 + 2 * phasePairCount prime
oddPhaseDecompositionExact odd3 = refl
oddPhaseDecompositionExact odd5 = refl
oddPhaseDecompositionExact odd7 = refl
oddPhaseDecompositionExact odd11 = refl
oddPhaseDecompositionExact odd13 = refl
oddPhaseDecompositionExact odd17 = refl
oddPhaseDecompositionExact odd19 = refl
oddPhaseDecompositionExact odd23 = refl
oddPhaseDecompositionExact odd29 = refl
oddPhaseDecompositionExact odd31 = refl
oddPhaseDecompositionExact odd41 = refl
oddPhaseDecompositionExact odd47 = refl
oddPhaseDecompositionExact odd59 = refl
oddPhaseDecompositionExact odd71 = refl

record PrimeRelationalCell (prime : Lane.MonsterPrimeLane) : Set where
  constructor primeRelationalCell
  field
    cyclicPhase : Fin (Lane.monsterPrimeLaneToNat prime)
    localRelationalCell : Cell.NestedRelationalCell

open PrimeRelationalCell public

iterate : {A : Set} → Nat → (A → A) → A → A
iterate zero step state = state
iterate (suc n) step state = step (iterate n step state)

record OggNestedEigenCarrier
  (prime : Lane.MonsterPrimeLane) : Set₁ where
  constructor mkOggNestedEigenCarrier
  field
    State : Set
    Phase : Set
    Normalizer : Set
    Scale : Set

    symmetry : State → State
    symmetryPowerPIsIdentity :
      (state : State) →
      iterate (Lane.monsterPrimeLaneToNat prime) symmetry state ≡ state

    phaseObservation : State → Phase
    phaseInverse : Phase → Phase
    phaseInverseInvolutive :
      (phase : Phase) → phaseInverse (phaseInverse phase) ≡ phase

    normalizerAction : Normalizer → State → State
    filtrationLevel : State → Scale
    transition : State → State
    stable : State → Set

    relationalCell : State → PrimeRelationalCell prime
    overflow : State → State

open OggNestedEigenCarrier public

record FrickeEigenInversionBridge
  {prime : Lane.MonsterPrimeLane}
  (carrier : OggNestedEigenCarrier prime) : Set₁ where
  constructor mkFrickeEigenInversionBridge
  field
    fricke : State carrier → State carrier
    frickeInvolutive :
      (state : State carrier) → fricke (fricke state) ≡ state
    frickeReversesPhase :
      (state : State carrier) →
      phaseObservation carrier (fricke state)
      ≡ phaseInverse carrier (phaseObservation carrier state)

record ActualNestedEigenCarrierBoundary : Set where
  constructor mkActualNestedEigenCarrierBoundary
  field
    actualOggNestedCarrierConstructed : Bool
    actualOggNestedCarrierConstructedIsFalse :
      actualOggNestedCarrierConstructed ≡ false
    actualFrickeEigenInversionBridgeConstructed : Bool
    actualFrickeEigenInversionBridgeConstructedIsFalse :
      actualFrickeEigenInversionBridgeConstructed ≡ false

canonicalActualNestedEigenCarrierBoundary : ActualNestedEigenCarrierBoundary
canonicalActualNestedEigenCarrierBoundary =
  mkActualNestedEigenCarrierBoundary false refl false refl
