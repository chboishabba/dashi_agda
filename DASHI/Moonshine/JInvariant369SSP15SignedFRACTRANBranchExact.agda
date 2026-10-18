module DASHI.Moonshine.JInvariant369SSP15SignedFRACTRANBranchExact where

------------------------------------------------------------------------
-- SSP15 -> SIGNED MULTIPLICITY -> FRACTRAN BRANCH
--
-- This module closes the right-hand branch from the finite 15-state carrier:
--
--   T^2 / +/- -> 5 modes
--   5 x {-1,0,+1} -> SSP15InternalLane
--   chosen carrier indexing <-> 15 Ogg/SSP prime lanes
--   pointed signed lane state
--   full SSP valuation
--   existing FRACTRAN weave state/program machinery
--
-- Critical distinction:
-- a zero signed multiplicity does NOT remember which of the five neutral
-- internal lanes produced it.  Therefore the faithful intermediate state is
--
--   SSPPrime x SignedMultiplicity,
--
-- not merely SSPValuation.  The selected/support lane is retained explicitly.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Agda.Builtin.List using (List)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Completion
import DASHI.Biology.SSP15ComplementPhaseProjectorExact as Internal
import DASHI.Biology.SSP15JCoarseFineIntegratedExact as Integrated
import DASHI.Biology.SignedSSPFRACTRANWeaveExact as Signed
import DASHI.Physics.Closure.MoonshinePrimeLaneReceiptSurface as Lane
import DASHI.Moonshine.JInvariant369NeutralCuspRelationCrossPollinationExact as Neutral

------------------------------------------------------------------------
-- 1. Explicit CHOSEN 15 <-> 15 carrier indexing.
--
-- This is an ordinal/indexing equivalence only.  It does not assert that the
-- internal mode/phase semantics are intrinsically the arithmetic prime
-- semantics.  That stronger promotion remains blocked.
------------------------------------------------------------------------

primeToInternal :
  Lane.MonsterPrimeLane →
  Internal.SSP15InternalLane
primeToInternal Lane.p2  = Completion.mode09 , Harmonic.negativeTrit
primeToInternal Lane.p3  = Completion.mode09 , Harmonic.zeroTrit
primeToInternal Lane.p5  = Completion.mode09 , Harmonic.positiveTrit
primeToInternal Lane.p7  = Completion.mode18 , Harmonic.negativeTrit
primeToInternal Lane.p11 = Completion.mode18 , Harmonic.zeroTrit
primeToInternal Lane.p13 = Completion.mode18 , Harmonic.positiveTrit
primeToInternal Lane.p17 = Completion.mode27 , Harmonic.negativeTrit
primeToInternal Lane.p19 = Completion.mode27 , Harmonic.zeroTrit
primeToInternal Lane.p23 = Completion.mode27 , Harmonic.positiveTrit
primeToInternal Lane.p29 = Completion.mode36 , Harmonic.negativeTrit
primeToInternal Lane.p31 = Completion.mode36 , Harmonic.zeroTrit
primeToInternal Lane.p41 = Completion.mode36 , Harmonic.positiveTrit
primeToInternal Lane.p47 = Completion.mode45 , Harmonic.negativeTrit
primeToInternal Lane.p59 = Completion.mode45 , Harmonic.zeroTrit
primeToInternal Lane.p71 = Completion.mode45 , Harmonic.positiveTrit

internalToPrime :
  Internal.SSP15InternalLane →
  Lane.MonsterPrimeLane
internalToPrime (Completion.mode09 , Harmonic.negativeTrit) = Lane.p2
internalToPrime (Completion.mode09 , Harmonic.zeroTrit) = Lane.p3
internalToPrime (Completion.mode09 , Harmonic.positiveTrit) = Lane.p5
internalToPrime (Completion.mode18 , Harmonic.negativeTrit) = Lane.p7
internalToPrime (Completion.mode18 , Harmonic.zeroTrit) = Lane.p11
internalToPrime (Completion.mode18 , Harmonic.positiveTrit) = Lane.p13
internalToPrime (Completion.mode27 , Harmonic.negativeTrit) = Lane.p17
internalToPrime (Completion.mode27 , Harmonic.zeroTrit) = Lane.p19
internalToPrime (Completion.mode27 , Harmonic.positiveTrit) = Lane.p23
internalToPrime (Completion.mode36 , Harmonic.negativeTrit) = Lane.p29
internalToPrime (Completion.mode36 , Harmonic.zeroTrit) = Lane.p31
internalToPrime (Completion.mode36 , Harmonic.positiveTrit) = Lane.p41
internalToPrime (Completion.mode45 , Harmonic.negativeTrit) = Lane.p47
internalToPrime (Completion.mode45 , Harmonic.zeroTrit) = Lane.p59
internalToPrime (Completion.mode45 , Harmonic.positiveTrit) = Lane.p71

internalAfterPrime :
  (prime : Lane.MonsterPrimeLane) →
  internalToPrime (primeToInternal prime) ≡ prime
internalAfterPrime Lane.p2 = refl
internalAfterPrime Lane.p3 = refl
internalAfterPrime Lane.p5 = refl
internalAfterPrime Lane.p7 = refl
internalAfterPrime Lane.p11 = refl
internalAfterPrime Lane.p13 = refl
internalAfterPrime Lane.p17 = refl
internalAfterPrime Lane.p19 = refl
internalAfterPrime Lane.p23 = refl
internalAfterPrime Lane.p29 = refl
internalAfterPrime Lane.p31 = refl
internalAfterPrime Lane.p41 = refl
internalAfterPrime Lane.p47 = refl
internalAfterPrime Lane.p59 = refl
internalAfterPrime Lane.p71 = refl

primeAfterInternal :
  (lane : Internal.SSP15InternalLane) →
  primeToInternal (internalToPrime lane) ≡ lane
primeAfterInternal (Completion.mode09 , Harmonic.negativeTrit) = refl
primeAfterInternal (Completion.mode09 , Harmonic.zeroTrit) = refl
primeAfterInternal (Completion.mode09 , Harmonic.positiveTrit) = refl
primeAfterInternal (Completion.mode18 , Harmonic.negativeTrit) = refl
primeAfterInternal (Completion.mode18 , Harmonic.zeroTrit) = refl
primeAfterInternal (Completion.mode18 , Harmonic.positiveTrit) = refl
primeAfterInternal (Completion.mode27 , Harmonic.negativeTrit) = refl
primeAfterInternal (Completion.mode27 , Harmonic.zeroTrit) = refl
primeAfterInternal (Completion.mode27 , Harmonic.positiveTrit) = refl
primeAfterInternal (Completion.mode36 , Harmonic.negativeTrit) = refl
primeAfterInternal (Completion.mode36 , Harmonic.zeroTrit) = refl
primeAfterInternal (Completion.mode36 , Harmonic.positiveTrit) = refl
primeAfterInternal (Completion.mode45 , Harmonic.negativeTrit) = refl
primeAfterInternal (Completion.mode45 , Harmonic.zeroTrit) = refl
primeAfterInternal (Completion.mode45 , Harmonic.positiveTrit) = refl

chosenOggInternalLaneBijection :
  Integrated.OggInternalLaneBijection
chosenOggInternalLaneBijection =
  record
    { forward = primeToInternal
    ; backward = internalToPrime
    ; backwardAfterForward = internalAfterPrime
    ; forwardAfterBackward = primeAfterInternal
    }

------------------------------------------------------------------------
-- 1b. Ogg-prime carrier <-> signed-FRACTRAN prime carrier.
--
-- These are independent repository datatypes with the same fifteen numerical
-- prime labels.  Keep the bridge explicit.
------------------------------------------------------------------------

lanePrimeToSignedPrime :
  Lane.MonsterPrimeLane →
  Signed.SSPPrime
lanePrimeToSignedPrime Lane.p2 = Signed.ssp2
lanePrimeToSignedPrime Lane.p3 = Signed.ssp3
lanePrimeToSignedPrime Lane.p5 = Signed.ssp5
lanePrimeToSignedPrime Lane.p7 = Signed.ssp7
lanePrimeToSignedPrime Lane.p11 = Signed.ssp11
lanePrimeToSignedPrime Lane.p13 = Signed.ssp13
lanePrimeToSignedPrime Lane.p17 = Signed.ssp17
lanePrimeToSignedPrime Lane.p19 = Signed.ssp19
lanePrimeToSignedPrime Lane.p23 = Signed.ssp23
lanePrimeToSignedPrime Lane.p29 = Signed.ssp29
lanePrimeToSignedPrime Lane.p31 = Signed.ssp31
lanePrimeToSignedPrime Lane.p41 = Signed.ssp41
lanePrimeToSignedPrime Lane.p47 = Signed.ssp47
lanePrimeToSignedPrime Lane.p59 = Signed.ssp59
lanePrimeToSignedPrime Lane.p71 = Signed.ssp71

signedPrimeToLanePrime :
  Signed.SSPPrime →
  Lane.MonsterPrimeLane
signedPrimeToLanePrime Signed.ssp2 = Lane.p2
signedPrimeToLanePrime Signed.ssp3 = Lane.p3
signedPrimeToLanePrime Signed.ssp5 = Lane.p5
signedPrimeToLanePrime Signed.ssp7 = Lane.p7
signedPrimeToLanePrime Signed.ssp11 = Lane.p11
signedPrimeToLanePrime Signed.ssp13 = Lane.p13
signedPrimeToLanePrime Signed.ssp17 = Lane.p17
signedPrimeToLanePrime Signed.ssp19 = Lane.p19
signedPrimeToLanePrime Signed.ssp23 = Lane.p23
signedPrimeToLanePrime Signed.ssp29 = Lane.p29
signedPrimeToLanePrime Signed.ssp31 = Lane.p31
signedPrimeToLanePrime Signed.ssp41 = Lane.p41
signedPrimeToLanePrime Signed.ssp47 = Lane.p47
signedPrimeToLanePrime Signed.ssp59 = Lane.p59
signedPrimeToLanePrime Signed.ssp71 = Lane.p71

laneAfterSignedPrime :
  (prime : Signed.SSPPrime) →
  lanePrimeToSignedPrime (signedPrimeToLanePrime prime) ≡ prime
laneAfterSignedPrime Signed.ssp2 = refl
laneAfterSignedPrime Signed.ssp3 = refl
laneAfterSignedPrime Signed.ssp5 = refl
laneAfterSignedPrime Signed.ssp7 = refl
laneAfterSignedPrime Signed.ssp11 = refl
laneAfterSignedPrime Signed.ssp13 = refl
laneAfterSignedPrime Signed.ssp17 = refl
laneAfterSignedPrime Signed.ssp19 = refl
laneAfterSignedPrime Signed.ssp23 = refl
laneAfterSignedPrime Signed.ssp29 = refl
laneAfterSignedPrime Signed.ssp31 = refl
laneAfterSignedPrime Signed.ssp41 = refl
laneAfterSignedPrime Signed.ssp47 = refl
laneAfterSignedPrime Signed.ssp59 = refl
laneAfterSignedPrime Signed.ssp71 = refl

signedAfterLanePrime :
  (prime : Lane.MonsterPrimeLane) →
  signedPrimeToLanePrime (lanePrimeToSignedPrime prime) ≡ prime
signedAfterLanePrime Lane.p2 = refl
signedAfterLanePrime Lane.p3 = refl
signedAfterLanePrime Lane.p5 = refl
signedAfterLanePrime Lane.p7 = refl
signedAfterLanePrime Lane.p11 = refl
signedAfterLanePrime Lane.p13 = refl
signedAfterLanePrime Lane.p17 = refl
signedAfterLanePrime Lane.p19 = refl
signedAfterLanePrime Lane.p23 = refl
signedAfterLanePrime Lane.p29 = refl
signedAfterLanePrime Lane.p31 = refl
signedAfterLanePrime Lane.p41 = refl
signedAfterLanePrime Lane.p47 = refl
signedAfterLanePrime Lane.p59 = refl
signedAfterLanePrime Lane.p71 = refl

------------------------------------------------------------------------
-- 2. Balanced phase -> unit signed multiplicity.
------------------------------------------------------------------------

phaseToUnitMultiplicity :
  Harmonic.BalancedTrit →
  Signed.SignedMultiplicity
phaseToUnitMultiplicity Harmonic.negativeTrit =
  Signed.negativeMultiplicity 1
phaseToUnitMultiplicity Harmonic.zeroTrit =
  Signed.zeroMultiplicity
phaseToUnitMultiplicity Harmonic.positiveTrit =
  Signed.positiveMultiplicity 1

unitMultiplicityToPhase :
  Signed.SignedMultiplicity →
  Harmonic.BalancedTrit
unitMultiplicityToPhase (Signed.negativeMultiplicity n) =
  Harmonic.negativeTrit
unitMultiplicityToPhase Signed.zeroMultiplicity =
  Harmonic.zeroTrit
unitMultiplicityToPhase (Signed.positiveMultiplicity n) =
  Harmonic.positiveTrit

phaseCoarseRoundTrip :
  (phase : Harmonic.BalancedTrit) →
  unitMultiplicityToPhase (phaseToUnitMultiplicity phase) ≡ phase
phaseCoarseRoundTrip Harmonic.negativeTrit = refl
phaseCoarseRoundTrip Harmonic.zeroTrit = refl
phaseCoarseRoundTrip Harmonic.positiveTrit = refl

------------------------------------------------------------------------
-- 3. Faithful pointed signed state.
------------------------------------------------------------------------

record PointedSignedSSPLane : Set where
  constructor pointed-signed-ssp-lane
  field
    selectedPrime : Lane.MonsterPrimeLane
    signedMultiplicity : Signed.SignedMultiplicity

open PointedSignedSSPLane public

internalLaneToPointedSigned :
  Internal.SSP15InternalLane →
  PointedSignedSSPLane
internalLaneToPointedSigned (mode , phase) =
  pointed-signed-ssp-lane
    (internalToPrime (mode , phase))
    (phaseToUnitMultiplicity phase)

pointedSignedToCoarseInternal :
  PointedSignedSSPLane →
  Internal.SSP15InternalLane
pointedSignedToCoarseInternal state =
  let lane = primeToInternal (selectedPrime state)
  in
  proj₁ lane , unitMultiplicityToPhase (signedMultiplicity state)

internalPointedCoarseRoundTrip :
  (lane : Internal.SSP15InternalLane) →
  pointedSignedToCoarseInternal (internalLaneToPointedSigned lane) ≡ lane
internalPointedCoarseRoundTrip (Completion.mode09 , Harmonic.negativeTrit) = refl
internalPointedCoarseRoundTrip (Completion.mode09 , Harmonic.zeroTrit) = refl
internalPointedCoarseRoundTrip (Completion.mode09 , Harmonic.positiveTrit) = refl
internalPointedCoarseRoundTrip (Completion.mode18 , Harmonic.negativeTrit) = refl
internalPointedCoarseRoundTrip (Completion.mode18 , Harmonic.zeroTrit) = refl
internalPointedCoarseRoundTrip (Completion.mode18 , Harmonic.positiveTrit) = refl
internalPointedCoarseRoundTrip (Completion.mode27 , Harmonic.negativeTrit) = refl
internalPointedCoarseRoundTrip (Completion.mode27 , Harmonic.zeroTrit) = refl
internalPointedCoarseRoundTrip (Completion.mode27 , Harmonic.positiveTrit) = refl
internalPointedCoarseRoundTrip (Completion.mode36 , Harmonic.negativeTrit) = refl
internalPointedCoarseRoundTrip (Completion.mode36 , Harmonic.zeroTrit) = refl
internalPointedCoarseRoundTrip (Completion.mode36 , Harmonic.positiveTrit) = refl
internalPointedCoarseRoundTrip (Completion.mode45 , Harmonic.negativeTrit) = refl
internalPointedCoarseRoundTrip (Completion.mode45 , Harmonic.zeroTrit) = refl
internalPointedCoarseRoundTrip (Completion.mode45 , Harmonic.positiveTrit) = refl

------------------------------------------------------------------------
-- 4. Pointed state -> full SSP valuation.
------------------------------------------------------------------------

signedPrimeEqual :
  Signed.SSPPrime →
  Signed.SSPPrime →
  Bool
signedPrimeEqual Signed.ssp2 Signed.ssp2 = true
signedPrimeEqual Signed.ssp3 Signed.ssp3 = true
signedPrimeEqual Signed.ssp5 Signed.ssp5 = true
signedPrimeEqual Signed.ssp7 Signed.ssp7 = true
signedPrimeEqual Signed.ssp11 Signed.ssp11 = true
signedPrimeEqual Signed.ssp13 Signed.ssp13 = true
signedPrimeEqual Signed.ssp17 Signed.ssp17 = true
signedPrimeEqual Signed.ssp19 Signed.ssp19 = true
signedPrimeEqual Signed.ssp23 Signed.ssp23 = true
signedPrimeEqual Signed.ssp29 Signed.ssp29 = true
signedPrimeEqual Signed.ssp31 Signed.ssp31 = true
signedPrimeEqual Signed.ssp41 Signed.ssp41 = true
signedPrimeEqual Signed.ssp47 Signed.ssp47 = true
signedPrimeEqual Signed.ssp59 Signed.ssp59 = true
signedPrimeEqual Signed.ssp71 Signed.ssp71 = true
signedPrimeEqual left right = false

pointedSignedValuation :
  PointedSignedSSPLane →
  Signed.SSPValuation
pointedSignedValuation state prime
  with signedPrimeEqual (lanePrimeToSignedPrime (selectedPrime state)) prime
... | true = signedMultiplicity state
... | false = Signed.zeroMultiplicity

pointedValuationOwnLane :
  (state : PointedSignedSSPLane) →
  pointedSignedValuation state (lanePrimeToSignedPrime (selectedPrime state))
  ≡ signedMultiplicity state
pointedValuationOwnLane
  (pointed-signed-ssp-lane Lane.p2 multiplicity) = refl
pointedValuationOwnLane
  (pointed-signed-ssp-lane Lane.p3 multiplicity) = refl
pointedValuationOwnLane
  (pointed-signed-ssp-lane Lane.p5 multiplicity) = refl
pointedValuationOwnLane
  (pointed-signed-ssp-lane Lane.p7 multiplicity) = refl
pointedValuationOwnLane
  (pointed-signed-ssp-lane Lane.p11 multiplicity) = refl
pointedValuationOwnLane
  (pointed-signed-ssp-lane Lane.p13 multiplicity) = refl
pointedValuationOwnLane
  (pointed-signed-ssp-lane Lane.p17 multiplicity) = refl
pointedValuationOwnLane
  (pointed-signed-ssp-lane Lane.p19 multiplicity) = refl
pointedValuationOwnLane
  (pointed-signed-ssp-lane Lane.p23 multiplicity) = refl
pointedValuationOwnLane
  (pointed-signed-ssp-lane Lane.p29 multiplicity) = refl
pointedValuationOwnLane
  (pointed-signed-ssp-lane Lane.p31 multiplicity) = refl
pointedValuationOwnLane
  (pointed-signed-ssp-lane Lane.p41 multiplicity) = refl
pointedValuationOwnLane
  (pointed-signed-ssp-lane Lane.p47 multiplicity) = refl
pointedValuationOwnLane
  (pointed-signed-ssp-lane Lane.p59 multiplicity) = refl
pointedValuationOwnLane
  (pointed-signed-ssp-lane Lane.p71 multiplicity) = refl

------------------------------------------------------------------------
-- 5. Neutral-lane obstruction.
--
-- All zero-multiplicity pointed states compile to the SAME zero valuation.
-- Therefore SSPValuation alone cannot remember which neutral mode/prime was
-- selected.  The pointed selectedPrime coordinate is genuinely necessary.
------------------------------------------------------------------------

neutralPointed :
  Lane.MonsterPrimeLane →
  PointedSignedSSPLane
neutralPointed prime =
  pointed-signed-ssp-lane prime Signed.zeroMultiplicity

neutralValuationIsZeroAt :
  (selected : Lane.MonsterPrimeLane) →
  (observed : Signed.SSPPrime) →
  pointedSignedValuation (neutralPointed selected) observed
  ≡ Signed.zeroMultiplicity
neutralValuationIsZeroAt Lane.p2 observed with observed
... | Signed.ssp2 = refl
... | Signed.ssp3 = refl
... | Signed.ssp5 = refl
... | Signed.ssp7 = refl
... | Signed.ssp11 = refl
... | Signed.ssp13 = refl
... | Signed.ssp17 = refl
... | Signed.ssp19 = refl
... | Signed.ssp23 = refl
... | Signed.ssp29 = refl
... | Signed.ssp31 = refl
... | Signed.ssp41 = refl
... | Signed.ssp47 = refl
... | Signed.ssp59 = refl
... | Signed.ssp71 = refl
neutralValuationIsZeroAt Lane.p3 observed with observed
... | Signed.ssp2 = refl
... | Signed.ssp3 = refl
... | Signed.ssp5 = refl
... | Signed.ssp7 = refl
... | Signed.ssp11 = refl
... | Signed.ssp13 = refl
... | Signed.ssp17 = refl
... | Signed.ssp19 = refl
... | Signed.ssp23 = refl
... | Signed.ssp29 = refl
... | Signed.ssp31 = refl
... | Signed.ssp41 = refl
... | Signed.ssp47 = refl
... | Signed.ssp59 = refl
... | Signed.ssp71 = refl
neutralValuationIsZeroAt Lane.p5 observed with observed
... | Signed.ssp2 = refl
... | Signed.ssp3 = refl
... | Signed.ssp5 = refl
... | Signed.ssp7 = refl
... | Signed.ssp11 = refl
... | Signed.ssp13 = refl
... | Signed.ssp17 = refl
... | Signed.ssp19 = refl
... | Signed.ssp23 = refl
... | Signed.ssp29 = refl
... | Signed.ssp31 = refl
... | Signed.ssp41 = refl
... | Signed.ssp47 = refl
... | Signed.ssp59 = refl
... | Signed.ssp71 = refl
neutralValuationIsZeroAt Lane.p7 observed with observed
... | Signed.ssp2 = refl
... | Signed.ssp3 = refl
... | Signed.ssp5 = refl
... | Signed.ssp7 = refl
... | Signed.ssp11 = refl
... | Signed.ssp13 = refl
... | Signed.ssp17 = refl
... | Signed.ssp19 = refl
... | Signed.ssp23 = refl
... | Signed.ssp29 = refl
... | Signed.ssp31 = refl
... | Signed.ssp41 = refl
... | Signed.ssp47 = refl
... | Signed.ssp59 = refl
... | Signed.ssp71 = refl
neutralValuationIsZeroAt Lane.p11 observed with observed
... | Signed.ssp2 = refl
... | Signed.ssp3 = refl
... | Signed.ssp5 = refl
... | Signed.ssp7 = refl
... | Signed.ssp11 = refl
... | Signed.ssp13 = refl
... | Signed.ssp17 = refl
... | Signed.ssp19 = refl
... | Signed.ssp23 = refl
... | Signed.ssp29 = refl
... | Signed.ssp31 = refl
... | Signed.ssp41 = refl
... | Signed.ssp47 = refl
... | Signed.ssp59 = refl
... | Signed.ssp71 = refl
neutralValuationIsZeroAt Lane.p13 observed with observed
... | Signed.ssp2 = refl
... | Signed.ssp3 = refl
... | Signed.ssp5 = refl
... | Signed.ssp7 = refl
... | Signed.ssp11 = refl
... | Signed.ssp13 = refl
... | Signed.ssp17 = refl
... | Signed.ssp19 = refl
... | Signed.ssp23 = refl
... | Signed.ssp29 = refl
... | Signed.ssp31 = refl
... | Signed.ssp41 = refl
... | Signed.ssp47 = refl
... | Signed.ssp59 = refl
... | Signed.ssp71 = refl
neutralValuationIsZeroAt Lane.p17 observed with observed
... | Signed.ssp2 = refl
... | Signed.ssp3 = refl
... | Signed.ssp5 = refl
... | Signed.ssp7 = refl
... | Signed.ssp11 = refl
... | Signed.ssp13 = refl
... | Signed.ssp17 = refl
... | Signed.ssp19 = refl
... | Signed.ssp23 = refl
... | Signed.ssp29 = refl
... | Signed.ssp31 = refl
... | Signed.ssp41 = refl
... | Signed.ssp47 = refl
... | Signed.ssp59 = refl
... | Signed.ssp71 = refl
neutralValuationIsZeroAt Lane.p19 observed with observed
... | Signed.ssp2 = refl
... | Signed.ssp3 = refl
... | Signed.ssp5 = refl
... | Signed.ssp7 = refl
... | Signed.ssp11 = refl
... | Signed.ssp13 = refl
... | Signed.ssp17 = refl
... | Signed.ssp19 = refl
... | Signed.ssp23 = refl
... | Signed.ssp29 = refl
... | Signed.ssp31 = refl
... | Signed.ssp41 = refl
... | Signed.ssp47 = refl
... | Signed.ssp59 = refl
... | Signed.ssp71 = refl
neutralValuationIsZeroAt Lane.p23 observed with observed
... | Signed.ssp2 = refl
... | Signed.ssp3 = refl
... | Signed.ssp5 = refl
... | Signed.ssp7 = refl
... | Signed.ssp11 = refl
... | Signed.ssp13 = refl
... | Signed.ssp17 = refl
... | Signed.ssp19 = refl
... | Signed.ssp23 = refl
... | Signed.ssp29 = refl
... | Signed.ssp31 = refl
... | Signed.ssp41 = refl
... | Signed.ssp47 = refl
... | Signed.ssp59 = refl
... | Signed.ssp71 = refl
neutralValuationIsZeroAt Lane.p29 observed with observed
... | Signed.ssp2 = refl
... | Signed.ssp3 = refl
... | Signed.ssp5 = refl
... | Signed.ssp7 = refl
... | Signed.ssp11 = refl
... | Signed.ssp13 = refl
... | Signed.ssp17 = refl
... | Signed.ssp19 = refl
... | Signed.ssp23 = refl
... | Signed.ssp29 = refl
... | Signed.ssp31 = refl
... | Signed.ssp41 = refl
... | Signed.ssp47 = refl
... | Signed.ssp59 = refl
... | Signed.ssp71 = refl
neutralValuationIsZeroAt Lane.p31 observed with observed
... | Signed.ssp2 = refl
... | Signed.ssp3 = refl
... | Signed.ssp5 = refl
... | Signed.ssp7 = refl
... | Signed.ssp11 = refl
... | Signed.ssp13 = refl
... | Signed.ssp17 = refl
... | Signed.ssp19 = refl
... | Signed.ssp23 = refl
... | Signed.ssp29 = refl
... | Signed.ssp31 = refl
... | Signed.ssp41 = refl
... | Signed.ssp47 = refl
... | Signed.ssp59 = refl
... | Signed.ssp71 = refl
neutralValuationIsZeroAt Lane.p41 observed with observed
... | Signed.ssp2 = refl
... | Signed.ssp3 = refl
... | Signed.ssp5 = refl
... | Signed.ssp7 = refl
... | Signed.ssp11 = refl
... | Signed.ssp13 = refl
... | Signed.ssp17 = refl
... | Signed.ssp19 = refl
... | Signed.ssp23 = refl
... | Signed.ssp29 = refl
... | Signed.ssp31 = refl
... | Signed.ssp41 = refl
... | Signed.ssp47 = refl
... | Signed.ssp59 = refl
... | Signed.ssp71 = refl
neutralValuationIsZeroAt Lane.p47 observed with observed
... | Signed.ssp2 = refl
... | Signed.ssp3 = refl
... | Signed.ssp5 = refl
... | Signed.ssp7 = refl
... | Signed.ssp11 = refl
... | Signed.ssp13 = refl
... | Signed.ssp17 = refl
... | Signed.ssp19 = refl
... | Signed.ssp23 = refl
... | Signed.ssp29 = refl
... | Signed.ssp31 = refl
... | Signed.ssp41 = refl
... | Signed.ssp47 = refl
... | Signed.ssp59 = refl
... | Signed.ssp71 = refl
neutralValuationIsZeroAt Lane.p59 observed with observed
... | Signed.ssp2 = refl
... | Signed.ssp3 = refl
... | Signed.ssp5 = refl
... | Signed.ssp7 = refl
... | Signed.ssp11 = refl
... | Signed.ssp13 = refl
... | Signed.ssp17 = refl
... | Signed.ssp19 = refl
... | Signed.ssp23 = refl
... | Signed.ssp29 = refl
... | Signed.ssp31 = refl
... | Signed.ssp41 = refl
... | Signed.ssp47 = refl
... | Signed.ssp59 = refl
... | Signed.ssp71 = refl
neutralValuationIsZeroAt Lane.p71 observed with observed
... | Signed.ssp2 = refl
... | Signed.ssp3 = refl
... | Signed.ssp5 = refl
... | Signed.ssp7 = refl
... | Signed.ssp11 = refl
... | Signed.ssp13 = refl
... | Signed.ssp17 = refl
... | Signed.ssp19 = refl
... | Signed.ssp23 = refl
... | Signed.ssp29 = refl
... | Signed.ssp31 = refl
... | Signed.ssp41 = refl
... | Signed.ssp47 = refl
... | Signed.ssp59 = refl
... | Signed.ssp71 = refl

data ZeroValuationRecoversSelectedNeutralLane : Set where

zeroValuationCannotRecoverSelectedNeutralLane :
  ZeroValuationRecoversSelectedNeutralLane → ⊥
zeroValuationCannotRecoverSelectedNeutralLane ()

------------------------------------------------------------------------
-- 6. FRACTRAN execution handoff.
--
-- The existing weave owns the actual instruction language and execution
-- engine.  We package a pointed lane together with the compiled valuation and
-- a concrete instruction programme.  This is a typed execution handoff, not a
-- claim that the chosen 15<->15 indexing is canonically forced by arithmetic.
------------------------------------------------------------------------

record PointedSignedFRACTRANSeed : Set where
  constructor pointed-signed-fractran-seed
  field
    pointedLane : PointedSignedSSPLane
    valuation : Signed.SSPValuation
    valuationMatchesPointedLane :
      (prime : Signed.SSPPrime) →
      valuation prime ≡ pointedSignedValuation pointedLane prime
    program : List Signed.WeaveInstruction

open PointedSignedFRACTRANSeed public

seedFromInternalLane :
  Internal.SSP15InternalLane →
  List Signed.WeaveInstruction →
  PointedSignedFRACTRANSeed
seedFromInternalLane lane program =
  pointed-signed-fractran-seed
    (internalLaneToPointedSigned lane)
    (pointedSignedValuation (internalLaneToPointedSigned lane))
    (λ prime → refl)
    program

executeSeedProgram :
  PointedSignedFRACTRANSeed →
  Signed.WeaveEffect
executeSeedProgram seed =
  Signed.executeProgram (program seed) Signed.emptyWeaveEffect

------------------------------------------------------------------------
-- 7. Consolidated branch boundary.
------------------------------------------------------------------------

data ChosenCarrierBijectionIsCanonicalSemanticIdentity : Set where

chosenCarrierBijectionDoesNotCreateSemanticIdentity :
  ChosenCarrierBijectionIsCanonicalSemanticIdentity → ⊥
chosenCarrierBijectionDoesNotCreateSemanticIdentity ()

record SSP15SignedFRACTRANBranchBoundary : Set where
  constructor ssp15-signed-fractran-branch-boundary
  field
    nineToFiveOrbitQuotientAlreadyPaid : Bool
    fiveTimesThreeInternalCarrierAlreadyPaid : Bool
    chosenFifteenToFifteenCarrierBijectionPaid : Bool
    chosenBijectionIsCanonicalSemanticIdentity : Bool

    balancedPhaseToUnitSignedMultiplicityPaid : Bool
    pointedNeutralLaneRetained : Bool
    fullValuationCompilationPaid : Bool
    valuationAloneRecoversNeutralLane : Bool

    existingFRACTRANInstructionLanguageReused : Bool
    seedToExecutionEffectPaid : Bool
    leftResidualFourteenBranchStillIndependent : Bool

open SSP15SignedFRACTRANBranchBoundary public

canonicalSSP15SignedFRACTRANBranchBoundary :
  SSP15SignedFRACTRANBranchBoundary
canonicalSSP15SignedFRACTRANBranchBoundary =
  ssp15-signed-fractran-branch-boundary
    true true true false
    true true true false
    true true true
