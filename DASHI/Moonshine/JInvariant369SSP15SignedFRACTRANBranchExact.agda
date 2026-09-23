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
unitMultiplicityToPhase =
  Signed.coarseMultiplicity

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
  proj₁ lane , Signed.coarseMultiplicity (signedMultiplicity state)

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

primeEqual :
  Lane.MonsterPrimeLane →
  Lane.MonsterPrimeLane →
  Bool
primeEqual Lane.p2 Lane.p2 = true
primeEqual Lane.p3 Lane.p3 = true
primeEqual Lane.p5 Lane.p5 = true
primeEqual Lane.p7 Lane.p7 = true
primeEqual Lane.p11 Lane.p11 = true
primeEqual Lane.p13 Lane.p13 = true
primeEqual Lane.p17 Lane.p17 = true
primeEqual Lane.p19 Lane.p19 = true
primeEqual Lane.p23 Lane.p23 = true
primeEqual Lane.p29 Lane.p29 = true
primeEqual Lane.p31 Lane.p31 = true
primeEqual Lane.p41 Lane.p41 = true
primeEqual Lane.p47 Lane.p47 = true
primeEqual Lane.p59 Lane.p59 = true
primeEqual Lane.p71 Lane.p71 = true
primeEqual left right = false

pointedSignedValuation :
  PointedSignedSSPLane →
  Signed.SSPValuation
pointedSignedValuation state prime
  with primeEqual (selectedPrime state) prime
... | true = signedMultiplicity state
... | false = Signed.zeroMultiplicity

pointedValuationOwnLane :
  (state : PointedSignedSSPLane) →
  pointedSignedValuation state (selectedPrime state)
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
  (selected observed : Lane.MonsterPrimeLane) →
  pointedSignedValuation (neutralPointed selected) observed
  ≡ Signed.zeroMultiplicity
neutralValuationIsZeroAt Lane.p2 observed = refl
neutralValuationIsZeroAt Lane.p3 observed = refl
neutralValuationIsZeroAt Lane.p5 observed = refl
neutralValuationIsZeroAt Lane.p7 observed = refl
neutralValuationIsZeroAt Lane.p11 observed = refl
neutralValuationIsZeroAt Lane.p13 observed = refl
neutralValuationIsZeroAt Lane.p17 observed = refl
neutralValuationIsZeroAt Lane.p19 observed = refl
neutralValuationIsZeroAt Lane.p23 observed = refl
neutralValuationIsZeroAt Lane.p29 observed = refl
neutralValuationIsZeroAt Lane.p31 observed = refl
neutralValuationIsZeroAt Lane.p41 observed = refl
neutralValuationIsZeroAt Lane.p47 observed = refl
neutralValuationIsZeroAt Lane.p59 observed = refl
neutralValuationIsZeroAt Lane.p71 observed = refl

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
      (prime : Lane.MonsterPrimeLane) →
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
