module DASHI.Biology.SSP15ComplementPhaseProjectorExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre,
-- "Linear Representations of Finite Groups",
-- Springer, 1977.
-- DOI: 10.1007/978-1-4684-9458-7.
--
-- Audrey Terras,
-- "Fourier Analysis on Finite Groups and Applications",
-- Cambridge University Press, 1999.
-- DOI: 10.1017/CBO9780511626265.
--
-- DASHI CONTRIBUTION
--
-- Construct the internal 15-state carrier as
--
--   five complement modes x three balanced phases.
--
-- The five complement modes are put in an explicit finite bijection with the
-- five D4 irrep names, while the authority boundary keeps the two semantics
-- distinct.  Characteristic projectors are concrete 0/1 coefficients.  Phase
-- reversal is an involution and transports the projector family equivariantly.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Nat using (_+_; _*_)
open import Data.Product using (_×_; _,_)

import DASHI.Biology.BalancedTernaryHarmonicCarrierExact as Harmonic
import DASHI.Biology.NonaryCompletionPhaseQuotientExact as Quotient
import DASHI.Biology.TernaryMonsterSymmetryCandidateExact as D4

BalancedPhase : Set
BalancedPhase = Harmonic.BalancedTrit

reverseBalancedPhase : BalancedPhase → BalancedPhase
reverseBalancedPhase Harmonic.negativeTrit = Harmonic.positiveTrit
reverseBalancedPhase Harmonic.zeroTrit = Harmonic.zeroTrit
reverseBalancedPhase Harmonic.positiveTrit = Harmonic.negativeTrit

reverseBalancedPhaseInvolutive :
  (phase : BalancedPhase) →
  reverseBalancedPhase (reverseBalancedPhase phase) ≡ phase
reverseBalancedPhaseInvolutive Harmonic.negativeTrit = refl
reverseBalancedPhaseInvolutive Harmonic.zeroTrit = refl
reverseBalancedPhaseInvolutive Harmonic.positiveTrit = refl

SSP15InternalLane : Set
SSP15InternalLane = Quotient.ComplementMode5 × BalancedPhase

canonicalSSP15InternalLanes : List SSP15InternalLane
canonicalSSP15InternalLanes =
  (Quotient.mode09 , Harmonic.negativeTrit)
  ∷ (Quotient.mode09 , Harmonic.zeroTrit)
  ∷ (Quotient.mode09 , Harmonic.positiveTrit)
  ∷ (Quotient.mode18 , Harmonic.negativeTrit)
  ∷ (Quotient.mode18 , Harmonic.zeroTrit)
  ∷ (Quotient.mode18 , Harmonic.positiveTrit)
  ∷ (Quotient.mode27 , Harmonic.negativeTrit)
  ∷ (Quotient.mode27 , Harmonic.zeroTrit)
  ∷ (Quotient.mode27 , Harmonic.positiveTrit)
  ∷ (Quotient.mode36 , Harmonic.negativeTrit)
  ∷ (Quotient.mode36 , Harmonic.zeroTrit)
  ∷ (Quotient.mode36 , Harmonic.positiveTrit)
  ∷ (Quotient.mode45 , Harmonic.negativeTrit)
  ∷ (Quotient.mode45 , Harmonic.zeroTrit)
  ∷ (Quotient.mode45 , Harmonic.positiveTrit)
  ∷ []

listCount : ∀ {A : Set} → List A → Nat
listCount [] = 0
listCount (_ ∷ rest) = 1 + listCount rest

ssp15InternalLaneCountIsFifteen :
  listCount canonicalSSP15InternalLanes ≡ 15
ssp15InternalLaneCountIsFifteen = refl

fiveModesTimesThreePhasesIsFifteen : 5 * 3 ≡ 15
fiveModesTimesThreePhasesIsFifteen = refl

tenDigitsTimesFifteenLanesIsOneHundredFifty : 10 * 15 ≡ 150
tenDigitsTimesFifteenLanesIsOneHundredFifty = refl

------------------------------------------------------------------------
-- Finite bijection with D4 irrep names.  This is an indexing equivalence,
-- not an identification of complement mythology with representation theory.
------------------------------------------------------------------------

modeToD4Irrep : Quotient.ComplementMode5 → D4.D4IrrepKind
modeToD4Irrep Quotient.mode09 = D4.A1
modeToD4Irrep Quotient.mode18 = D4.A2
modeToD4Irrep Quotient.mode27 = D4.B1
modeToD4Irrep Quotient.mode36 = D4.B2
modeToD4Irrep Quotient.mode45 = D4.E2

d4IrrepToMode : D4.D4IrrepKind → Quotient.ComplementMode5
d4IrrepToMode D4.A1 = Quotient.mode09
d4IrrepToMode D4.A2 = Quotient.mode18
d4IrrepToMode D4.B1 = Quotient.mode27
d4IrrepToMode D4.B2 = Quotient.mode36
d4IrrepToMode D4.E2 = Quotient.mode45

irrepAfterMode :
  (kind : D4.D4IrrepKind) →
  modeToD4Irrep (d4IrrepToMode kind) ≡ kind
irrepAfterMode D4.A1 = refl
irrepAfterMode D4.A2 = refl
irrepAfterMode D4.B1 = refl
irrepAfterMode D4.B2 = refl
irrepAfterMode D4.E2 = refl

modeAfterIrrep :
  (mode : Quotient.ComplementMode5) →
  d4IrrepToMode (modeToD4Irrep mode) ≡ mode
modeAfterIrrep Quotient.mode09 = refl
modeAfterIrrep Quotient.mode18 = refl
modeAfterIrrep Quotient.mode27 = refl
modeAfterIrrep Quotient.mode36 = refl
modeAfterIrrep Quotient.mode45 = refl

modeEqual : Quotient.ComplementMode5 → Quotient.ComplementMode5 → Bool
modeEqual Quotient.mode09 Quotient.mode09 = Agda.Builtin.Bool.true
modeEqual Quotient.mode18 Quotient.mode18 = Agda.Builtin.Bool.true
modeEqual Quotient.mode27 Quotient.mode27 = Agda.Builtin.Bool.true
modeEqual Quotient.mode36 Quotient.mode36 = Agda.Builtin.Bool.true
modeEqual Quotient.mode45 Quotient.mode45 = Agda.Builtin.Bool.true
modeEqual left right = false

phaseEqual : BalancedPhase → BalancedPhase → Bool
phaseEqual Harmonic.negativeTrit Harmonic.negativeTrit = Agda.Builtin.Bool.true
phaseEqual Harmonic.zeroTrit Harmonic.zeroTrit = Agda.Builtin.Bool.true
phaseEqual Harmonic.positiveTrit Harmonic.positiveTrit = Agda.Builtin.Bool.true
phaseEqual left right = false

laneEqual : SSP15InternalLane → SSP15InternalLane → Bool
laneEqual (leftMode , leftPhase) (rightMode , rightPhase)
  with modeEqual leftMode rightMode | phaseEqual leftPhase rightPhase
... | Agda.Builtin.Bool.true | Agda.Builtin.Bool.true = Agda.Builtin.Bool.true
... | Agda.Builtin.Bool.true | false = false
... | false | Agda.Builtin.Bool.true = false
... | false | false = false

modeEqualOwn :
  (mode : Quotient.ComplementMode5) →
  modeEqual mode mode ≡ Agda.Builtin.Bool.true
modeEqualOwn Quotient.mode09 = refl
modeEqualOwn Quotient.mode18 = refl
modeEqualOwn Quotient.mode27 = refl
modeEqualOwn Quotient.mode36 = refl
modeEqualOwn Quotient.mode45 = refl

phaseEqualOwn :
  (phase : BalancedPhase) → phaseEqual phase phase ≡ Agda.Builtin.Bool.true
phaseEqualOwn Harmonic.negativeTrit = refl
phaseEqualOwn Harmonic.zeroTrit = refl
phaseEqualOwn Harmonic.positiveTrit = refl

laneEqualOwn :
  (lane : SSP15InternalLane) → laneEqual lane lane ≡ Agda.Builtin.Bool.true
laneEqualOwn (mode , phase)
  rewrite modeEqualOwn mode | phaseEqualOwn phase = refl

laneProjectorCoefficient :
  SSP15InternalLane → SSP15InternalLane → Nat
laneProjectorCoefficient selected actual with laneEqual selected actual
... | Agda.Builtin.Bool.true = 1
... | false = 0

laneProjectorOwnCoefficient :
  (lane : SSP15InternalLane) →
  laneProjectorCoefficient lane lane ≡ 1
laneProjectorOwnCoefficient lane rewrite laneEqualOwn lane = refl

explicitlyDifferentLaneAnnihilates :
  (selected actual : SSP15InternalLane) →
  laneEqual selected actual ≡ false →
  laneProjectorCoefficient selected actual ≡ 0
explicitlyDifferentLaneAnnihilates
  (selectedMode , selectedPhase)
  (actualMode , actualPhase)
  different
  rewrite different = refl

laneProjectorCoefficientIdempotent :
  (selected actual : SSP15InternalLane) →
  laneProjectorCoefficient selected actual
    * laneProjectorCoefficient selected actual
  ≡ laneProjectorCoefficient selected actual
laneProjectorCoefficientIdempotent selected actual
  with laneEqual selected actual
... | Agda.Builtin.Bool.true = refl
... | false = refl

reverseLane : SSP15InternalLane → SSP15InternalLane
reverseLane (mode , phase) = mode , reverseBalancedPhase phase

reverseLaneInvolutive :
  (lane : SSP15InternalLane) → reverseLane (reverseLane lane) ≡ lane
reverseLaneInvolutive (mode , phase)
  rewrite reverseBalancedPhaseInvolutive phase = refl

phaseEqualReverseCovariant :
  (left right : BalancedPhase) →
  phaseEqual (reverseBalancedPhase left) (reverseBalancedPhase right)
  ≡ phaseEqual left right
phaseEqualReverseCovariant Harmonic.negativeTrit Harmonic.negativeTrit = refl
phaseEqualReverseCovariant Harmonic.negativeTrit Harmonic.zeroTrit = refl
phaseEqualReverseCovariant Harmonic.negativeTrit Harmonic.positiveTrit = refl
phaseEqualReverseCovariant Harmonic.zeroTrit Harmonic.negativeTrit = refl
phaseEqualReverseCovariant Harmonic.zeroTrit Harmonic.zeroTrit = refl
phaseEqualReverseCovariant Harmonic.zeroTrit Harmonic.positiveTrit = refl
phaseEqualReverseCovariant Harmonic.positiveTrit Harmonic.negativeTrit = refl
phaseEqualReverseCovariant Harmonic.positiveTrit Harmonic.zeroTrit = refl
phaseEqualReverseCovariant Harmonic.positiveTrit Harmonic.positiveTrit = refl

laneEqualReverseCovariant :
  (left right : SSP15InternalLane) →
  laneEqual (reverseLane left) (reverseLane right) ≡ laneEqual left right
laneEqualReverseCovariant (leftMode , leftPhase) (rightMode , rightPhase)
  rewrite phaseEqualReverseCovariant leftPhase rightPhase = refl

laneProjectorReverseCovariant :
  (selected actual : SSP15InternalLane) →
  laneProjectorCoefficient (reverseLane selected) (reverseLane actual)
  ≡ laneProjectorCoefficient selected actual
laneProjectorReverseCovariant selected actual
  rewrite laneEqualReverseCovariant selected actual = refl

data ComplementPhasePolicy : Set where
  preserveBalancedPhase reverseBalancedPhasePolicy : ComplementPhasePolicy

record StageSymmetryPhaseState : Set where
  constructor stage-symmetry-phase-state
  field
    stage : Quotient.DecimalCompletionState
    lane : SSP15InternalLane

open StageSymmetryPhaseState public

complementStructuredState :
  ComplementPhasePolicy → StageSymmetryPhaseState → StageSymmetryPhaseState
complementStructuredState preserveBalancedPhase
  (stage-symmetry-phase-state digit (mode , phase)) =
  stage-symmetry-phase-state (Quotient.complementState digit) (mode , phase)
complementStructuredState reverseBalancedPhasePolicy
  (stage-symmetry-phase-state digit (mode , phase)) =
  stage-symmetry-phase-state
    (Quotient.complementState digit)
    (mode , reverseBalancedPhase phase)

complementStructuredStateInvolutive :
  (policy : ComplementPhasePolicy) →
  (state : StageSymmetryPhaseState) →
  complementStructuredState policy (complementStructuredState policy state)
  ≡ state
complementStructuredStateInvolutive preserveBalancedPhase
  (stage-symmetry-phase-state digit (mode , phase))
  rewrite Quotient.complementStateInvolutive digit = refl
complementStructuredStateInvolutive reverseBalancedPhasePolicy
  (stage-symmetry-phase-state digit (mode , phase))
  rewrite Quotient.complementStateInvolutive digit
        | reverseBalancedPhaseInvolutive phase = refl

------------------------------------------------------------------------
-- Authority is backed by the exact laws above, not by self-attesting Booleans.
------------------------------------------------------------------------

record SSP15ComplementPhaseBoundary : Set where
  constructor ssp15-complement-phase-boundary
  field
    internalLaneCountWitness :
      listCount canonicalSSP15InternalLanes ≡ 15
    ownLaneProjectorWitness :
      (lane : SSP15InternalLane) →
      laneProjectorCoefficient lane lane ≡ 1
    phaseReversalCovarianceWitness :
      (selected actual : SSP15InternalLane) →
      laneProjectorCoefficient (reverseLane selected) (reverseLane actual)
      ≡ laneProjectorCoefficient selected actual
    d4NameBijectionProvesSemanticIdentity : Bool
    d4NameBijectionProvesSemanticIdentityIsFalse :
      d4NameBijectionProvesSemanticIdentity ≡ false
    internalLanesCanonicallyAssignedToOggPrimes : Bool
    internalLanesCanonicallyAssignedToOggPrimesIsFalse :
      internalLanesCanonicallyAssignedToOggPrimes ≡ false

canonicalSSP15ComplementPhaseBoundary : SSP15ComplementPhaseBoundary
canonicalSSP15ComplementPhaseBoundary =
  ssp15-complement-phase-boundary
    ssp15InternalLaneCountIsFifteen
    laneProjectorOwnCoefficient
    laneProjectorReverseCovariant
    false refl
    false refl
