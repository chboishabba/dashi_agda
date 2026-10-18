module DASHI.Moonshine.Monster369SignedPairNineOrbitExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Biology.SignedSSPFRACTRANWeaveExact as SSP
import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Wikimedia.IbrahimMonsterFiveOrbitD4KernelCharacterExact as Kernel

------------------------------------------------------------------------
-- SIGNED-SSP PAIR -> T^2 -> T^2/± = NineOrbit
--
-- This is a structural quotient bridge, not a Monster same-object claim.
-- Each signed FRACTRAN multiplicity already has a canonical coarse balanced
-- trit.  A pair therefore gives the existing nine-state sheet, and the
-- existing global-inversion quotient gives the canonical five-orbit carrier.
------------------------------------------------------------------------

SignedPair : Set
SignedPair = SSP.SignedMultiplicity × SSP.SignedMultiplicity

coarseSignedPair : SignedPair → Triadic.NineSheet
coarseSignedPair (a , b) = SSP.coarseMultiplicity a , SSP.coarseMultiplicity b

signedPairOrbit : SSP.SignedMultiplicity → SSP.SignedMultiplicity → Triadic.NineOrbit
signedPairOrbit a b = Triadic.quotientNine (coarseSignedPair (a , b))

------------------------------------------------------------------------
-- Simultaneous signed inversion disappears in the global-inversion quotient.
------------------------------------------------------------------------

signedPairOrbitNegationInvariant :
  (a b : SSP.SignedMultiplicity) ->
  signedPairOrbit (SSP.negateMultiplicity a) (SSP.negateMultiplicity b)
  ≡ signedPairOrbit a b
signedPairOrbitNegationInvariant (SSP.negativeMultiplicity a) (SSP.negativeMultiplicity b) = refl
signedPairOrbitNegationInvariant (SSP.negativeMultiplicity a) SSP.zeroMultiplicity = refl
signedPairOrbitNegationInvariant (SSP.negativeMultiplicity a) (SSP.positiveMultiplicity b) = refl
signedPairOrbitNegationInvariant SSP.zeroMultiplicity (SSP.negativeMultiplicity b) = refl
signedPairOrbitNegationInvariant SSP.zeroMultiplicity SSP.zeroMultiplicity = refl
signedPairOrbitNegationInvariant SSP.zeroMultiplicity (SSP.positiveMultiplicity b) = refl
signedPairOrbitNegationInvariant (SSP.positiveMultiplicity a) (SSP.negativeMultiplicity b) = refl
signedPairOrbitNegationInvariant (SSP.positiveMultiplicity a) SSP.zeroMultiplicity = refl
signedPairOrbitNegationInvariant (SSP.positiveMultiplicity a) (SSP.positiveMultiplicity b) = refl

------------------------------------------------------------------------
-- Raw signed-pair lifts of the square generators.
--
-- quarter turn: (a,b) |-> (-b,a)
-- axis reflection: (a,b) |-> (a,-b)
--
-- Their quotient actions are exactly the existing kernel rotate/reflection.
------------------------------------------------------------------------

signedPairQuarterTurn : SignedPair → SignedPair
signedPairQuarterTurn (a , b) = SSP.negateMultiplicity b , a

signedPairAxisReflection : SignedPair → SignedPair
signedPairAxisReflection (a , b) = a , SSP.negateMultiplicity b

signedPairOrbitOfQuarterTurn :
  SSP.SignedMultiplicity -> SSP.SignedMultiplicity -> Triadic.NineOrbit
signedPairOrbitOfQuarterTurn a b =
  signedPairOrbit (SSP.negateMultiplicity b) a

signedPairOrbitOfAxisReflection :
  SSP.SignedMultiplicity -> SSP.SignedMultiplicity -> Triadic.NineOrbit
signedPairOrbitOfAxisReflection a b =
  signedPairOrbit a (SSP.negateMultiplicity b)

rotateOrbit : Triadic.NineOrbit → Triadic.NineOrbit
rotateOrbit = Kernel.rotateOrbit

reflectAxisOrbit : Triadic.NineOrbit → Triadic.NineOrbit
reflectAxisOrbit = Kernel.reflectAxisOrbit

signedPairQuarterTurnDescends :
  (a b : SSP.SignedMultiplicity) ->
  signedPairOrbitOfQuarterTurn a b
  ≡ rotateOrbit (signedPairOrbit a b)
signedPairQuarterTurnDescends (SSP.negativeMultiplicity a) (SSP.negativeMultiplicity b) = refl
signedPairQuarterTurnDescends (SSP.negativeMultiplicity a) SSP.zeroMultiplicity = refl
signedPairQuarterTurnDescends (SSP.negativeMultiplicity a) (SSP.positiveMultiplicity b) = refl
signedPairQuarterTurnDescends SSP.zeroMultiplicity (SSP.negativeMultiplicity b) = refl
signedPairQuarterTurnDescends SSP.zeroMultiplicity SSP.zeroMultiplicity = refl
signedPairQuarterTurnDescends SSP.zeroMultiplicity (SSP.positiveMultiplicity b) = refl
signedPairQuarterTurnDescends (SSP.positiveMultiplicity a) (SSP.negativeMultiplicity b) = refl
signedPairQuarterTurnDescends (SSP.positiveMultiplicity a) SSP.zeroMultiplicity = refl
signedPairQuarterTurnDescends (SSP.positiveMultiplicity a) (SSP.positiveMultiplicity b) = refl

signedPairAxisReflectionDescends :
  (a b : SSP.SignedMultiplicity) ->
  signedPairOrbitOfAxisReflection a b
  ≡ reflectAxisOrbit (signedPairOrbit a b)
signedPairAxisReflectionDescends (SSP.negativeMultiplicity a) (SSP.negativeMultiplicity b) = refl
signedPairAxisReflectionDescends (SSP.negativeMultiplicity a) SSP.zeroMultiplicity = refl
signedPairAxisReflectionDescends (SSP.negativeMultiplicity a) (SSP.positiveMultiplicity b) = refl
signedPairAxisReflectionDescends SSP.zeroMultiplicity (SSP.negativeMultiplicity b) = refl
signedPairAxisReflectionDescends SSP.zeroMultiplicity SSP.zeroMultiplicity = refl
signedPairAxisReflectionDescends SSP.zeroMultiplicity (SSP.positiveMultiplicity b) = refl
signedPairAxisReflectionDescends (SSP.positiveMultiplicity a) (SSP.negativeMultiplicity b) = refl
signedPairAxisReflectionDescends (SSP.positiveMultiplicity a) SSP.zeroMultiplicity = refl
signedPairAxisReflectionDescends (SSP.positiveMultiplicity a) (SSP.positiveMultiplicity b) = refl

------------------------------------------------------------------------
-- Literal five qualitative classes on signed computational state.
------------------------------------------------------------------------

bothNeutral :
  signedPairOrbit SSP.zeroMultiplicity SSP.zeroMultiplicity ≡ Triadic.zeroOrbit
bothNeutral = refl

firstOnlyActive :
  (n : Nat) ->
  signedPairOrbit (SSP.positiveMultiplicity n) SSP.zeroMultiplicity
  ≡ Triadic.firstAxisOrbit
firstOnlyActive n = refl

secondOnlyActive :
  (n : Nat) ->
  signedPairOrbit SSP.zeroMultiplicity (SSP.positiveMultiplicity n)
  ≡ Triadic.secondAxisOrbit
secondOnlyActive n = refl

sameOrientation :
  (m n : Nat) ->
  signedPairOrbit (SSP.positiveMultiplicity m) (SSP.positiveMultiplicity n)
  ≡ Triadic.equalSignOrbit
sameOrientation m n = refl

oppositeOrientation :
  (m n : Nat) ->
  signedPairOrbit (SSP.positiveMultiplicity m) (SSP.negativeMultiplicity n)
  ≡ Triadic.oppositeSignOrbit
oppositeOrientation m n = refl

------------------------------------------------------------------------
-- Firewalls: quotient/action grammar is reusable without semantic promotion.
------------------------------------------------------------------------

data SignedPairQuotientCreatesMonsterAction : Set where
data SignedPairQuotientCreatesAnalyticIdentity : Set where
data FiveOrbitClassifiesMagnitude : Set where

signedPairQuotientDoesNotCreateMonsterAction :
  SignedPairQuotientCreatesMonsterAction -> ⊥
signedPairQuotientDoesNotCreateMonsterAction ()

signedPairQuotientDoesNotCreateAnalyticIdentity :
  SignedPairQuotientCreatesAnalyticIdentity -> ⊥
signedPairQuotientDoesNotCreateAnalyticIdentity ()

fiveOrbitDoesNotClassifyMagnitude : FiveOrbitClassifiesMagnitude -> ⊥
fiveOrbitDoesNotClassifyMagnitude ()

record SignedPairNineOrbitBoundary : Set where
  constructor signed-pair-nine-orbit-boundary
  field
    signedSSPPairConstructed : Bool
    coarseTritPairReused : Bool
    canonicalNineOrbitQuotientReused : Bool
    simultaneousNegationInvariant : Bool
    quarterTurnDescendsToKernelRotation : Bool
    axisReflectionDescendsToKernelReflection : Bool
    magnitudeRetainedByFiveOrbit : Bool
    monsterActionCreated : Bool
    analyticSameObjectCreated : Bool
    nextResidual : String
open SignedPairNineOrbitBoundary public

canonicalSignedPairNineOrbitBoundary : SignedPairNineOrbitBoundary
canonicalSignedPairNineOrbitBoundary =
  signed-pair-nine-orbit-boundary
    true true true true true true
    false false false
    "compose this exact quotient/action bridge with the clean current-master NineOrbit-to-N(3B) screen adapter; separately acquire concrete ordered-real sign/trig shift laws before any trig realization is promoted"
