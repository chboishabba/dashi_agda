module DASHI.Mathematics.Complexity.PNotEqualsNPXORCountdownMicrocodeExact where

------------------------------------------------------------------------
-- XOR / BORROW COUNTDOWN MICROCODE FOR THE P != NP COMPILER FRONTIER
--
-- Cross-pollination role:
--
-- The recent IIT/XOR-grid branch isolates XOR/XNOR as the complete
-- bipermutative Boolean class.  That sibling theorem is NOT imported here as
-- proof authority.  The relevant finite facts are reproved locally on the
-- complexity carrier.
--
-- For binary countdown, the updated bit is exactly
--
--     bit' = bit XOR borrowIn
--
-- while the outgoing borrow is
--
--     borrowOut = (NOT bit) AND borrowIn.
--
-- Thus XOR supplies the information-preserving local data update, but XOR
-- output alone cannot recover the carry/borrow coordinate.  This is the exact
-- boundary needed for the clock compiler: parity is a useful microcode donor,
-- not a complete timer and not complexity-theoretic hardness evidence.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

false≢true : false ≢ true
false≢true ()

true≢false : true ≢ false
true≢false ()

------------------------------------------------------------------------
-- 1. Local Boolean microcode.
------------------------------------------------------------------------

notBit : Bool → Bool
notBit false = true
notBit true = false

andBit : Bool → Bool → Bool
andBit false _ = false
andBit true x = x

xorBit : Bool → Bool → Bool
xorBit false false = false
xorBit false true = true
xorBit true false = true
xorBit true true = false

borrowOut : Bool → Bool → Bool
borrowOut bit borrowIn = andBit (notBit bit) borrowIn

countdownBitStep : Bool → Bool → Bool × Bool
countdownBitStep bit borrowIn =
  xorBit bit borrowIn , borrowOut bit borrowIn

------------------------------------------------------------------------
-- 2. XOR is information preserving in either coordinate.
------------------------------------------------------------------------

xorRecoverLeft : (left right : Bool) →
  xorBit (xorBit left right) right ≡ left
xorRecoverLeft false false = refl
xorRecoverLeft false true = refl
xorRecoverLeft true false = refl
xorRecoverLeft true true = refl

xorRecoverRight : (left right : Bool) →
  xorBit left (xorBit left right) ≡ right
xorRecoverRight false false = refl
xorRecoverRight false true = refl
xorRecoverRight true false = refl
xorRecoverRight true true = refl

------------------------------------------------------------------------
-- 3. Exact borrow truth table.
------------------------------------------------------------------------

countdownNoBorrow : (bit : Bool) →
  countdownBitStep bit false ≡ bit , false
countdownNoBorrow false = refl
countdownNoBorrow true = refl

countdownBitFalseBorrow :
  countdownBitStep false true ≡ true , true
countdownBitFalseBorrow = refl

countdownBitTrueBorrow :
  countdownBitStep true true ≡ false , false
countdownBitTrueBorrow = refl

------------------------------------------------------------------------
-- 4. Parity alone cannot determine the carry/borrow state.
--
-- The inputs (false,true) and (true,false) have the same XOR output true but
-- different outgoing borrow.  Any clock construction therefore needs a second
-- carry/borrow coordinate in addition to the parity-updated data bit.
------------------------------------------------------------------------

sameXorOutput :
  xorBit false true ≡ xorBit true false
sameXorOutput = refl

differentBorrowOutput :
  borrowOut false true ≢ borrowOut true false
differentBorrowOutput = true≢false

sameXorOutputDifferentBorrow :
  (xorBit false true ≡ xorBit true false)
  ×
  (borrowOut false true ≢ borrowOut true false)
sameXorOutputDifferentBorrow = sameXorOutput , differentBorrowOutput

------------------------------------------------------------------------
-- 5. Max-cut boundary.
------------------------------------------------------------------------

record XORCountdownMicrocodeBoundary : Set where
  constructor xor-countdown-microcode-boundary
  field
    xorProvidesBitUpdate : Bool
    xorUpdateIsCoordinateRecoverable : Bool
    separateBorrowCoordinateRequired : Bool
    xorGridRecurrenceIsExactTClock : Bool
    iitPhiIsComplexityLowerBound : Bool
    timerStillNeedsFiniteTapeCounterCompilation : Bool

open XORCountdownMicrocodeBoundary public

canonicalXORCountdownBoundary : XORCountdownMicrocodeBoundary
canonicalXORCountdownBoundary =
  xor-countdown-microcode-boundary
    true true true false false true

xorDoesNotCloseTimer :
  xorGridRecurrenceIsExactTClock canonicalXORCountdownBoundary ≡ false
xorDoesNotCloseTimer = refl

iitDoesNotCreateLowerBound :
  iitPhiIsComplexityLowerBound canonicalXORCountdownBoundary ≡ false
iitDoesNotCreateLowerBound = refl

counterCompilationRemains :
  timerStillNeedsFiniteTapeCounterCompilation canonicalXORCountdownBoundary ≡ true
counterCompilationRemains = refl
