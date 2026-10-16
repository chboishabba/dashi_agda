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
-- output alone cannot recover the carry/borrow coordinate.  The same local
-- cell is then iterated over a little-endian finite bit list to obtain an
-- executable ripple-borrow countdown semantics.  This pays the arithmetic
-- core of the timer without pretending that the list recursion is already a
-- finite standard-TM rule-table implementation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
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
-- 3. Exact one-bit borrow truth table.
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
-- 5. Finite little-endian ripple-borrow countdown semantics.
--
-- Incoming borrow=false is observational identity.  Incoming borrow=true
-- subtracts one modulo the represented width and exposes the final underflow
-- borrow separately.  This is the compact arithmetic core to be compiled onto
-- the standard tape; it does not hide the borrow inside the XOR coordinate.
------------------------------------------------------------------------

countdownBits : List Bool → Bool → List Bool × Bool
countdownBits [] borrow = [] , borrow
countdownBits (bit ∷ rest) borrow
  with countdownBitStep bit borrow
... | bit' , nextBorrow
  with countdownBits rest nextBorrow
... | rest' , finalBorrow =
  (bit' ∷ rest') , finalBorrow

countdownBitsNoBorrow :
  (bits : List Bool) →
  countdownBits bits false ≡ bits , false
countdownBitsNoBorrow [] = refl
countdownBitsNoBorrow (bit ∷ rest)
  rewrite countdownNoBorrow bit
        | countdownBitsNoBorrow rest =
  refl

countdownOne : List Bool → List Bool × Bool
countdownOne bits = countdownBits bits true

-- 1 = [1] -> 0 = [0].
decrementOne :
  countdownOne (true ∷ []) ≡ (false ∷ []) , false
decrementOne = refl

-- 2 = [0,1] -> 1 = [1,0].
decrementTwo :
  countdownOne (false ∷ true ∷ [])
  ≡ (true ∷ false ∷ []) , false
decrementTwo = refl

-- 4 = [0,0,1] -> 3 = [1,1,0].
decrementFour :
  countdownOne (false ∷ false ∷ true ∷ [])
  ≡ (true ∷ true ∷ false ∷ []) , false
decrementFour = refl

------------------------------------------------------------------------
-- 6. Max-cut boundary.
------------------------------------------------------------------------

record XORCountdownMicrocodeBoundary : Set where
  constructor xor-countdown-microcode-boundary
  field
    xorProvidesBitUpdate : Bool
    xorUpdateIsCoordinateRecoverable : Bool
    separateBorrowCoordinateRequired : Bool
    finiteRippleCountdownSemanticsPaid : Bool
    xorGridRecurrenceIsExactTClock : Bool
    iitPhiIsComplexityLowerBound : Bool
    timerStillNeedsFiniteTapeCounterCompilation : Bool

open XORCountdownMicrocodeBoundary public

canonicalXORCountdownBoundary : XORCountdownMicrocodeBoundary
canonicalXORCountdownBoundary =
  xor-countdown-microcode-boundary
    true true true true false false true

xorDoesNotCloseTimer :
  xorGridRecurrenceIsExactTClock canonicalXORCountdownBoundary ≡ false
xorDoesNotCloseTimer = refl

iitDoesNotCreateLowerBound :
  iitPhiIsComplexityLowerBound canonicalXORCountdownBoundary ≡ false
iitDoesNotCreateLowerBound = refl

rippleCountdownSemanticsPaid :
  finiteRippleCountdownSemanticsPaid canonicalXORCountdownBoundary ≡ true
rippleCountdownSemanticsPaid = refl

counterCompilationRemains :
  timerStillNeedsFiniteTapeCounterCompilation canonicalXORCountdownBoundary ≡ true
counterCompilationRemains = refl
