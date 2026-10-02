module DASHI.Physics.CondensedMatter.MajoranaParityQubitExact where

------------------------------------------------------------------------
-- Exact four-Majorana parity-qubit combinatorics.
--
-- A pair of Majoranas defines a fermionic occupation bit.  Four Majoranas
-- give two pair occupations (n12,n34).  Restricting to even total parity
-- leaves exactly two basis states:
--
--   |0_L> = |00>
--   |1_L> = |11>
--
-- This is a finite logical encoding theorem.  It does not assert that YbSb2
-- experimentally supplies four isolated Majorana zero modes or readout.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

data Bit : Set where
  zero one : Bit

xor : Bit → Bit → Bit
xor zero b = b
xor one zero = one
xor one one = zero

record PairOccupation : Set where
  constructor occ
  field
    n12 n34 : Bit

open PairOccupation public

totalParity : PairOccupation → Bit
totalParity p = xor (n12 p) (n34 p)

record EvenParityState : Set where
  constructor even-state
  field
    occupation : PairOccupation
    evenWitness : totalParity occupation ≡ zero

open EvenParityState public

data LogicalQubit : Set where
  logicalZero logicalOne : LogicalQubit

encodeLogical : LogicalQubit → EvenParityState
encodeLogical logicalZero =
  even-state (occ zero zero) refl
encodeLogical logicalOne =
  even-state (occ one one) refl

decodeLogical : EvenParityState → LogicalQubit
decodeLogical (even-state (occ zero zero) refl) = logicalZero
decodeLogical (even-state (occ zero one) ())
decodeLogical (even-state (occ one zero) ())
decodeLogical (even-state (occ one one) refl) = logicalOne

decodeEncode :
  (q : LogicalQubit) →
  decodeLogical (encodeLogical q) ≡ q
decodeEncode logicalZero = refl
decodeEncode logicalOne = refl

encodeDecodeOccupation :
  (s : EvenParityState) →
  occupation (encodeLogical (decodeLogical s))
  ≡ occupation s
encodeDecodeOccupation (even-state (occ zero zero) refl) = refl
encodeDecodeOccupation (even-state (occ zero one) ())
encodeDecodeOccupation (even-state (occ one zero) ())
encodeDecodeOccupation (even-state (occ one one) refl) = refl

logicalZeroOccupation :
  occupation (encodeLogical logicalZero)
  ≡ occ zero zero
logicalZeroOccupation = refl

logicalOneOccupation :
  occupation (encodeLogical logicalOne)
  ≡ occ one one
logicalOneOccupation = refl

logicalBasisDistinct :
  logicalZero ≡ logicalOne →
  ⊥
logicalBasisDistinct ()
