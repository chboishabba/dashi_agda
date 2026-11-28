{-# OPTIONS --safe #-}
module DASHI.Moonshine.JInvariantBishopCenteredDyadicAddressExact where

-- Donors: DASHI.Core.BinaryBranchOutcomeEnumerationExact and
-- PNotEqualsNPExactResidualSummaryBitLowerBoundExact (master/PR #1548).
-- Karp #1474 motivates preserving the entire bit payload.  This is the
-- actual signed-residue chart, not an orientation-only compression.
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Vec.Base as V using (Vec; []; _∷_; reverse)
import Data.Vec.Properties as VP
open import Data.Fin.Base as F using (Fin; toℕ)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
open import Data.Integer.Base as Z using (ℤ; +_; -[1+_])
import DASHI.Core.BinaryBranchOutcomeEnumerationExact as B
import DASHI.Mathematics.Complexity.PNotEqualsNPExactResidualSummaryBitLowerBoundExact as Codec

toBits : ∀ {n} → B.BinaryWord n → Vec Bool n
toBits B.end = []
toBits (B.bit0 w) = false ∷ toBits w
toBits (B.bit1 w) = true ∷ toBits w

fromBits : ∀ {n} → Vec Bool n → B.BinaryWord n
fromBits [] = B.end
fromBits (false ∷ w) = B.bit0 (fromBits w)
fromBits (true ∷ w) = B.bit1 (fromBits w)

wordRoundtrip : ∀ {n} (w : B.BinaryWord n) → fromBits (toBits w) ≡ w
wordRoundtrip B.end = refl
wordRoundtrip (B.bit0 w) = cong B.bit0 (wordRoundtrip w)
wordRoundtrip (B.bit1 w) = cong B.bit1 (wordRoundtrip w)

bitsRoundtrip : ∀ {n} (w : Vec Bool n) → toBits (fromBits w) ≡ w
bitsRoundtrip [] = refl
bitsRoundtrip (false ∷ w) = cong (false ∷_) (bitsRoundtrip w)
bitsRoundtrip (true ∷ w) = cong (true ∷_) (bitsRoundtrip w)

-- Branch words execute low bit FIRST; the existing finite codec reads
-- high bit first. Reverse once at the coordinate boundary.
residue : ∀ {n} → B.BinaryWord n → Fin (Codec.bitCardinality n)
residue w = Codec.bitsToFin (reverse (toBits w))

reopen : ∀ {n} → Fin (Codec.bitCardinality n) → B.BinaryWord n
reopen r = fromBits (reverse (Codec.finToBits r))

reopenResidue : ∀ {n} (w : B.BinaryWord n) → reopen (residue w) ≡ w
reopenResidue w =
  trans (cong (λ b → fromBits (reverse b))
    (Codec.finToBitsAfterBitsToFin (reverse (toBits w))))
    (trans (cong fromBits (VP.reverse-involutive (toBits w))) (wordRoundtrip w))

residueReopen : ∀ {n} (r : Fin (Codec.bitCardinality n)) → residue (reopen r) ≡ r
residueReopen r =
  trans (cong (λ b → Codec.bitsToFin (reverse b))
    (bitsRoundtrip (reverse (Codec.finToBits r))))
    (trans (cong Codec.bitsToFin (VP.reverse-involutive (Codec.finToBits r)))
      (Codec.bitsToFinAfterFinToBits r))

-- The signed interval at width suc n is [-2^n,2^n).
-- Retain the sign and all n lower bits, not a sign-only quotient.
SignedIndex : Nat → Set
SignedIndex n = Bool × Fin (Codec.bitCardinality n)

readSigned : ∀ {n} → Vec Bool (suc n) → SignedIndex n
readSigned (b ∷ bs) = b , Codec.bitsToFin bs

writeSigned : ∀ {n} → SignedIndex n → Vec Bool (suc n)
writeSigned (b , r) = b ∷ Codec.finToBits r

signedReadWrite : ∀ {n} (s : SignedIndex n) → readSigned (writeSigned s) ≡ s
signedReadWrite (b , r) = cong (b ,_) (Codec.bitsToFinAfterFinToBits r)

signedWriteRead : ∀ {n} (bs : Vec Bool (suc n)) → writeSigned (readSigned bs) ≡ bs
signedWriteRead (b ∷ bs) = cong (b ∷_) (Codec.finToBitsAfterBitsToFin bs)

center : ∀ {n} → B.BinaryWord (suc n) → SignedIndex n
center w = readSigned (reverse (toBits w))

uncenter : ∀ {n} → SignedIndex n → B.BinaryWord (suc n)
uncenter s = fromBits (reverse (writeSigned s))

uncenterCenter : ∀ {n} (w : B.BinaryWord (suc n)) → uncenter (center w) ≡ w
uncenterCenter w = trans
  (cong (λ bs → fromBits (reverse bs)) (signedWriteRead (reverse (toBits w))))
  (trans (cong fromBits (VP.reverse-involutive (toBits w))) (wordRoundtrip w))

centerUncenter : ∀ {n} (s : SignedIndex n) → center (uncenter s) ≡ s
centerUncenter s = trans
  (cong (λ bs → readSigned (reverse bs)) (bitsRoundtrip (reverse (writeSigned s))))
  (trans (cong readSigned (VP.reverse-involutive (writeSigned s))) (signedReadWrite s))

integerRead : ∀ {n} → SignedIndex n → ℤ
integerRead {n} (false , r) = + toℕ r
integerRead {n} (true , r) = (+ toℕ r) Z.- (+ Codec.bitCardinality n)

-- Each signed coordinate is recoverable with no enumeration.
-- In particular the zero word is retained, and no negative-zero sheet
-- occurs: the negative half is offset by a whole half interval.
zeroWord : ∀ n → B.BinaryWord n
zeroWord zero = B.end
zeroWord (suc n) = B.bit0 (zeroWord n)

centerInjective : ∀ {n} {a b : B.BinaryWord (suc n)} → center a ≡ center b → a ≡ b
centerInjective {a = a} {b = b} h =
  trans (sym (uncenterCenter a)) (trans (cong uncenter h) (uncenterCenter b))
