{-# OPTIONS --safe #-}
module DASHI.Moonshine.JInvariantBishopCenteredDyadicAddressExact where

-- Donors: DASHI.Core.BinaryBranchOutcomeEnumerationExact and
-- PNotEqualsNPExactResidualSummaryBitLowerBoundExact (master/PR #1548).
-- Karp #1474 motivates preserving the entire bit payload.  This is the
-- actual signed-residue chart, not an orientation-only compression.
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Vec.Base as V using (Vec; []; _∷_)

open import Data.Fin.Base as F using (Fin; toℕ; inject+; raise)
import Data.Nat.Properties as NP
open import Data.Nat.Solver using (module +-*-Solver)
import Data.Integer.Solver as IS
import Data.Integer.Properties as ZP
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; sym; trans)
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

snoc : ∀ {n} → Vec Bool n → Bool → Vec Bool (suc n)
snoc [] b = b ∷ []
snoc (a ∷ as) b = a ∷ snoc as b

reverseBits : ∀ {n} → Vec Bool n → Vec Bool n
reverseBits [] = []
reverseBits (a ∷ as) = snoc (reverseBits as) a

reverseSnoc : ∀ {n} (as : Vec Bool n) b →
  reverseBits (snoc as b) ≡ b ∷ reverseBits as
reverseSnoc [] b = refl
reverseSnoc (a ∷ as) b = cong (λ xs → snoc xs a) (reverseSnoc as b)

reverseInvolutive : ∀ {n} (as : Vec Bool n) → reverseBits (reverseBits as) ≡ as
reverseInvolutive [] = refl
reverseInvolutive (a ∷ as) =
  trans (reverseSnoc (reverseBits as) a) (cong (a ∷_) (reverseInvolutive as))

-- Branch words execute low bit FIRST; the existing finite codec reads
-- high bit first. Reverse once at the coordinate boundary.
residue : ∀ {n} → B.BinaryWord n → Fin (Codec.bitCardinality n)
residue w = Codec.bitsToFin (reverseBits (toBits w))

reopen : ∀ {n} → Fin (Codec.bitCardinality n) → B.BinaryWord n
reopen r = fromBits (reverseBits (Codec.finToBits r))

reopenResidue : ∀ {n} (w : B.BinaryWord n) → reopen (residue w) ≡ w
reopenResidue w =
  trans (cong (λ b → fromBits (reverseBits b))
    (Codec.finToBitsAfterBitsToFin (reverseBits (toBits w))))
    (trans (cong fromBits (reverseInvolutive (toBits w))) (wordRoundtrip w))

residueReopen : ∀ {n} (r : Fin (Codec.bitCardinality n)) → residue (reopen r) ≡ r
residueReopen r =
  trans (cong (λ b → Codec.bitsToFin (reverseBits b))
    (bitsRoundtrip (reverseBits (Codec.finToBits r))))
    (trans (cong Codec.bitsToFin (reverseInvolutive (Codec.finToBits r)))
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
center w = readSigned (reverseBits (toBits w))

uncenter : ∀ {n} → SignedIndex n → B.BinaryWord (suc n)
uncenter s = fromBits (reverseBits (writeSigned s))

uncenterCenter : ∀ {n} (w : B.BinaryWord (suc n)) → uncenter (center w) ≡ w
uncenterCenter w = trans
  (cong (λ bs → fromBits (reverseBits bs)) (signedWriteRead (reverseBits (toBits w))))
  (trans (cong fromBits (reverseInvolutive (toBits w))) (wordRoundtrip w))

centerUncenter : ∀ {n} (s : SignedIndex n) → center (uncenter s) ≡ s
centerUncenter s = trans
  (cong (λ bs → readSigned (reverseBits bs)) (bitsRoundtrip (reverseBits (writeSigned s))))
  (trans (cong readSigned (reverseInvolutive (writeSigned s))) (signedReadWrite s))

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

-- Numeric readout of the donor Fin codec. These proofs recurse on its
-- literal injections, not on an unbounded integer enumeration.
injectRead : ∀ {m} n (i : Fin m) → toℕ (F.inject+ n i) ≡ toℕ i
injectRead n F.zero = refl
injectRead n (F.suc i) = cong suc (injectRead n i)

raiseRead : ∀ {m} n (i : Fin m) → toℕ (F.raise n i) ≡ n + toℕ i
raiseRead zero i = refl
raiseRead (suc n) i = cong suc (raiseRead n i)

bit : Bool → Nat
bit false = 0
bit true = 1

rank : ∀ {n} → Vec Bool n → Nat
rank [] = 0
rank {suc n} (false ∷ bs) = rank bs
rank {suc n} (true ∷ bs) = Codec.bitCardinality n + rank bs

rankRead : ∀ {n} (bs : Vec Bool n) → toℕ (Codec.bitsToFin bs) ≡ rank bs
rankRead [] = refl
rankRead {suc n} (false ∷ bs) =
  trans (injectRead (Codec.bitCardinality n) (Codec.bitsToFin bs)) (rankRead bs)
rankRead {suc n} (true ∷ bs) =
  trans (raiseRead (Codec.bitCardinality n) (Codec.bitsToFin bs))
    (cong (Codec.bitCardinality n +_) (rankRead bs))

rankSnoc : ∀ {n} (bs : Vec Bool n) b → rank (snoc bs b) ≡ 2 * rank bs + bit b
rankSnoc [] false = refl
rankSnoc [] true = refl
rankSnoc (false ∷ bs) b = rankSnoc bs b
rankSnoc {suc n} (true ∷ bs) b =
  trans (cong (Codec.bitCardinality (suc n) +_) (rankSnoc bs b))
    (let open +-*-Solver in solve 3
      (λ d r b → (d :+ d) :+ (con 2 :* r :+ b) := con 2 :* (d :+ r) :+ b)
      refl (Codec.bitCardinality n) (rank bs) (bit b))

signedValue : ∀ {n} → Vec Bool (suc n) → ℤ
signedValue (false ∷ bs) = + rank bs
signedValue {n} (true ∷ bs) = (+ rank bs) Z.- (+ Codec.bitCardinality n)

signedValueRead : ∀ {n} (bs : Vec Bool (suc n)) → integerRead (readSigned bs) ≡ signedValue bs
signedValueRead (false ∷ bs) = cong +_ (rankRead bs)
signedValueRead {n} (true ∷ bs) =
  cong (λ r → (+ r) Z.- (+ Codec.bitCardinality n)) (rankRead bs)

-- The positive integer injection preserves double-plus-bit.
natDoubleRead : ∀ a b → (+ (2 * a + b)) ≡ ((+ a) Z.+ (+ a)) Z.+ (+ b)
natDoubleRead a b = cong +_
  (let open +-*-Solver in solve 2
    (λ a b → con 2 :* a :+ b := a :+ a :+ b) refl a b)

signedSnoc : ∀ {n} (bs : Vec Bool (suc n)) b →
  signedValue (snoc bs b) ≡ (signedValue bs Z.+ signedValue bs) Z.+ (+ bit b)
signedSnoc (false ∷ bs) b =
  trans (cong +_ (rankSnoc bs b)) (natDoubleRead (rank bs) (bit b))
signedSnoc {n} (true ∷ bs) b =
  trans (cong (λ r → (+ r) Z.- (+ Codec.bitCardinality (suc n))) (rankSnoc bs b))
    (trans (cong₂ Z._-_ (natDoubleRead (rank bs) (bit b)) refl)
      (let open IS.+-*-Solver in solve 3
        (λ r d b → (r :+ r :+ b) :- (d :+ d) := (r :- d) :+ (r :- d) :+ b)
        refl (+ rank bs) (+ Codec.bitCardinality n) (+ bit b)))

-- The actual low-first path numerator; the final high bit has negative
-- weight. Its integer value is exactly the signed Fin chart above.
offset : ∀ {n} → B.BinaryWord n → ℤ
offset B.end = + 0
offset (B.bit0 B.end) = + 0
offset (B.bit1 B.end) = -[1+ 0 ]
offset (B.bit0 (B.bit0 w)) = offset (B.bit0 w) Z.+ offset (B.bit0 w) Z.+ (+ 0)
offset (B.bit0 (B.bit1 w)) = offset (B.bit1 w) Z.+ offset (B.bit1 w) Z.+ (+ 0)
offset (B.bit1 (B.bit0 w)) = offset (B.bit0 w) Z.+ offset (B.bit0 w) Z.+ (+ 1)
offset (B.bit1 (B.bit1 w)) = offset (B.bit1 w) Z.+ offset (B.bit1 w) Z.+ (+ 1)

offsetRead : ∀ {n} (w : B.BinaryWord (suc n)) →
  signedValue (reverseBits (toBits w)) ≡ offset w
offsetRead (B.bit0 B.end) = refl
offsetRead (B.bit1 B.end) = refl
offsetRead (B.bit0 (B.bit0 w)) =
  trans (signedSnoc (reverseBits (toBits (B.bit0 w))) false)
    (cong (λ j → j Z.+ j Z.+ (+ 0)) (offsetRead (B.bit0 w)))
offsetRead (B.bit0 (B.bit1 w)) =
  trans (signedSnoc (reverseBits (toBits (B.bit1 w))) false)
    (cong (λ j → j Z.+ j Z.+ (+ 0)) (offsetRead (B.bit1 w)))
offsetRead (B.bit1 (B.bit0 w)) =
  trans (signedSnoc (reverseBits (toBits (B.bit0 w))) true)
    (cong (λ j → j Z.+ j Z.+ (+ 1)) (offsetRead (B.bit0 w)))
offsetRead (B.bit1 (B.bit1 w)) =
  trans (signedSnoc (reverseBits (toBits (B.bit1 w))) true)
    (cong (λ j → j Z.+ j Z.+ (+ 1)) (offsetRead (B.bit1 w)))

integerOffsetRead : ∀ {n} (w : B.BinaryWord (suc n)) → integerRead (center w) ≡ offset w
integerOffsetRead w = trans (signedValueRead (reverseBits (toBits w))) (offsetRead w)
