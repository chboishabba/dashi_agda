{-# OPTIONS --safe #-}
module DASHI.Codec.VerifiedFiniteTritCoder where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)

open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

------------------------------------------------------------------------
-- A concrete finite-precision machine code for one balanced trit.
--
--   neg -> 00
--   zer -> 01
--   pos -> 10
--   11  -> invalid/reserved
--
-- Every codeword has exactly two bits.  This proves finite machine-level
-- roundtrip correctness and malformed-word rejection.  It is deliberately not
-- an entropy-optimality or rANS theorem.

data Bit : Set where
  bit0 bit1 : Bit

data Word2 : Set where
  word00 word01 word10 word11 : Word2

wordWidth : Nat
wordWidth = suc (suc zero)

encodeTrit : Trit → Word2
encodeTrit neg = word00
encodeTrit zer = word01
encodeTrit pos = word10

decodeWord : Word2 → Maybe Trit
decodeWord word00 = just neg
decodeWord word01 = just zer
decodeWord word10 = just pos
decodeWord word11 = nothing

decode-encode : ∀ t → decodeWord (encodeTrit t) ≡ just t
decode-encode neg = refl
decode-encode zer = refl
decode-encode pos = refl

reserved-word-rejected : decodeWord word11 ≡ nothing
reserved-word-rejected = refl

encode-injective : ∀ {x y} → encodeTrit x ≡ encodeTrit y → x ≡ y
encode-injective {neg} {neg} refl = refl
encode-injective {neg} {zer} ()
encode-injective {neg} {pos} ()
encode-injective {zer} {neg} ()
encode-injective {zer} {zer} refl = refl
encode-injective {zer} {pos} ()
encode-injective {pos} {neg} ()
encode-injective {pos} {zer} ()
encode-injective {pos} {pos} refl = refl

------------------------------------------------------------------------
-- Fixed-width triple packing.  Three trits occupy exactly six bits and decode
-- componentwise.  This is the finite baseline used by the executable flagship
-- benchmark; the mask/sign entropy lane may beat it only through measured
-- statistical modelling.

TritTriple : Set
TritTriple = Trit × (Trit × Trit)

WordTriple : Set
WordTriple = Word2 × (Word2 × Word2)

tripleWidth : Nat
tripleWidth = suc (suc (suc (suc (suc (suc zero)))))

encodeTriple : TritTriple → WordTriple
encodeTriple (a , (b , c)) = encodeTrit a , (encodeTrit b , encodeTrit c)

decodeTriple : WordTriple → Maybe TritTriple
decodeTriple (word00 , (word00 , word00)) = just (neg , (neg , neg))
decodeTriple (word00 , (word00 , word01)) = just (neg , (neg , zer))
decodeTriple (word00 , (word00 , word10)) = just (neg , (neg , pos))
decodeTriple (word00 , (word01 , word00)) = just (neg , (zer , neg))
decodeTriple (word00 , (word01 , word01)) = just (neg , (zer , zer))
decodeTriple (word00 , (word01 , word10)) = just (neg , (zer , pos))
decodeTriple (word00 , (word10 , word00)) = just (neg , (pos , neg))
decodeTriple (word00 , (word10 , word01)) = just (neg , (pos , zer))
decodeTriple (word00 , (word10 , word10)) = just (neg , (pos , pos))
decodeTriple (word01 , (word00 , word00)) = just (zer , (neg , neg))
decodeTriple (word01 , (word00 , word01)) = just (zer , (neg , zer))
decodeTriple (word01 , (word00 , word10)) = just (zer , (neg , pos))
decodeTriple (word01 , (word01 , word00)) = just (zer , (zer , neg))
decodeTriple (word01 , (word01 , word01)) = just (zer , (zer , zer))
decodeTriple (word01 , (word01 , word10)) = just (zer , (zer , pos))
decodeTriple (word01 , (word10 , word00)) = just (zer , (pos , neg))
decodeTriple (word01 , (word10 , word01)) = just (zer , (pos , zer))
decodeTriple (word01 , (word10 , word10)) = just (zer , (pos , pos))
decodeTriple (word10 , (word00 , word00)) = just (pos , (neg , neg))
decodeTriple (word10 , (word00 , word01)) = just (pos , (neg , zer))
decodeTriple (word10 , (word00 , word10)) = just (pos , (neg , pos))
decodeTriple (word10 , (word01 , word00)) = just (pos , (zer , neg))
decodeTriple (word10 , (word01 , word01)) = just (pos , (zer , zer))
decodeTriple (word10 , (word01 , word10)) = just (pos , (zer , pos))
decodeTriple (word10 , (word10 , word00)) = just (pos , (pos , neg))
decodeTriple (word10 , (word10 , word01)) = just (pos , (pos , zer))
decodeTriple (word10 , (word10 , word10)) = just (pos , (pos , pos))
decodeTriple _ = nothing

triple-roundtrip : ∀ x → decodeTriple (encodeTriple x) ≡ just x
triple-roundtrip (neg , (neg , neg)) = refl
triple-roundtrip (neg , (neg , zer)) = refl
triple-roundtrip (neg , (neg , pos)) = refl
triple-roundtrip (neg , (zer , neg)) = refl
triple-roundtrip (neg , (zer , zer)) = refl
triple-roundtrip (neg , (zer , pos)) = refl
triple-roundtrip (neg , (pos , neg)) = refl
triple-roundtrip (neg , (pos , zer)) = refl
triple-roundtrip (neg , (pos , pos)) = refl
triple-roundtrip (zer , (neg , neg)) = refl
triple-roundtrip (zer , (neg , zer)) = refl
triple-roundtrip (zer , (neg , pos)) = refl
triple-roundtrip (zer , (zer , neg)) = refl
triple-roundtrip (zer , (zer , zer)) = refl
triple-roundtrip (zer , (zer , pos)) = refl
triple-roundtrip (zer , (pos , neg)) = refl
triple-roundtrip (zer , (pos , zer)) = refl
triple-roundtrip (zer , (pos , pos)) = refl
triple-roundtrip (pos , (neg , neg)) = refl
triple-roundtrip (pos , (neg , zer)) = refl
triple-roundtrip (pos , (neg , pos)) = refl
triple-roundtrip (pos , (zer , neg)) = refl
triple-roundtrip (pos , (zer , zer)) = refl
triple-roundtrip (pos , (zer , pos)) = refl
triple-roundtrip (pos , (pos , neg)) = refl
triple-roundtrip (pos , (pos , zer)) = refl
triple-roundtrip (pos , (pos , pos)) = refl

record VerifiedFiniteTritCoder : Set where
  field
    precisionBits : Nat
    encode : Trit → Word2
    decode : Word2 → Maybe Trit
    roundtrip : ∀ t → decode (encode t) ≡ just t
    malformedRejected : decode word11 ≡ nothing
    injective : ∀ {x y} → encode x ≡ encode y → x ≡ y
open VerifiedFiniteTritCoder public

verifiedFiniteTritCoder : VerifiedFiniteTritCoder
verifiedFiniteTritCoder =
  record
    { precisionBits = wordWidth
    ; encode = encodeTrit
    ; decode = decodeWord
    ; roundtrip = decode-encode
    ; malformedRejected = reserved-word-rejected
    ; injective = encode-injective
    }
