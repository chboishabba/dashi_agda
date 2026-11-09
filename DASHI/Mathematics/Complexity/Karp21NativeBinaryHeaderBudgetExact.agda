{-# OPTIONS --safe #-}
module DASHI.Mathematics.Complexity.Karp21NativeBinaryHeaderBudgetExact where

------------------------------------------------------------------------
-- B3+B4 genuine binary ORIGINAL gamma n/m graph header and budget.
-- The executable reads only native LE bits for n,m and tests the
-- original 3*m <= remaining actual word bit count *before* any edge
-- loop. No unary decoded n or m is allocated on the runtime path.
--
-- Original numeric headers and 3m guard are observed in proofs only.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Maybe.Base using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Mathematics.Complexity.FiniteWordSizeExact as Word
import DASHI.Mathematics.Complexity.Karp21NativeUnsignedEndpointBitReaderExact as Reader
import DASHI.Mathematics.Complexity.Karp21NativeBinaryCountBudgetExact as Budget
import DASHI.Mathematics.Complexity.Karp21BinaryNativeRippleAdderValueExact as Value
import DASHI.Mathematics.Complexity.Karp21GammaZigzagPartitionWordDecodeExact as Original
import Data.Nat.Base as Nat

record NativeBinaryGraphHeader : Set where
  constructor binary-header
  field
    verticesLE : Word.BitWord
    edgesLE : Word.BitWord
    afterHeader : Word.BitWord
open NativeBinaryGraphHeader public

readNativeBinaryGraphHeader :
  Word.BitWord → Maybe NativeBinaryGraphHeader
readNativeBinaryGraphHeader word
  with Reader.readGammaNatLE word
... | nothing = nothing
... | just (n , afterN)
  with Reader.readGammaNatLE afterN
... | nothing = nothing
... | just (m , afterM) =
  just (binary-header n m afterM)

-- Return nothing if original source's 3*m budget is impossible.
-- Crucially this branch happens without iterating m times.
readNativeBinaryBudgetedHeader :
  Word.BitWord → Maybe NativeBinaryGraphHeader
readNativeBinaryBudgetedHeader word
  with readNativeBinaryGraphHeader word
... | nothing = nothing
... | just (binary-header n m afterM)
  with Budget.binaryCountBudget m afterM
... | false = nothing
... | true = just (binary-header n m afterM)

record OriginalNumericGraphHeader : Set where
  constructor numeric-header
  field
    vertices : Nat
    edgeCount : Nat
    afterNumericHeader : Word.BitWord
open OriginalNumericGraphHeader public

observeNativeBinaryGraphHeader :
  Maybe NativeBinaryGraphHeader → Maybe OriginalNumericGraphHeader
observeNativeBinaryGraphHeader nothing = nothing
observeNativeBinaryGraphHeader
  (just (binary-header n m afterM)) =
  just (numeric-header (Value.valueLE n) (Value.valueLE m) afterM)

readOriginalNumericGraphHeader :
  Word.BitWord → Maybe OriginalNumericGraphHeader
readOriginalNumericGraphHeader word
  with Original.readGamma word
... | nothing = nothing
... | just (n , afterN)
  with Original.readGamma afterN
... | nothing = nothing
... | just (m , afterM) =
  just (numeric-header n m afterM)

-- EXACT original two gamma headers, including truncation/suffix.
nativeBinaryGraphHeadersSameOriginal :
  (word : Word.BitWord) →
  observeNativeBinaryGraphHeader
    (readNativeBinaryGraphHeader word)
    ≡ readOriginalNumericGraphHeader word
nativeBinaryGraphHeadersSameOriginal word
  with Reader.readGammaNatLE word
     | Reader.nativeUnsignedEndpointSameOriginal word
... | nothing | eq rewrite sym eq = refl
... | just (n , afterN) | eq rewrite sym eq
  with Reader.readGammaNatLE afterN
     | Reader.nativeUnsignedEndpointSameOriginal afterN
... | nothing | eq2 rewrite sym eq2 = refl
... | just (m , afterM) | eq2 rewrite sym eq2 = refl

-- Source-level original complete header's budgeted result. This
-- original Nat read is NOT on the executable native graph path.
readOriginalBudgetedHeader :
  Word.BitWord → Maybe OriginalNumericGraphHeader
readOriginalBudgetedHeader word
  with readOriginalNumericGraphHeader word
... | nothing = nothing
... | just (numeric-header n m afterM)
  with Nat._≤ᵇ_ (suc (suc (suc zero)) * m)
       (Data.List.Base.length afterM)
... | false = nothing
... | true = just (numeric-header n m afterM)

nativeBinaryBudgetedHeadersSameOriginal :
  (word : Word.BitWord) →
  observeNativeBinaryGraphHeader
    (readNativeBinaryBudgetedHeader word)
    ≡ readOriginalBudgetedHeader word
nativeBinaryBudgetedHeadersSameOriginal word
  with readNativeBinaryGraphHeader word
     | nativeBinaryGraphHeadersSameOriginal word
... | nothing | headEq rewrite sym headEq = refl
... | just (binary-header n m afterM) | headEq
  rewrite sym headEq
        | Budget.binaryCountBudgetSameOriginal m afterM
  with Nat._≤ᵇ_ (suc (suc (suc zero)) * Value.valueLE m)
       (Data.List.Base.length afterM)
... | false = refl
... | true = refl
