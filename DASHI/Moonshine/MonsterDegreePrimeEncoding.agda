module DASHI.Moonshine.MonsterDegreePrimeEncoding where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.MonsterCharacterTableExact as MCT

------------------------------------------------------------------------
-- Prime valuations encode degrees only.  They are expressly not an
-- encoding of arbitrary cyclotomic character values.

postulate
  PrimeValuationVector : Set
  encodeDegree : Nat → PrimeValuationVector
  decodeDegree : PrimeValuationVector → Nat

record DegreePrimeEncoding (table : MCT.ExactMonsterCharacterTable) : Set where
  field
    primeSupportDescription : String
    encodeDecode : ∀ i → decodeDegree (encodeDegree (MCT.ExactMonsterCharacterTable.degree table i))
                    ≡ MCT.ExactMonsterCharacterTable.degree table i
    degreesOnly : String

