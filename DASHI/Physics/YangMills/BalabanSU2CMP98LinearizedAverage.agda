module DASHI.Physics.YangMills.BalabanSU2CMP98LinearizedAverage where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)

-- `sourceFormula` is the transcription target and `implementation` is the
-- executable/formal operator.  Source exactness is an equality, not metadata.
record CMP98LinearizedAverage (Input Output Support : Set) : Set₁ where
  field
    sourceFormula : Input → Output
    implementation : Input → Output
    support : Input → List Support
    sourceExact : ∀ input → implementation input ≡ sourceFormula input

open CMP98LinearizedAverage public

linearizedAverageSourceEquality :
  ∀ {Input Output Support}
  (average : CMP98LinearizedAverage Input Output Support) →
  ∀ input → implementation average input ≡ sourceFormula average input
linearizedAverageSourceEquality = sourceExact
