module DASHI.Moonshine.Monster3BSchurFromSimpleFDRepLeanReceiptValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Moonshine.Monster3BSchurFromSimpleFDRepLeanReceiptExact as Receipt

rankOnePaidGenerically :
  Receipt.simpleFDRepEndRankOneSourceWritten Receipt.canonicalBoundary ≡ true
rankOnePaidGenerically = refl

scalarSelfIntertwinersPaidGenerically :
  Receipt.irreducibleSelfIntertwinersScalarSourceWritten Receipt.canonicalBoundary ≡ true
scalarSelfIntertwinersPaidGenerically = refl

schurNotMonsterSpecific :
  Receipt.schurRemainsMonsterSpecificInput Receipt.canonicalBoundary ≡ false
schurNotMonsterSpecific = refl
