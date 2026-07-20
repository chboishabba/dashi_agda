module DASHI.Codec.TriadicMaskSignRegression where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Codec.TriadicMaskSign
open import DASHI.Codec.TriadicGlobalInversionFold
open import DASHI.Codec.RANSMaskSignModel

------------------------------------------------------------------------
-- Compact import/regression surface for the exact finite codec tranche.
------------------------------------------------------------------------

zeroTriple : Trit3
zeroTriple = tri3 zero zero zero

mixedTriple : Trit3
mixedTriple = tri3 neg zero pos

fullTriple : Trit3
fullTriple = tri3 pos neg pos

zero-mask-roundtrip : decode3 (encode3 zeroTriple) ≡ zeroTriple
zero-mask-roundtrip = refl

mixed-mask-roundtrip : decode3 (encode3 mixedTriple) ≡ mixedTriple
mixed-mask-roundtrip = refl

full-mask-roundtrip : decode3 (encode3 fullTriple) ≡ fullTriple
full-mask-roundtrip = refl

mixed-fold-roundtrip : decodeFold14 (encodeFold14 mixedTriple) ≡ mixedTriple
mixed-fold-roundtrip = refl

cold-mask-table-total :
  maskFrequencyTotal (RANSModelContract.maskTable coldStartModel) ≡ TotalFrequency
cold-mask-table-total = RANSModelContract.maskNormalized coldStartModel

cold-sign-table-total :
  signFrequencyTotal (RANSModelContract.signTable coldStartModel) ≡ TotalFrequency
cold-sign-table-total = RANSModelContract.signNormalized coldStartModel
