module DASHI.Codec.TriadicCodecFactorisationCrossPollinationRegression where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Algebra.Trit using (neg; zer; pos; inv)
import DASHI.Algebra.TritSupportSignFactor as Canonical
import DASHI.Codec.TriadicMaskSignFactorization as MaskSign
import DASHI.Codec.TriadicPAdicCodec as PAdic
open import DASHI.Codec.TriadicCodecFactorisationCrossPollination

pAdicNegativeUsesCanonicalFactor :
  pAdic→canonical (PAdic.foldTrit neg) ≡ Canonical.encode neg
pAdicNegativeUsesCanonicalFactor = refl

pAdicZeroUsesCanonicalFactor :
  pAdic→canonical (PAdic.foldTrit zer) ≡ Canonical.encode zer
pAdicZeroUsesCanonicalFactor = refl

pAdicPositiveUsesCanonicalFactor :
  pAdic→canonical (PAdic.foldTrit pos) ≡ Canonical.encode pos
pAdicPositiveUsesCanonicalFactor = refl

maskSignSparseTripleCost :
  rawSupportSignBits (MaskSign.triple neg zer pos) ≡ 5
maskSignSparseTripleCost = refl

negativeSupportSurvivesInversion :
  PAdic.support (inv neg) ≡ PAdic.support neg
negativeSupportSurvivesInversion = refl
