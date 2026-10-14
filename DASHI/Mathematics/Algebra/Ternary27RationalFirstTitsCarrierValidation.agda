module DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsCarrierValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Mathematics.Algebra.Ternary27RationalFirstTitsCarrierExact as R

literalRationalCarrierExists : R.literalRationalCarrierDefined R.canonicalBoundary ≡ true
literalRationalCarrierExists = refl

literalFirstTitsProductExists : R.literalFirstTitsProductDefined R.canonicalBoundary ≡ true
literalFirstTitsProductExists = refl

literalFirstTitsCubicExists : R.literalFirstTitsCubicDefined R.canonicalBoundary ≡ true
literalFirstTitsCubicExists = refl

ternaryBasisIndexesRationalCarrier : R.ternaryBasisEmbeddingDefined R.canonicalBoundary ≡ true
ternaryBasisIndexesRationalCarrier = refl

jordanLawStillProofRelevant : R.jordanIdentityKernelProved R.canonicalBoundary ≡ false
jordanLawStillProofRelevant = refl

classicalAlbertRecognitionStillOpen : R.classicalAlbertApplicationKernelProved R.canonicalBoundary ≡ false
classicalAlbertRecognitionStillOpen = refl
