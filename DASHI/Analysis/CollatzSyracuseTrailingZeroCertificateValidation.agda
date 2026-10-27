module DASHI.Analysis.CollatzSyracuseTrailingZeroCertificateValidation where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Analysis.CollatzSyracuseTrailingZeroCertificateExact as Zero

oneTrailingZeroCompilerPaid :
  Zero.TrailingZeroCertificateBoundary.oneTrailingZeroCompilerPaid
    Zero.canonicalTrailingZeroCertificateBoundary
  ≡ 1
oneTrailingZeroCompilerPaid = refl

arbitraryTrailingZerosCompilerPaid :
  Zero.TrailingZeroCertificateBoundary.arbitraryTrailingZerosCompilerPaid
    Zero.canonicalTrailingZeroCertificateBoundary
  ≡ 1
arbitraryTrailingZerosCompilerPaid = refl

noUniversalPromotion :
  Zero.TrailingZeroCertificateBoundary.trailingZeroCompilerCreatesUniversalStopping
    Zero.canonicalTrailingZeroCertificateBoundary
  ≡ 0
noUniversalPromotion = refl
