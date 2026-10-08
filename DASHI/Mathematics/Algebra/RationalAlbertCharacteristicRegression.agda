module DASHI.Mathematics.Algebra.RationalAlbertCharacteristicRegression where

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Mathematics.Algebra.RationalAlbertJordanExact as A
import DASHI.Mathematics.Algebra.RationalAlbertCharacteristicExact as C

characteristicRegression : (x : A.RationalAlbert) →
  C.characteristicResidual x ≡ C.zeroAlbert
characteristicRegression = C.characteristicIdentity
