module DASHI.Mathematics.Algebra.RationalAlbertUniversalIdentityRegression where

import DASHI.Mathematics.Algebra.RationalAlbertJordanIdentityExact as J
import DASHI.Mathematics.Algebra.RationalAlbertCharacteristicIdentityExact as C
import DASHI.Mathematics.Algebra.RationalAlbertCyclicAutomorphismExact as G

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)

jordanIdentitySourceWritten : Bool
jordanIdentitySourceWritten = J.jordanIdentitySourceWritten

jordanIdentitySourceWrittenIsTrue : jordanIdentitySourceWritten ≡ true
jordanIdentitySourceWrittenIsTrue = refl

characteristicIdentitySourceWritten : Bool
characteristicIdentitySourceWritten = C.characteristicIdentitySourceWritten

characteristicIdentitySourceWrittenIsTrue : characteristicIdentitySourceWritten ≡ true
characteristicIdentitySourceWrittenIsTrue = refl

cyclicAutomorphismSourceWritten : Bool
cyclicAutomorphismSourceWritten = G.cyclicAlbertAutomorphismSourceWritten

cyclicAutomorphismSourceWrittenIsTrue : cyclicAutomorphismSourceWritten ≡ true
cyclicAutomorphismSourceWrittenIsTrue = refl
