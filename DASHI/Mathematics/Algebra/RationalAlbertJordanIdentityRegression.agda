module DASHI.Mathematics.Algebra.RationalAlbertJordanIdentityRegression where

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Mathematics.Algebra.RationalAlbertJordanExact as A
import DASHI.Mathematics.Algebra.RationalAlbertJordanIdentityExact as J

universalJordanIdentityRegression :
  (x y : A.RationalAlbert) →
  A.jordanProduct (A.jordanProduct (A.jordanProduct x x) y) x
  ≡
  A.jordanProduct (A.jordanProduct x x) (A.jordanProduct y x)
universalJordanIdentityRegression = J.jordanIdentity
