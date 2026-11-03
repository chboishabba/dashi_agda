module DASHI.Mathematics.Algebra.RationalAlbertJordanRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (1ℚ)

import DASHI.Mathematics.Algebra.RationalAlbertJordanExact as A

open A.RationalAlbert
open A.AlbertConstructionBoundary

carrierDimension : A.rationalAlbertDimension ≡ 27
carrierDimension = refl

unitFirstDiagonal : diag1 A.albertUnit ≡ 1ℚ
unitFirstDiagonal = refl

productConstructed :
  jordanProductConstructed A.canonicalAlbertConstructionBoundary ≡ true
productConstructed = refl

cubicNormConstructed :
  cubicNormConstructed A.canonicalAlbertConstructionBoundary ≡ true
cubicNormConstructed = refl

jordanIdentityStillOpen :
  jordanIdentityProved A.canonicalAlbertConstructionBoundary ≡ false
jordanIdentityStillOpen = refl

f4StillOpen :
  f4AutomorphismActionConstructed A.canonicalAlbertConstructionBoundary ≡ false
f4StillOpen = refl
