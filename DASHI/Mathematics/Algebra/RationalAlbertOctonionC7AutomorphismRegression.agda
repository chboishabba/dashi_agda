module DASHI.Mathematics.Algebra.RationalAlbertOctonionC7AutomorphismRegression where

import DASHI.Mathematics.Algebra.RationalAlbertOctonionC7AutomorphismExact as C7

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

c7OctonionAutomorphismPaid :
  C7.c7OctonionAutomorphismConstructed C7.canonicalBoundary ≡ true
c7OctonionAutomorphismPaid = refl

c7AlbertAutomorphismPaid :
  C7.c7AlbertAutomorphismConstructed C7.canonicalBoundary ≡ true
c7AlbertAutomorphismPaid = refl

fullG2NotPromoted :
  C7.fullG2AutomorphismGroupConstructed C7.canonicalBoundary ≡ false
fullG2NotPromoted = refl

fullF4NotPromoted :
  C7.fullF4AutomorphismGroupConstructed C7.canonicalBoundary ≡ false
fullF4NotPromoted = refl
