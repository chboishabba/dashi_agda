module DASHI.Mathematics.Algebra.RationalAlbertS3AutomorphismRegression where

import DASHI.Mathematics.Algebra.RationalAlbertS3AutomorphismExact as S

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

s3SubgroupPaid :
  S.s3MatrixIndexAutomorphismSubgroupConstructed S.canonicalBoundary ≡ true
s3SubgroupPaid = refl

fullF4NotPromoted :
  S.fullF4AutomorphismGroupConstructed S.canonicalBoundary ≡ false
fullF4NotPromoted = refl

fullE6NotPromoted :
  S.fullE6NormStabilizerConstructed S.canonicalBoundary ≡ false
fullE6NotPromoted = refl
