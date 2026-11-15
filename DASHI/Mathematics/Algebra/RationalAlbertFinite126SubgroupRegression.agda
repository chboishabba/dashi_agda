module DASHI.Mathematics.Algebra.RationalAlbertFinite126SubgroupRegression where

import DASHI.Mathematics.Algebra.RationalAlbertFinite126SubgroupExact as F

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

c21OctonionSubgroupPaid :
  F.c21OctonionSubgroupConstructed F.canonicalBoundary ≡ true
c21OctonionSubgroupPaid = refl

commutingS3C21Paid :
  F.matrixS3CommutesWithOctonionC21 F.canonicalBoundary ≡ true
commutingS3C21Paid = refl

finite126ExecutionPaid :
  F.generatedAlbertPermutationCount F.canonicalExecutionReceipt ≡ 126
finite126ExecutionPaid = refl

fullF4StillOpen :
  F.fullF4AutomorphismGroupConstructed F.canonicalBoundary ≡ false
fullF4StillOpen = refl
