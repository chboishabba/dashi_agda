module DASHI.Computation.SSSPThreeFrontierBinaryTernaryFactorExact where

-- Exact finite factorisation of the six linear extensions of three frontier
-- vertices into:
--
--   ternary consumer coordinate = which vertex is minimum
--   binary residual coordinate  = orientation of the remaining two vertices.
--
-- Thus the finite carrier has a literal 3 x 2 product chart.  This is not an
-- identification with the cyclic Base369 C6 carrier; only the 2*3 resolution
-- shape is shared.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false)
open import DASHI.Algebra.Trit using (Trit; neg; zer; pos)

import DASHI.Computation.SSSPThreeFrontierLinearExtensionQuotientBidiExact as F3
import DASHI.Computation.SSSPThreeFrontierMinimumOrbitQuotientExact as Min
import DASHI.Foundations.Base369BinaryTernaryRefinement as R23

------------------------------------------------------------------------
-- 1. Binary tail orientation.
------------------------------------------------------------------------

data TailBit : Set where
  forwardTail reverseTail : TailBit

record MinTailCode : Set where
  constructor minTailCode
  field
    minimumClass : Trit
    tailOrientation : TailBit

open MinTailCode public

------------------------------------------------------------------------
-- 2. Six linear extensions <-> ternary x binary product.
------------------------------------------------------------------------

encodeOrder : F3.LinearOrder3 → MinTailCode
encodeOrder F3.abc = minTailCode neg forwardTail
encodeOrder F3.acb = minTailCode neg reverseTail
encodeOrder F3.bac = minTailCode zer forwardTail
encodeOrder F3.bca = minTailCode zer reverseTail
encodeOrder F3.cab = minTailCode pos forwardTail
encodeOrder F3.cba = minTailCode pos reverseTail

decodeOrder : MinTailCode → F3.LinearOrder3
decodeOrder (minTailCode neg forwardTail) = F3.abc
decodeOrder (minTailCode neg reverseTail) = F3.acb
decodeOrder (minTailCode zer forwardTail) = F3.bac
decodeOrder (minTailCode zer reverseTail) = F3.bca
decodeOrder (minTailCode pos forwardTail) = F3.cab
decodeOrder (minTailCode pos reverseTail) = F3.cba

orderRoundTrip :
  (o : F3.LinearOrder3) → decodeOrder (encodeOrder o) ≡ o
orderRoundTrip F3.abc = refl
orderRoundTrip F3.acb = refl
orderRoundTrip F3.bac = refl
orderRoundTrip F3.bca = refl
orderRoundTrip F3.cab = refl
orderRoundTrip F3.cba = refl

codeRoundTrip :
  (c : MinTailCode) → encodeOrder (decodeOrder c) ≡ c
codeRoundTrip (minTailCode neg forwardTail) = refl
codeRoundTrip (minTailCode neg reverseTail) = refl
codeRoundTrip (minTailCode zer forwardTail) = refl
codeRoundTrip (minTailCode zer reverseTail) = refl
codeRoundTrip (minTailCode pos forwardTail) = refl
codeRoundTrip (minTailCode pos reverseTail) = refl

------------------------------------------------------------------------
-- 3. The ternary factor is exactly the Pull(M=1) minimum observation.
------------------------------------------------------------------------

minimumFactorAgreesWithPull :
  (o : F3.LinearOrder3) →
  minimumClass (encodeOrder o) ≡ Min.pullOneObservation o
minimumFactorAgreesWithPull F3.abc = refl
minimumFactorAgreesWithPull F3.acb = refl
minimumFactorAgreesWithPull F3.bac = refl
minimumFactorAgreesWithPull F3.bca = refl
minimumFactorAgreesWithPull F3.cab = refl
minimumFactorAgreesWithPull F3.cba = refl

------------------------------------------------------------------------
-- 4. Forgetting the binary residual performs the sorting-barrier quotient.
------------------------------------------------------------------------

forgetTail : MinTailCode → Trit
forgetTail = minimumClass

sameMinimumDifferentTailA :
  forgetTail (encodeOrder F3.abc) ≡ forgetTail (encodeOrder F3.acb)
sameMinimumDifferentTailA = refl

sameMinimumDifferentTailB :
  forgetTail (encodeOrder F3.bac) ≡ forgetTail (encodeOrder F3.bca)
sameMinimumDifferentTailB = refl

sameMinimumDifferentTailC :
  forgetTail (encodeOrder F3.cab) ≡ forgetTail (encodeOrder F3.cba)
sameMinimumDifferentTailC = refl

------------------------------------------------------------------------
-- 5. Exact connection to the repository's 2^a 3^b resolution *shape*.
------------------------------------------------------------------------

sixResolutionCount : R23.sectorCount R23.phase6Resolution ≡ 6
sixResolutionCount = R23.phase6-sector-count

threeResolutionCount : R23.sectorCount R23.phase3Resolution ≡ 3
threeResolutionCount = R23.phase3-sector-count

binaryRefinementShape :
  R23.binaryRefine R23.phase3Resolution ≡ R23.phase6Resolution
binaryRefinementShape = R23.phase3-binary-refines-to-phase6

------------------------------------------------------------------------
-- 6. Carrier-role firewall.
------------------------------------------------------------------------

record BinaryTernaryFactorBoundary : Set where
  constructor binaryTernaryFactorBoundary
  field
    sixOrdersHaveExactThreeTimesTwoChart :
      (o : F3.LinearOrder3) → decodeOrder (encodeOrder o) ≡ o
    ternaryFactorIsPullMinimum :
      (o : F3.LinearOrder3) →
      minimumClass (encodeOrder o) ≡ Min.pullOneObservation o
    cyclicC6IdentificationClaimed : Bool
    cyclicC6IdentificationClaimedIsFalse :
      cyclicC6IdentificationClaimed ≡ false

canonicalBinaryTernaryFactorBoundary : BinaryTernaryFactorBoundary
canonicalBinaryTernaryFactorBoundary =
  binaryTernaryFactorBoundary
    orderRoundTrip
    minimumFactorAgreesWithPull
    false refl
