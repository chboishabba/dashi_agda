module DASHI.Cognition.PNF.OrientedZeroConditionalResidualCardinalityExact where

open import DASHI.Core.Prelude
open import Data.Fin.Base using (Fin; zero; suc)

import DASHI.Cognition.PNF.OrientedZeroFutureQuotientExact as Wave
import DASHI.Core.GeneralResidualFibreCardinalityExact as General

------------------------------------------------------------------------
-- CONDITIONAL RESIDUAL CARDINALITY OVER THE RETAINED SCALAR PROJECTION
------------------------------------------------------------------------

localResidualCount : Wave.Scalar3 → Nat
localResidualCount Wave.negative = 1
localResidualCount Wave.scalarZero = 2
localResidualCount Wave.positive = 1

localResidualBits : Wave.Scalar3 → Nat
localResidualBits Wave.negative = 0
localResidualBits Wave.scalarZero = 1
localResidualBits Wave.positive = 0

localCapacityExact :
  (coarse : Wave.Scalar3) →
  General.pow2 (localResidualBits coarse) ≡ localResidualCount coarse
localCapacityExact Wave.negative = refl
localCapacityExact Wave.scalarZero = refl
localCapacityExact Wave.positive = refl

encodeAdaptive :
  ∀ {coarse} → Wave.AdaptiveResidual coarse → Fin (localResidualCount coarse)
encodeAdaptive {Wave.negative} Wave.nonzeroReceipt = zero
encodeAdaptive {Wave.scalarZero} (Wave.zeroReceipt Wave.approachingZero) = zero
encodeAdaptive {Wave.scalarZero} (Wave.zeroReceipt Wave.leavingZero) = suc zero
encodeAdaptive {Wave.positive} Wave.positiveReceipt = zero

decodeAdaptive :
  (coarse : Wave.Scalar3) →
  Fin (localResidualCount coarse) →
  Wave.AdaptiveResidual coarse
decodeAdaptive Wave.negative zero = Wave.nonzeroReceipt
decodeAdaptive Wave.scalarZero zero = Wave.zeroReceipt Wave.approachingZero
decodeAdaptive Wave.scalarZero (suc zero) = Wave.zeroReceipt Wave.leavingZero
decodeAdaptive Wave.positive zero = Wave.positiveReceipt

adaptiveDecodeEncodeExact :
  ∀ {coarse} (receipt : Wave.AdaptiveResidual coarse) →
  decodeAdaptive coarse (encodeAdaptive receipt) ≡ receipt
adaptiveDecodeEncodeExact Wave.nonzeroReceipt = refl
adaptiveDecodeEncodeExact (Wave.zeroReceipt Wave.approachingZero) = refl
adaptiveDecodeEncodeExact (Wave.zeroReceipt Wave.leavingZero) = refl
adaptiveDecodeEncodeExact Wave.positiveReceipt = refl

adaptiveEncodeDecodeExact :
  (coarse : Wave.Scalar3) →
  (code : Fin (localResidualCount coarse)) →
  encodeAdaptive (decodeAdaptive coarse code) ≡ code
adaptiveEncodeDecodeExact Wave.negative zero = refl
adaptiveEncodeDecodeExact Wave.scalarZero zero = refl
adaptiveEncodeDecodeExact Wave.scalarZero (suc zero) = refl
adaptiveEncodeDecodeExact Wave.positive zero = refl

------------------------------------------------------------------------
-- Exact local least-width certificates.
------------------------------------------------------------------------

negativeNeedsZeroResidualBits : General.CeilLog2Certificate 1 0
negativeNeedsZeroResidualBits =
  General.ceilLog2Certificate ≤-refl least
  where
    least : (bits : Nat) → 1 ≤ General.pow2 bits → 0 ≤ bits
    least bits capacity = z≤n

zeroNeedsOneResidualBit : General.CeilLog2Certificate 2 1
zeroNeedsOneResidualBit =
  General.ceilLog2Certificate ≤-refl least
  where
    least : (bits : Nat) → 2 ≤ General.pow2 bits → 1 ≤ bits
    least zero ()
    least (suc remaining) capacity = s≤s z≤n

positiveNeedsZeroResidualBits : General.CeilLog2Certificate 1 0
positiveNeedsZeroResidualBits = negativeNeedsZeroResidualBits

------------------------------------------------------------------------
-- The local information geometry is therefore 0/1/0 bits over {-1,0,+1}.
------------------------------------------------------------------------
