{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP109TangentialGaussianCancellationRecutExact where

------------------------------------------------------------------------
-- ARCHAEOLOGY RE-CUT OF THE CMP109 DIRECT-BETA GAUSSIAN LEAF
--
-- The current direct A1 carrier asks for a broad
-- `constrainedWardCancellationInsideTrace` payment.  An older theorem owner
-- already proves a substantial part of that payment on the exact finite
-- rational constrained-coordinate carrier:
--
--   tr(Ahat^-1 (K^T Ahat + Ahat K)) = 2 tr K,
--
-- hence the -1/2 log-determinant response of a pure tangential change of free
-- constrained coordinates cancels the induced coordinate-volume Jacobian.
--
-- This module does NOT identify the literal CMP99/CMP109 Gaussian with that
-- finite rational carrier.  It isolates the remaining same-object weld and
-- records that, after the weld, tangential basis motion is compiler-paid rather
-- than a new Yang--Mills analytic theorem.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanFiniteRationalTraceConnectionCancellationExact as Trace
import DASHI.Physics.YangMills.BalabanCMP109DirectBetaSourceCutsetExact as Direct

------------------------------------------------------------------------
-- SAME-OBJECT PAYMENT SURFACE
------------------------------------------------------------------------

record CMP109TangentialGaussianSameObjectWeld (Index : Set) : Set₁ where
  field
    -- Existing theorem-bearing rational response.
    response : Trace.InducedVolumeJacobianResponse Index

    -- Physical/source welds only.  These are deliberately proof-relevant Sets,
    -- not booleans or theorem-name receipts.
    restrictedOperatorIsLiteralCMP109ConstrainedGaussian : Set
    connectionVariationIsLiteralTangentialBackgroundVariation : Set
    volumeResponseIsLiteralCMPGaussianChangeOfVariablesJacobian : Set

open CMP109TangentialGaussianSameObjectWeld public

cmp109TangentialGaussianContribution :
  ∀ {Index} → CMP109TangentialGaussianSameObjectWeld Index → ℚ
cmp109TangentialGaussianContribution weld =
  Trace.logVolumeDerivative (response weld)

cmp109TangentialLogDetContribution :
  ∀ {Index} → CMP109TangentialGaussianSameObjectWeld Index → ℚ
cmp109TangentialLogDetContribution weld =
  Trace.matrixTrace
    (Trace.carrier (Trace.connection (response weld)))
    (DASHI.Physics.YangMills.BalabanConstructiveRationalMatrixInverseExact.multiplyMatrix
      (Trace.carrier (Trace.connection (response weld)))
      (Trace.inverseRestricted (Trace.connection (response weld)))
      (Trace.connectionVariation (Trace.connection (response weld))))

-- The same-object weld does not add analytic content to this equality.  Once
-- the literal source objects are identified with the existing response, the
-- cancellation theorem is exactly the older finite rational theorem.
cmp109TangentialGaussianCancels :
  ∀ {Index} (weld : CMP109TangentialGaussianSameObjectWeld Index) →
  Trace.logVolumeDerivative (response weld)
    Data.Rational.Base.-
      (Data.Rational.Base._*_
        (Data.Rational.Base._/_ (Data.Integer.Base.+ 1) 2)
        (cmp109TangentialLogDetContribution weld))
  ≡ 0ℚ
cmp109TangentialGaussianCancels weld =
  Trace.gaussianTangentialConnectionCancelsVolumeJacobian (response weld)

------------------------------------------------------------------------
-- CURRENT A1 RE-CUT
------------------------------------------------------------------------

-- This is a route classification, not a proof of the remaining physical weld.
tangentialTraceAlgebraNeedsReproofForA1 : Bool
tangentialTraceAlgebraNeedsReproofForA1 = false

literalCMPGaussianJacobianSameObjectWeldOpen : Bool
literalCMPGaussianJacobianSameObjectWeldOpen = true

normalConstrainedSubspaceMotionStillPhysical : Bool
normalConstrainedSubspaceMotionStillPhysical = true

fourierBrillouinSameOperatorIdentificationStillPhysical : Bool
fourierBrillouinSameOperatorIdentificationStillPhysical = true

positiveBetaZLowerBoundStillPhysical : Bool
positiveBetaZLowerBoundStillPhysical = true

fullDirectA1ClosedByThisModule : Bool
fullDirectA1ClosedByThisModule = false

tangentialTraceAlgebraNeedsReproofForA1IsFalse :
  tangentialTraceAlgebraNeedsReproofForA1 ≡ false
tangentialTraceAlgebraNeedsReproofForA1IsFalse = refl

literalCMPGaussianJacobianSameObjectWeldOpenIsTrue :
  literalCMPGaussianJacobianSameObjectWeldOpen ≡ true
literalCMPGaussianJacobianSameObjectWeldOpenIsTrue = refl

normalConstrainedSubspaceMotionStillPhysicalIsTrue :
  normalConstrainedSubspaceMotionStillPhysical ≡ true
normalConstrainedSubspaceMotionStillPhysicalIsTrue = refl

fullDirectA1ClosedByThisModuleIsFalse :
  fullDirectA1ClosedByThisModule ≡ false
fullDirectA1ClosedByThisModuleIsFalse = refl

cmp109TangentialTraceCancellationCompilerLevel : ProofLevel
cmp109TangentialTraceCancellationCompilerLevel = machineChecked

cmp109TangentialGaussianSameObjectWeldLevel : ProofLevel
cmp109TangentialGaussianSameObjectWeldLevel = conditional

cmp109NormalMotionAndPhysicalBetaLevel : ProofLevel
cmp109NormalMotionAndPhysicalBetaLevel =
  Direct.cmp109LiteralGaussianSymbolsAndPositiveBetaZLevel
