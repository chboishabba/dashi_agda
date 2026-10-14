module DASHI.Moonshine.OggSSP2BPostSocleMaxCutExact where

------------------------------------------------------------------------
-- POST-SOCLE CANONICAL 2B MAX-CUT
--
-- This owner supersedes the older acquisition wording without deleting it.
-- The latest finite/runtime work has removed target-side representation search:
-- Co1 Sym2(24) has one Frobenius 24 Hom/socle line, and the residual block is
-- already selected by CTBlocks.  Lean now separately compiles:
--
--   centralizer commutation -> norm (1+a) equivariance;
--   module linearity -> central block naturality;
--   equivariance -> invariant residual range;
--   rank/support squeeze -> residual rank 24;
--   Frobenius socle containment -> unique invariant 24 range;
--   range equality + common-lane cancellation -> Tate cokernel = wedge2(24).
--
-- Therefore the one scientific same-object leaf before the Tate/duad weld is
-- no longer "discover a 24" or "prove equivariance".  It is to instantiate the
-- ACTUAL centralizer/group-algebra action and the runtime-selected residual
-- block idempotent on the source-native norm carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.OggSSP2BNormWeldLastLeafExact as Last
import DASHI.Moonshine.OggSSP2BDefectProvenanceSearchNoGoExact as Defect

record PostSocleMaxCutStatus : Set where
  constructor post-socle-max-cut-status
  field
    tateBrauerIngressPaid : Bool
    finiteTenFactorsPaid : Bool
    finiteOuterJ2x5Paid : Bool
    integralTateCokernelPaid : Bool
    co1FrobeniusSocleRigidityPaid : Bool
    residualBlockLabelPaid : Bool

    normEquivarianceCompilerPaid : Bool
    blockNaturalityCompilerPaid : Bool
    invariantRangeCompilerPaid : Bool
    rankTwentyFourCompilerPaid : Bool
    uniqueRangeCompilerPaid : Bool
    exteriorCokernelCompilerPaid : Bool

    actualCentralizerBlockActionOnNormCarrierPaid : Bool
    actualTateExteriorSquareWeldPaid : Bool
    actualTateStableQ10Paid : Bool
    actualOuterJ2x5OnSameQPaid : Bool
    actualThreeFibreQ10TransportPaid : Bool

    remainingNormWeldSameObjectLeaves : Nat
    remainingDefectSourceBits : Nat
    downstream31Paid : Bool
    downstream279Paid : Bool
    nextResidual : String

canonicalPostSocleMaxCutStatus : PostSocleMaxCutStatus
canonicalPostSocleMaxCutStatus =
  post-socle-max-cut-status
    true true true true true true
    true true true true true true
    false false false false false
    1 2 false false
    "Instantiate the actual C_M(2B)/Co1 module or group-algebra action and the selected residual block idempotent on the source-native norm carrier. The existing compiler chain then forces the residual image to Frobenius 24, identifies the Tate 276 with wedge2(24)/duads, transports an explicit finite M22:2-stable Q10 into the actual Tate head, imports the paid outer J2^5 Completion10 action on that same quotient, and transports the same Q10 across the three 2B fibres. Keep the two Mode5/2T provenance bits independent; only after this core closes should 31 and 279 be promoted."

remainingNormWeldSameObjectLeavesIsOne :
  PostSocleMaxCutStatus.remainingNormWeldSameObjectLeaves
    canonicalPostSocleMaxCutStatus
  ≡ 1
remainingNormWeldSameObjectLeavesIsOne = refl

remainingDefectSourceBitsIsTwo :
  PostSocleMaxCutStatus.remainingDefectSourceBits
    canonicalPostSocleMaxCutStatus
  ≡ 2
remainingDefectSourceBitsIsTwo = refl

actualCentralizerBlockActionStillOpen :
  PostSocleMaxCutStatus.actualCentralizerBlockActionOnNormCarrierPaid
    canonicalPostSocleMaxCutStatus
  ≡ false
actualCentralizerBlockActionStillOpen = refl

actualTateExteriorSquareWeldStillOpen :
  PostSocleMaxCutStatus.actualTateExteriorSquareWeldPaid
    canonicalPostSocleMaxCutStatus
  ≡ false
actualTateExteriorSquareWeldStillOpen = refl

lastLeafCountAgrees :
  Last.NormWeldLastLeafStatus.remainingSameObjectLeafCount
    Last.canonicalNormWeldLastLeafStatus
  ≡ 1
lastLeafCountAgrees = Last.remainingSameObjectLeafCountIsOne

defectBitCountAgrees : Defect.remainingSourceDecisionCount ≡ 2
defectBitCountAgrees = Defect.remainingSourceDecisionCountIsTwo
