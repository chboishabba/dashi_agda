module DASHI.Moonshine.OggSSP2BNormWeldLastLeafExact where

------------------------------------------------------------------------
-- TERMINAL SAME-OBJECT LEAF FOR THE 2B NORM WELD
--
-- The preferred route has now removed the representation-discovery leaves.
-- Paid source/runtime structure gives:
--
--   * source-native Tate cokernel 98304 -> 98580 -> 276;
--   * common/residual modular support 98280 + 24;
--   * unique residual degree-24 simple;
--   * dim Hom_Co1(24,Sym2(24)) = 1 with explicit Frobenius-square generator;
--   * standard modular block idempotents and naturality of module homomorphisms;
--   * Lean compilers: equivariant maps have invariant range, commuting
--     centralizer operators commute with 1+a, and a unique invariant 24-range
--     forces literal equality with Frobenius.
--
-- Consequently block-projector existence, norm equivariance, common-98280
-- recovery and target-side Frobenius uniqueness are no longer independent
-- scientific acquisitions.  The one surviving same-object leaf is to
-- instantiate the ACTUAL centralizer/group-algebra action and the already-
-- selected residual block idempotent on the source-native norm carrier.
--
-- Once that object is supplied, the existing rank/cokernel compilers force
-- the actual Tate head to the exterior-square/duad 276 model.  Stable Q10,
-- outer J2^5 and three-fibre transport are already downstream compilers.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.OggSSP2BCo1FrobeniusHomRigidityExact as Frob
import DASHI.Moonshine.OggSSP2BCentralizerMod2CancellationRigidityExact as Cancel
import DASHI.Moonshine.OggSSP2BModularBlockIdempotentSourceExact as Block

record NormWeldLastLeafStatus : Set where
  constructor norm-weld-last-leaf-status
  field
    targetSocleFrobeniusRuntimePaid : Bool
    residual24UniqueSimplePaid : Bool
    blockProjectorExistenceSourced : Bool
    residualBlockChoiceRuntimePaid : Bool
    blockNaturalityIsCompilerConsequence : Bool
    normEquivarianceIsCompilerConsequence : Bool
    common98280RecoveryIsCompilerConsequence : Bool

    actualCentralizerActionInstantiationPaid : Bool
    actualResidualBlockActionInstantiationPaid : Bool
    actualTateExteriorSquareWeldPaid : Bool

    remainingSameObjectLeafCount : Nat
    nextResidual : String

canonicalNormWeldLastLeafStatus : NormWeldLastLeafStatus
canonicalNormWeldLastLeafStatus =
  norm-weld-last-leaf-status
    true true true true true true true
    false false false
    1
    "Instantiate the actual C_M(2B)/Co1 module or group-algebra action on the source-native mod-2 norm carrier and apply the runtime-selected residual central block idempotent there. All norm commutation, block preservation, residual rank-24, Frobenius-range equality, common-98280 recovery and exterior-square cokernel steps are compiler consequences once this same-object action is present."

targetSocleFrobeniusRuntimeIsPaid :
  NormWeldLastLeafStatus.targetSocleFrobeniusRuntimePaid
    canonicalNormWeldLastLeafStatus
  ≡ true
targetSocleFrobeniusRuntimeIsPaid = refl

blockProjectorExistenceIsSourced :
  NormWeldLastLeafStatus.blockProjectorExistenceSourced
    canonicalNormWeldLastLeafStatus
  ≡ true
blockProjectorExistenceIsSourced = refl

blockNaturalityIsCompilerConsequence :
  NormWeldLastLeafStatus.blockNaturalityIsCompilerConsequence
    canonicalNormWeldLastLeafStatus
  ≡ true
blockNaturalityIsCompilerConsequence = refl

normEquivarianceIsCompilerConsequence :
  NormWeldLastLeafStatus.normEquivarianceIsCompilerConsequence
    canonicalNormWeldLastLeafStatus
  ≡ true
normEquivarianceIsCompilerConsequence = refl

actualCentralizerActionInstantiationStillOpen :
  NormWeldLastLeafStatus.actualCentralizerActionInstantiationPaid
    canonicalNormWeldLastLeafStatus
  ≡ false
actualCentralizerActionInstantiationStillOpen = refl

actualResidualBlockActionInstantiationStillOpen :
  NormWeldLastLeafStatus.actualResidualBlockActionInstantiationPaid
    canonicalNormWeldLastLeafStatus
  ≡ false
actualResidualBlockActionInstantiationStillOpen = refl

actualTateExteriorSquareWeldStillOpen :
  NormWeldLastLeafStatus.actualTateExteriorSquareWeldPaid
    canonicalNormWeldLastLeafStatus
  ≡ false
actualTateExteriorSquareWeldStillOpen = refl

remainingSameObjectLeafCountIsOne :
  NormWeldLastLeafStatus.remainingSameObjectLeafCount
    canonicalNormWeldLastLeafStatus
  ≡ 1
remainingSameObjectLeafCountIsOne = refl

-- Cross-check that the source owners still expose the paid ingredients rather
-- than this status file silently manufacturing them.
frobeniusHomRuntimePaidUpstream :
  Frob.FrobeniusHomRigidityBoundary.homUniquenessRuntimePaid
    Frob.canonicalFrobeniusHomRigidityBoundary
  ≡ true
frobeniusHomRuntimePaidUpstream = Frob.homUniquenessRuntimeIsPaid

residual24UniqueSimplePaidUpstream :
  Cancel.CancellationRigidityBoundary.residual24UniqueSimpleIdentified
    Cancel.canonicalCancellationRigidityBoundary
  ≡ true
residual24UniqueSimplePaidUpstream = Cancel.residual24UniqueSimpleIsPaid

blockExistenceSourcedUpstream :
  Block.ModularBlockIdempotentSourceStatus.centralPrimitiveIdempotentsSourced
    Block.canonicalModularBlockIdempotentSourceStatus
  ≡ true
blockExistenceSourcedUpstream = refl
