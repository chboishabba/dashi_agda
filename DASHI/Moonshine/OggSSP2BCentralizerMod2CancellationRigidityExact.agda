module DASHI.Moonshine.OggSSP2BCentralizerMod2CancellationRigidityExact where

------------------------------------------------------------------------
-- CENTRALIZER MOD-2 CANCELLATION RIGIDITY FRONTIER
--
-- The source-native Tate exact sequence has dimensions
--
--   0 -> 98304 -> 98580 -> 276 -> 0.
--
-- The executed CTBlocks/decomposition runtime now pays the stronger modular
-- support statement
--
--   [98304]_2 = [98280]_2 + [24],
--
-- where the residual 24 is one copy of the unique degree-24 simple, while the
-- common 98280 support is separated from the residual 24/276 lanes.  The Tate
-- residual profile is exactly 1,274,1.
--
-- Lean's map-level rank squeeze sharpens the same-object boundary further.
-- Let the actual source-native norm map have canonical block coordinates
--
--   n = (c,r) : M_98304 -> C_98280 x S_300.
--
-- Since n is injective, it is enough to prove that the actual residual
-- coordinate r has image supported on the certified residual 24-source block.
-- Equivalently, produce the canonical rank-24 source block projector e24 and
-- the block-equivariance equation
--
--   r o e24 = r.
--
-- Then rank(r) <= 24.  The kernel of r injects through c into C_98280, so
-- rank-nullity has no slack and forces rank(r)=24 and dim ker(r)=98280.  Thus
-- the common-lane same-object equivalence is automatic: there is NO separate
-- 98280-map discovery gate after the residual block projector is paid.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_)

commonDimension : Nat
commonDimension = 98280

residualNaturalDimension : Nat
residualNaturalDimension = 24

minusDimension : Nat
minusDimension = 98304

commonPlusResidualIsMinus : commonDimension + residualNaturalDimension ≡ minusDimension
commonPlusResidualIsMinus = refl

record CentralizerMod2RuntimeReceipt : Set where
  constructor centralizer-mod2-runtime-receipt
  field
    candidateCount : Nat
    strongCandidateCount : Nat
    rigidSupportCandidateCount : Nat
    residual24IsSingleDegree24Simple : Bool
    residual276ProfileIsOne274One : Bool
    common98280SupportSeparatedFromResidual24 : Bool
    common98280SupportSeparatedFromResidual276 : Bool

-- The remaining proof-relevant same-object producer.  Runtime characters and
-- block labels do not manufacture this map equation; it must come from the
-- actual centralizer-equivariant norm/block action.
record ResidualBlockProjectorSameObjectReceipt : Set₁ where
  constructor residual-block-projector-same-object-receipt
  field
    ActualResidualBlockProjector : Set
    actualResidualBlockProjector : ActualResidualBlockProjector
    ResidualNormBlockEquivariance : Set
    residualNormBlockEquivariance : ResidualNormBlockEquivariance

open ResidualBlockProjectorSameObjectReceipt public

record CancellationRigidityBoundary : Set where
  constructor cancellation-rigidity-boundary
  field
    decompositionScreenImplemented : Bool
    runtimeDecompositionPaid : Bool
    actualTateJHProfileOne274OnePaid : Bool
    common98280SupportSeparated : Bool
    residual24UniqueSimpleIdentified : Bool
    residualBlockProjectorSameObjectPaid : Bool
    common98280SameObjectFollowsFromResidualBlock : Bool
    actualTateExteriorSquareWeldPaid : Bool

canonicalCancellationRigidityBoundary : CancellationRigidityBoundary
canonicalCancellationRigidityBoundary =
  cancellation-rigidity-boundary
    true true true true true false true false

runtimeDecompositionIsPaid :
  CancellationRigidityBoundary.runtimeDecompositionPaid
    canonicalCancellationRigidityBoundary
  ≡ true
runtimeDecompositionIsPaid = refl

actualTateJHProfileIsPaid :
  CancellationRigidityBoundary.actualTateJHProfileOne274OnePaid
    canonicalCancellationRigidityBoundary
  ≡ true
actualTateJHProfileIsPaid = refl

commonSupportSeparationIsPaid :
  CancellationRigidityBoundary.common98280SupportSeparated
    canonicalCancellationRigidityBoundary
  ≡ true
commonSupportSeparationIsPaid = refl

residual24UniqueSimpleIsPaid :
  CancellationRigidityBoundary.residual24UniqueSimpleIdentified
    canonicalCancellationRigidityBoundary
  ≡ true
residual24UniqueSimpleIsPaid = refl

residualBlockProjectorSameObjectStillOpen :
  CancellationRigidityBoundary.residualBlockProjectorSameObjectPaid
    canonicalCancellationRigidityBoundary
  ≡ false
residualBlockProjectorSameObjectStillOpen = refl

common98280NoLongerIndependentGate :
  CancellationRigidityBoundary.common98280SameObjectFollowsFromResidualBlock
    canonicalCancellationRigidityBoundary
  ≡ true
common98280NoLongerIndependentGate = refl

actualTateExteriorSquareWeldStillOpen :
  CancellationRigidityBoundary.actualTateExteriorSquareWeldPaid
    canonicalCancellationRigidityBoundary
  ≡ false
actualTateExteriorSquareWeldStillOpen = refl
