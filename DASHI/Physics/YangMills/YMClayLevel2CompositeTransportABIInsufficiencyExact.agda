{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLevel2CompositeTransportABIInsufficiencyExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCompositeOperatorRGParallelTransportExact as Transport

------------------------------------------------------------------------
-- D2 SOUNDNESS AUDIT / BARE TRANSPORT ABI IS NOT PHYSICAL OPERATOR MIXING
--
-- CompositeRGParallelTransport currently asks only for
--
--   oneStepMixing : Nat -> Operator -> Operator
--   CovariantlyConstantAtStep
--   parallelTransportEquation
--
-- with no linearity, insertion naturality, blocking compatibility, or relation
-- to an actual RG state transition.
--
-- Consequently ANY chosen operator trajectory can generate an inhabitant by
-- making the "mixing map" ignore its operator argument and return the next
-- trajectory value.  This theorem is constructive evidence that a bare
-- CompositeRGParallelTransport inhabitant must not be counted as D2a physics.
------------------------------------------------------------------------

transportFromArbitraryTrajectory :
  ∀ {Operator : Set} →
  (trajectory : Nat → Operator) →
  Transport.CompositeRGParallelTransport Operator
transportFromArbitraryTrajectory trajectory = record
  { Transport.CompositeRGParallelTransport.oneStepMixing =
      λ depth _ → trajectory (suc depth)
  ; Transport.CompositeRGParallelTransport.CovariantlyConstantAtStep =
      λ depth operator → trajectory (suc depth) ≡ operator
  ; Transport.CompositeRGParallelTransport.parallelTransportEquation =
      λ depth operator proof → proof
  }

arbitraryTrajectoryTransportReproducesTrajectory :
  ∀ {Operator : Set}
    (trajectory : Nat → Operator) →
  ∀ depth →
  Transport.transportToDepth
    (transportFromArbitraryTrajectory trajectory)
    depth (trajectory zero)
  ≡ trajectory depth
arbitraryTrajectoryTransportReproducesTrajectory trajectory zero = refl
arbitraryTrajectoryTransportReproducesTrajectory trajectory (suc depth) = refl

bareCompositeRGParallelTransportCanBeManufacturedFromAnyTrajectory : Bool
bareCompositeRGParallelTransportCanBeManufacturedFromAnyTrajectory = true

bareCompositeRGParallelTransportCanBeManufacturedFromAnyTrajectoryIsTrue :
  bareCompositeRGParallelTransportCanBeManufacturedFromAnyTrajectory ≡ true
bareCompositeRGParallelTransportCanBeManufacturedFromAnyTrajectoryIsTrue = refl

bareTransportInhabitantPaysPhysicalD2a : Bool
bareTransportInhabitantPaysPhysicalD2a = false

bareTransportInhabitantPaysPhysicalD2aIsFalse :
  bareTransportInhabitantPaysPhysicalD2a ≡ false
bareTransportInhabitantPaysPhysicalD2aIsFalse = refl

physicalD2aNeedsInsertionOrBlockingNaturality : Bool
physicalD2aNeedsInsertionOrBlockingNaturality = true

physicalD2aNeedsInsertionOrBlockingNaturalityIsTrue :
  physicalD2aNeedsInsertionOrBlockingNaturality ≡ true
physicalD2aNeedsInsertionOrBlockingNaturalityIsTrue = refl

transportABISoundnessAuditLevel : ProofLevel
transportABISoundnessAuditLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
