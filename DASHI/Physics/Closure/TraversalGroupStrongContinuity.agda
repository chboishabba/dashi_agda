module DASHI.Physics.Closure.TraversalGroupStrongContinuity where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Unifier using (ℝ; HilbertSpace; WaveLift; _+ℝ_; toℝ)
import DASHI.Quantum.DepthEmbeddingIsometry as Depth
import DASHI.Quantum.Stone as Stone
import DASHI.Quantum.StrongContinuity as Strong

------------------------------------------------------------------------
-- Gate 5 finite traversal group strong-continuity receipt.
--
-- This module is deliberately small: it threads the existing one-point
-- finite Stone/Hilbert carrier through the Gate 5 traversal group and strong
-- continuity surfaces.  It does not promote the finite one-point carrier to a
-- noncollapsed physical Hilbert completion or a physical Stone bundle.

data Gate5TraversalStrongContinuityBlocker : Set where
  missingNoncollapsedPhysicalHilbertCompletion :
    Gate5TraversalStrongContinuityBlocker

  missingGNSHilbertToDASHIHilbertBridge :
    Gate5TraversalStrongContinuityBlocker

  missingPhysicalTraversalUnitaryGroup :
    Gate5TraversalStrongContinuityBlocker

  missingPhysicalStrongContinuityOnCompletion :
    Gate5TraversalStrongContinuityBlocker

  missingTraversalDerivedPhysicalStoneBundle :
    Gate5TraversalStrongContinuityBlocker

canonicalGate5TraversalStrongContinuityBlockers :
  List Gate5TraversalStrongContinuityBlocker
canonicalGate5TraversalStrongContinuityBlockers =
  missingNoncollapsedPhysicalHilbertCompletion
  ∷ missingGNSHilbertToDASHIHilbertBridge
  ∷ missingPhysicalTraversalUnitaryGroup
  ∷ missingPhysicalStrongContinuityOnCompletion
  ∷ missingTraversalDerivedPhysicalStoneBundle
  ∷ []

record Gate5FiniteTraversalGroupStrongContinuityReceipt : Setω where
  field
    finiteStoneProgress :
      Stone.FiniteStoneUnitaryContinuityGeneratorProgress

    finiteStoneProgressTyped :
      Stone.FiniteStoneUnitaryContinuityGeneratorProgress.finiteUnitaryContinuityGeneratorTyped
        finiteStoneProgress
      ≡
      true

    finiteDepthSkeleton :
      Stone.FiniteDepthIdentityStoneTowerSkeleton

    finiteDepthSkeletonIsProgressSkeleton :
      Stone.FiniteDepthIdentityStoneTowerSkeleton.finiteDepthTowerOnly
        finiteDepthSkeleton
      ≡
      true

    finiteDepthPhysicalPromotionClosed :
      Stone.FiniteDepthIdentityStoneTowerSkeleton.physicalHilbertStonePromotion
        finiteDepthSkeleton
      ≡
      false

    depthEmbeddingWitness :
      Depth.DepthEmbeddingConcreteWitness

    depthEmbeddingCarrierIsCanonical :
      Depth.DepthEmbeddingConcreteWitness.carrier depthEmbeddingWitness
      ≡
      Depth.DepthCarrier

    onePointDepthTransitionSystem :
      Stone.HilbertInductiveLimitTransitionSystem

    onePointDepthTransitionSystemIsCanonicalH0 :
      Stone.HilbertInductiveLimitTransitionSystem.H_d
        onePointDepthTransitionSystem
        (0)
      ≡
      Stone.onePointFiniteHilbertSpace

    finiteTraversalDepthData :
      Stone.TraversalUnitaryDepthData onePointDepthTransitionSystem

    finiteTraversalDepthDataUnitaryOnly :
      Stone.TraversalUnitaryDepthData.finiteTraversalUnitaryOnly
        finiteTraversalDepthData
      ≡
      true

    finiteTraversalDepthPhysicalPromotionClosed :
      Stone.TraversalUnitaryDepthData.physicalTraversalUnitaryPromoted
        finiteTraversalDepthData
      ≡
      false

    finiteTraversalGroup :
      Stone.StoneGroup Stone.onePointFiniteLift

    finiteTraversalGroupIdentityAtZero :
      (x : HilbertSpace.H Stone.onePointFiniteHilbertSpace) →
      WaveLift.U Stone.onePointFiniteLift (toℝ 0) x
      ≡
      x

    finiteTraversalGroupComposition :
      (s t : ℝ) →
      (x : HilbertSpace.H Stone.onePointFiniteHilbertSpace) →
      WaveLift.U Stone.onePointFiniteLift (s +ℝ t) x
      ≡
      WaveLift.U Stone.onePointFiniteLift
        s
        (WaveLift.U Stone.onePointFiniteLift t x)

    finiteStrongContinuity :
      Stone.StoneContinuity
        (WaveLift.U Stone.onePointFiniteLift)
        Stone.onePointFiniteDistance

    finiteStrongContinuityMatchesOnePoint :
      finiteStrongContinuity
      ≡
      Stone.onePointFiniteStrongContinuity

    strongContinuityWitness :
      Strong.StrongContinuityWitness

    strongContinuityWitnessMatchesFiniteStone :
      Strong.StrongContinuityWitness.strongContinuity
        strongContinuityWitness
      ≡
      Stone.onePointFiniteStrongContinuity

    physicalTraversalReceipt :
      Stone.PhysicalTraversalUnitaryGroupReceipt

    finiteStrongContinuityThreadedFromTraversalReceipt :
      Bool

    finiteStrongContinuityThreadedFromTraversalReceipt-v :
      finiteStrongContinuityThreadedFromTraversalReceipt ≡ true

    traversalGroupShapeReceipt :
      Stone.U5PhysicalTraversalUnitaryGroupReceiptShape

    finiteTraversalGroupShapeAvailable :
      Stone.U5PhysicalTraversalUnitaryGroupReceiptShape.finiteTraversalUnitaryGroupShapeAvailable
        traversalGroupShapeReceipt
      ≡
      true

    physicalTraversalGroupSupplied :
      Stone.U5PhysicalTraversalUnitaryGroupReceiptShape.noncollapsedPhysicalTraversalUnitarySupplied
        traversalGroupShapeReceipt
      ≡
      false

    strongContinuityAttemptReceipt :
      Stone.U5GNSHilbertDASHIStoneStrongContinuityAttemptReceipt

    finiteStrongContinuityMatchesAttempt :
      Bool

    finiteStrongContinuityMatchesAttempt-v :
      finiteStrongContinuityMatchesAttempt ≡ true

    physicalStrongContinuityAttemptClosed :
      Stone.PhysicalTraversalUnitaryGroupReceipt.physicalStrongContinuityPromoted
        (Stone.U5GNSHilbertDASHIStoneStrongContinuityAttemptReceipt.physicalTraversalReceipt
          strongContinuityAttemptReceipt)
      ≡
      false

    finiteTraversalGroupConstructed :
      Bool

    finiteTraversalGroupConstructed-v :
      finiteTraversalGroupConstructed ≡ true

    finiteStrongContinuityConstructed :
      Bool

    finiteStrongContinuityConstructed-v :
      finiteStrongContinuityConstructed ≡ true

    physicalHilbertCompletionPromoted :
      Bool

    physicalHilbertCompletionPromoted-v :
      physicalHilbertCompletionPromoted ≡ false

    physicalStrongContinuityPromoted :
      Bool

    physicalStrongContinuityPromoted-v :
      physicalStrongContinuityPromoted ≡ false

    traversalDerivedPhysicalStoneBundlePromoted :
      Bool

    traversalDerivedPhysicalStoneBundlePromoted-v :
      traversalDerivedPhysicalStoneBundlePromoted ≡ false

    firstBlocker :
      Gate5TraversalStrongContinuityBlocker

    firstBlocker-v :
      firstBlocker ≡ missingNoncollapsedPhysicalHilbertCompletion

    blockers :
      List Gate5TraversalStrongContinuityBlocker

    blockers-v :
      blockers ≡ canonicalGate5TraversalStrongContinuityBlockers

    receiptBoundary :
      List String

open Gate5FiniteTraversalGroupStrongContinuityReceipt public

canonicalGate5FiniteTraversalGroupStrongContinuityReceipt :
  Gate5FiniteTraversalGroupStrongContinuityReceipt
canonicalGate5FiniteTraversalGroupStrongContinuityReceipt =
  record
    { finiteStoneProgress =
        Stone.onePointFiniteStoneUnitaryContinuityGeneratorProgress
    ; finiteStoneProgressTyped =
        refl
    ; finiteDepthSkeleton =
        Stone.onePointFiniteDepthIdentityStoneTowerSkeleton
    ; finiteDepthSkeletonIsProgressSkeleton =
        refl
    ; finiteDepthPhysicalPromotionClosed =
        refl
    ; depthEmbeddingWitness =
        Depth.canonicalDepthEmbeddingConcreteWitness
    ; depthEmbeddingCarrierIsCanonical =
        refl
    ; onePointDepthTransitionSystem =
        Stone.onePointConstantDepthTransitionSystem
    ; onePointDepthTransitionSystemIsCanonicalH0 =
        refl
    ; finiteTraversalDepthData =
        Stone.onePointTraversalUnitaryDepthData
    ; finiteTraversalDepthDataUnitaryOnly =
        refl
    ; finiteTraversalDepthPhysicalPromotionClosed =
        refl
    ; finiteTraversalGroup =
        Stone.onePointFiniteUnitaryGroup
    ; finiteTraversalGroupIdentityAtZero =
        λ _ → refl
    ; finiteTraversalGroupComposition =
        λ _ _ _ → refl
    ; finiteStrongContinuity =
        Stone.onePointFiniteStrongContinuity
    ; finiteStrongContinuityMatchesOnePoint =
        refl
    ; strongContinuityWitness =
        Strong.canonicalStrongContinuityWitness
    ; strongContinuityWitnessMatchesFiniteStone =
        refl
    ; physicalTraversalReceipt =
        Stone.canonicalPhysicalTraversalUnitaryGroupReceipt
    ; finiteStrongContinuityThreadedFromTraversalReceipt =
        true
    ; finiteStrongContinuityThreadedFromTraversalReceipt-v =
        refl
    ; traversalGroupShapeReceipt =
        Stone.canonicalU5PhysicalTraversalUnitaryGroupReceiptShape
    ; finiteTraversalGroupShapeAvailable =
        refl
    ; physicalTraversalGroupSupplied =
        refl
    ; strongContinuityAttemptReceipt =
        Stone.canonicalU5GNSHilbertDASHIStoneStrongContinuityAttemptReceipt
    ; finiteStrongContinuityMatchesAttempt =
        true
    ; finiteStrongContinuityMatchesAttempt-v =
        refl
    ; physicalStrongContinuityAttemptClosed =
        refl
    ; finiteTraversalGroupConstructed =
        true
    ; finiteTraversalGroupConstructed-v =
        refl
    ; finiteStrongContinuityConstructed =
        true
    ; finiteStrongContinuityConstructed-v =
        refl
    ; physicalHilbertCompletionPromoted =
        false
    ; physicalHilbertCompletionPromoted-v =
        refl
    ; physicalStrongContinuityPromoted =
        false
    ; physicalStrongContinuityPromoted-v =
        refl
    ; traversalDerivedPhysicalStoneBundlePromoted =
        false
    ; traversalDerivedPhysicalStoneBundlePromoted-v =
        refl
    ; firstBlocker =
        missingNoncollapsedPhysicalHilbertCompletion
    ; firstBlocker-v =
        refl
    ; blockers =
        canonicalGate5TraversalStrongContinuityBlockers
    ; blockers-v =
        refl
    ; receiptBoundary =
        "Gate 5 finite traversal group strong-continuity is inhabited by the existing one-point Stone carrier"
        ∷ "The Hilbert depth embedding, finite traversal unitary data, Stone group identity/composition, and epsilon-delta strong-continuity surface are concrete refl/one-point witnesses"
        ∷ "The receipt threads the existing GNS/Stone handoff and strong-continuity attempt receipts but does not build a GNS-to-DASHI Hilbert bridge"
        ∷ "Physical Hilbert completion, noncollapsed physical traversal unitary group, physical strong continuity, and traversal-derived physical Stone bundle remain false"
        ∷ []
    }

gate5FiniteTraversalGroupConstructed :
  finiteTraversalGroupConstructed
    canonicalGate5FiniteTraversalGroupStrongContinuityReceipt
  ≡
  true
gate5FiniteTraversalGroupConstructed =
  refl

gate5FiniteStrongContinuityConstructed :
  finiteStrongContinuityConstructed
    canonicalGate5FiniteTraversalGroupStrongContinuityReceipt
  ≡
  true
gate5FiniteStrongContinuityConstructed =
  refl

gate5PhysicalStrongContinuityStillClosed :
  physicalStrongContinuityPromoted
    canonicalGate5FiniteTraversalGroupStrongContinuityReceipt
  ≡
  false
gate5PhysicalStrongContinuityStillClosed =
  refl
