module DASHI.Physics.Closure.StoneTheoremCarrierReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Quantum.Stone as Stone
import DASHI.Quantum.Stone_Gates as StoneGates
import DASHI.Quantum.StrongContinuity as StrongContinuity
import DASHI.Unifier as Unifier

------------------------------------------------------------------------
-- Gate 5 Stone theorem carrier receipt.
--
-- This receipt consumes the finite one-point Stone carrier already present
-- in DASHI.Quantum.Stone, together with the strong-continuity and traversal
-- depth witnesses.  It records finite-depth self-adjoint generator existence
-- while keeping the physical Hilbert colimit/completion obligation explicit
-- and fail-closed.

data StoneTheoremCarrierReceiptStatus : Set where
  finiteStoneCarrierRecordedPhysicalHilbertColimitOpen :
    StoneTheoremCarrierReceiptStatus

data StoneTheoremCarrierBlocker : Set where
  finiteOnePointCarrierOnly :
    StoneTheoremCarrierBlocker

  missingNoncollapsedPhysicalHilbertColimit :
    StoneTheoremCarrierBlocker

  missingPhysicalTraversalUnitaryPromotion :
    StoneTheoremCarrierBlocker

  missingPhysicalStoneBridgeBoundary :
    StoneTheoremCarrierBlocker

  missingPhysicalHamiltonianSelfAdjointness :
    StoneTheoremCarrierBlocker

canonicalStoneTheoremCarrierBlockers :
  List StoneTheoremCarrierBlocker
canonicalStoneTheoremCarrierBlockers =
  finiteOnePointCarrierOnly
  ∷ missingNoncollapsedPhysicalHilbertColimit
  ∷ missingPhysicalTraversalUnitaryPromotion
  ∷ missingPhysicalStoneBridgeBoundary
  ∷ missingPhysicalHamiltonianSelfAdjointness
  ∷ []

record PhysicalHilbertColimitObligation : Setω where
  field
    physicalPrimitiveRequest :
      Stone.PhysicalHilbertStonePrimitiveRequest

    physicalPrimitiveRequestIsCanonical :
      physicalPrimitiveRequest
      ≡
      Stone.canonicalPhysicalHilbertStonePrimitiveRequest

    finiteWitnessAvailable :
      Bool

    finiteWitnessAvailableIsTrue :
      finiteWitnessAvailable ≡ true

    noncollapsedProjectionPrecursorAvailable :
      Stone.PhysicalHilbertStonePrimitiveRequest.noncollapsedProjectionPrecursorSupplied
        physicalPrimitiveRequest
      ≡
      true

    physicalProjectionAlgebraSuppliedFalse :
      Stone.PhysicalHilbertStonePrimitiveRequest.physicalProjectionAlgebraSupplied
        physicalPrimitiveRequest
      ≡
      false

    physicalHamiltonianSelfAdjointnessSuppliedFalse :
      Stone.PhysicalHilbertStonePrimitiveRequest.HamiltonianSelfAdjointnessSupplied
        physicalPrimitiveRequest
      ≡
      false

    stoneBridgeBoundarySuppliedFalse :
      Stone.PhysicalHilbertStonePrimitiveRequest.StoneBridgeBoundarySupplied
        physicalPrimitiveRequest
      ≡
      false

    physicalHilbertColimitConstructed :
      Bool

    physicalHilbertColimitConstructedIsFalse :
      physicalHilbertColimitConstructed ≡ false

    physicalHilbertColimitPromoted :
      Bool

    physicalHilbertColimitPromotedIsFalse :
      physicalHilbertColimitPromoted ≡ false

    physicalStonePromotionClosed :
      Stone.PhysicalHilbertStonePrimitiveRequest.physicalPromotion
        physicalPrimitiveRequest
      ≡
      false

    colimitObligationBoundary :
      List String

open PhysicalHilbertColimitObligation public

canonicalPhysicalHilbertColimitObligation :
  PhysicalHilbertColimitObligation
canonicalPhysicalHilbertColimitObligation =
  record
    { physicalPrimitiveRequest =
        Stone.canonicalPhysicalHilbertStonePrimitiveRequest
    ; physicalPrimitiveRequestIsCanonical =
        refl
    ; finiteWitnessAvailable =
        true
    ; finiteWitnessAvailableIsTrue =
        refl
    ; noncollapsedProjectionPrecursorAvailable =
        refl
    ; physicalProjectionAlgebraSuppliedFalse =
        refl
    ; physicalHamiltonianSelfAdjointnessSuppliedFalse =
        refl
    ; stoneBridgeBoundarySuppliedFalse =
        refl
    ; physicalHilbertColimitConstructed =
        false
    ; physicalHilbertColimitConstructedIsFalse =
        refl
    ; physicalHilbertColimitPromoted =
        false
    ; physicalHilbertColimitPromotedIsFalse =
        refl
    ; physicalStonePromotionClosed =
        refl
    ; colimitObligationBoundary =
        "The finite Stone carrier and primitive request are available"
        ∷ "The noncollapsed projection precursor is present only as precursor data"
        ∷ "Physical projection algebra, Hamiltonian self-adjointness, Stone bridge boundary, and Hilbert colimit completion remain unsupplied"
        ∷ "PhysicalHilbertColimitObligation is therefore fail-closed"
        ∷ []
    }

record FiniteDepthStoneSelfAdjointGeneratorReceipt : Setω where
  field
    finiteStoneData :
      Stone.FiniteSelfAdjointHamiltonianStoneData

    finiteStoneDataIsCanonical :
      finiteStoneData
      ≡
      Stone.onePointFiniteSelfAdjointHamiltonianStoneData

    finiteStoneBundle :
      Stone.StoneBundle
        (Stone.FiniteSelfAdjointHamiltonianStoneData.finiteTower
          finiteStoneData)
        (Stone.FiniteSelfAdjointHamiltonianStoneData.finiteHilbertSpace
          finiteStoneData)

    finiteStoneBundleIsDataBundle :
      finiteStoneBundle
      ≡
      Stone.FiniteSelfAdjointHamiltonianStoneData.finiteStoneBundle
        finiteStoneData

    generatorSelfAdjoint :
      Stone.StoneSelfAdjoint
        (Stone.FiniteSelfAdjointHamiltonianStoneData.finiteHilbertSpace
          finiteStoneData)
        (Stone.FiniteSelfAdjointHamiltonianStoneData.Hamiltonian
          finiteStoneData)

    generatorSelfAdjointIsDataWitness :
      generatorSelfAdjoint
      ≡
      Stone.FiniteSelfAdjointHamiltonianStoneData.HamiltonianSelfAdjoint
        finiteStoneData

    stoneTheoremConsequences :
      Stone.StoneConsequences finiteStoneBundle

    finiteStrongContinuity :
      Stone.StoneContinuity
        (Unifier.WaveLift.U
          (Stone.FiniteSelfAdjointHamiltonianStoneData.finiteLift
            finiteStoneData))
        (Stone.FiniteSelfAdjointHamiltonianStoneData.finiteDistance
          finiteStoneData)

    finiteStrongContinuityIsDataWitness :
      finiteStrongContinuity
      ≡
      Stone.FiniteSelfAdjointHamiltonianStoneData.finiteStrongContinuity
        finiteStoneData

    finiteDepthSelfAdjointGeneratorExists :
      Bool

    finiteDepthSelfAdjointGeneratorExistsIsTrue :
      finiteDepthSelfAdjointGeneratorExists ≡ true

    physicalHilbertTowerPromotedFalse :
      Stone.FiniteSelfAdjointHamiltonianStoneData.physicalHilbertTowerPromoted
        finiteStoneData
      ≡
      false

    finiteGeneratorBoundary :
      List String

open FiniteDepthStoneSelfAdjointGeneratorReceipt public

canonicalFiniteDepthStoneSelfAdjointGeneratorReceipt :
  FiniteDepthStoneSelfAdjointGeneratorReceipt
canonicalFiniteDepthStoneSelfAdjointGeneratorReceipt =
  record
    { finiteStoneData =
        Stone.onePointFiniteSelfAdjointHamiltonianStoneData
    ; finiteStoneDataIsCanonical =
        refl
    ; finiteStoneBundle =
        Stone.onePointFiniteStoneBundle
    ; finiteStoneBundleIsDataBundle =
        refl
    ; generatorSelfAdjoint =
        Stone.onePointFiniteHamiltonianSelfAdjoint
    ; generatorSelfAdjointIsDataWitness =
        refl
    ; stoneTheoremConsequences =
        Stone.Stone-theorem Stone.onePointFiniteStoneBundle
    ; finiteStrongContinuity =
        Stone.onePointFiniteStrongContinuity
    ; finiteStrongContinuityIsDataWitness =
        refl
    ; finiteDepthSelfAdjointGeneratorExists =
        true
    ; finiteDepthSelfAdjointGeneratorExistsIsTrue =
        refl
    ; physicalHilbertTowerPromotedFalse =
        refl
    ; finiteGeneratorBoundary =
        "The finite one-point Stone data supplies the identity Hamiltonian"
        ∷ "StoneSelfAdjoint is inherited from onePointFiniteHamiltonianSelfAdjoint"
        ∷ "Stone-theorem is consumed to expose the finite Stone consequences"
        ∷ "This records finite-depth self-adjoint generator existence only"
        ∷ []
    }

record StoneTheoremCarrierReceipt : Setω where
  field
    status :
      StoneTheoremCarrierReceiptStatus

    stoneGatesWitnessBundleAvailable :
      Bool

    stoneGatesWitnessBundleAvailableIsTrue :
      stoneGatesWitnessBundleAvailable ≡ true

    strongContinuityWitnessAvailable :
      Bool

    strongContinuityWitnessAvailableIsTrue :
      strongContinuityWitnessAvailable ≡ true

    finiteDepthIdentityStoneTowerSkeleton :
      Stone.FiniteDepthIdentityStoneTowerSkeleton

    finiteDepthIdentityStoneTowerSkeletonIsCanonical :
      finiteDepthIdentityStoneTowerSkeleton
      ≡
      Stone.onePointFiniteDepthIdentityStoneTowerSkeleton

    finiteTraversalUnitaryDepthData :
      Stone.TraversalUnitaryDepthData
        Stone.onePointConstantDepthTransitionSystem

    finiteTraversalUnitaryDepthDataIsCanonical :
      finiteTraversalUnitaryDepthData
      ≡
      Stone.onePointTraversalUnitaryDepthData

    finiteTraversalUnitaryOnly :
      Stone.TraversalUnitaryDepthData.finiteTraversalUnitaryOnly
        finiteTraversalUnitaryDepthData
      ≡
      true

    finiteTraversalPhysicalPromotionFalse :
      Stone.TraversalUnitaryDepthData.physicalTraversalUnitaryPromoted
        finiteTraversalUnitaryDepthData
      ≡
      false

    finiteSelfAdjointGeneratorReceipt :
      FiniteDepthStoneSelfAdjointGeneratorReceipt

    finiteDepthSelfAdjointGeneratorRecorded :
      finiteDepthSelfAdjointGeneratorExists
        finiteSelfAdjointGeneratorReceipt
      ≡
      true

    physicalHilbertColimitObligation :
      PhysicalHilbertColimitObligation

    physicalHilbertColimitStillFalse :
      physicalHilbertColimitPromoted
        physicalHilbertColimitObligation
      ≡
      false

    finiteStoneCarrierRecorded :
      Bool

    finiteStoneCarrierRecordedIsTrue :
      finiteStoneCarrierRecorded ≡ true

    physicalStoneCarrierPromoted :
      Bool

    physicalStoneCarrierPromotedIsFalse :
      physicalStoneCarrierPromoted ≡ false

    exactBlockers :
      List StoneTheoremCarrierBlocker

    exactBlockersAreCanonical :
      exactBlockers ≡ canonicalStoneTheoremCarrierBlockers

    receiptBoundary :
      List String

open StoneTheoremCarrierReceipt public

canonicalStoneTheoremCarrierReceipt :
  StoneTheoremCarrierReceipt
canonicalStoneTheoremCarrierReceipt =
  record
    { status =
        finiteStoneCarrierRecordedPhysicalHilbertColimitOpen
    ; stoneGatesWitnessBundleAvailable =
        true
    ; stoneGatesWitnessBundleAvailableIsTrue =
        refl
    ; strongContinuityWitnessAvailable =
        true
    ; strongContinuityWitnessAvailableIsTrue =
        refl
    ; finiteDepthIdentityStoneTowerSkeleton =
        Stone.onePointFiniteDepthIdentityStoneTowerSkeleton
    ; finiteDepthIdentityStoneTowerSkeletonIsCanonical =
        refl
    ; finiteTraversalUnitaryDepthData =
        Stone.onePointTraversalUnitaryDepthData
    ; finiteTraversalUnitaryDepthDataIsCanonical =
        refl
    ; finiteTraversalUnitaryOnly =
        refl
    ; finiteTraversalPhysicalPromotionFalse =
        refl
    ; finiteSelfAdjointGeneratorReceipt =
        canonicalFiniteDepthStoneSelfAdjointGeneratorReceipt
    ; finiteDepthSelfAdjointGeneratorRecorded =
        refl
    ; physicalHilbertColimitObligation =
        canonicalPhysicalHilbertColimitObligation
    ; physicalHilbertColimitStillFalse =
        refl
    ; finiteStoneCarrierRecorded =
        true
    ; finiteStoneCarrierRecordedIsTrue =
        refl
    ; physicalStoneCarrierPromoted =
        false
    ; physicalStoneCarrierPromotedIsFalse =
        refl
    ; exactBlockers =
        canonicalStoneTheoremCarrierBlockers
    ; exactBlockersAreCanonical =
        refl
    ; receiptBoundary =
        "Gate 5 Stone theorem carrier receipt consumes the canonical finite one-point Stone bundle"
        ∷ "The existing strong-continuity witness and traversal-unitary depth data are threaded in unchanged"
        ∷ "Self-adjoint generator existence is recorded at finite depth via the finite identity Hamiltonian"
        ∷ "The physical Hilbert colimit/completion obligation remains fail-closed"
        ∷ "No noncollapsed physical Stone carrier or physical traversal promotion is claimed"
        ∷ []
    }

stoneTheoremCarrierReceiptRecordsFiniteGenerator :
  finiteDepthSelfAdjointGeneratorExists
    (finiteSelfAdjointGeneratorReceipt
      canonicalStoneTheoremCarrierReceipt)
  ≡
  true
stoneTheoremCarrierReceiptRecordsFiniteGenerator =
  refl

stoneTheoremCarrierReceiptKeepsPhysicalColimitFalse :
  physicalHilbertColimitPromoted
    (physicalHilbertColimitObligation
      canonicalStoneTheoremCarrierReceipt)
  ≡
  false
stoneTheoremCarrierReceiptKeepsPhysicalColimitFalse =
  refl
