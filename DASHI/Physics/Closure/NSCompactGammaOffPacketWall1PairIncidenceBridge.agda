module DASHI.Physics.Closure.NSCompactGammaOffPacketWall1PairIncidenceBridge where

open import Agda.Primitive using (Level; lzero; _⊔_; lsuc)

open import DASHI.Analysis.WeightedKernelSchurTest
open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaOffPacketSchurSplit
open import DASHI.Physics.Closure.NSPairIncidenceKernel
open import DASHI.Physics.Closure.NSFourierBiotSavartTriadKernel
open import DASHI.Physics.Closure.NSWall1FourierShellInstance
open import DASHI.Physics.Closure.NSPairIncidenceSchurBridge
open import DASHI.Physics.Closure.NSCompactGammaOffPacketPairIncidenceKernelBridge

------------------------------------------------------------------------
-- Wall-1 specialization of the compact-Gamma pair-incidence bridge.
------------------------------------------------------------------------

wall1ConcreteKernelMatch :
  ∀ {v s}
    {Vector : Set v}
    {Scalar : Set s}
    (W : Wall1FourierShellData Vector Scalar) →
  ConcreteBiotSavartKernelMatch
    (wall1PairIncidenceData W)
    (wall1BiotSavartKernel W)
wall1ConcreteKernelMatch W =
  fourierKernelIsPairIncidence (wall1TransferData W)

record Wall1NearMajorizationInputs
    {v : Level}
    {Vector : Set v}
    (A : AbsorptionArithmetic)
    (W : Wall1FourierShellData Vector (Scalar A))
    (L : WeightedSchurLaws
      (asWeightedKernelData (wall1PairIncidenceData W))) :
    Set (lsuc (v ⊔ lsuc lzero)) where
  field
    wall1ExactKernelAction :
      ExactKernelAction
        (asWeightedKernelData (wall1PairIncidenceData W))
        L

    wall1KernelInput : VectorIn L
    wall1ConcreteNearResponse : Scalar A

    wall1ConcreteNearResponseBelowKernelAction :
      _≤_ A wall1ConcreteNearResponse
        (outputEnergy L
          (evaluateEntries wall1ExactKernelAction
            (wall1BiotSavartKernel W)
            wall1KernelInput))

open Wall1NearMajorizationInputs public

wall1NearPairIncidenceMajorization :
  ∀ {v}
    {Vector : Set v}
    (A : AbsorptionArithmetic)
    (W : Wall1FourierShellData Vector (Scalar A))
    (L : WeightedSchurLaws
      (asWeightedKernelData (wall1PairIncidenceData W))) →
  Wall1NearMajorizationInputs A W L →
  NearPairIncidenceMajorization
    A (wall1PairIncidenceData W) L
wall1NearPairIncidenceMajorization A W L I = record
  { exactKernelAction = wall1ExactKernelAction I
  ; exactKernelInput = wall1KernelInput I
  ; concreteMajorantKernel = wall1BiotSavartKernel W
  ; concreteMajorantKernelMatch = wall1ConcreteKernelMatch W
  ; concreteNearResponse = wall1ConcreteNearResponse I
  ; concreteNearResponseBelowMajorantAction =
      wall1ConcreteNearResponseBelowKernelAction I
  }

------------------------------------------------------------------------
-- Full Wall-1 evidence bundle.  `Scalar A : Set₁`, so a Schur realization over
-- it lives in Set₂ even when the vector carrier itself is level zero.  The old
-- `Set (lsuc v)` annotation hid that level and failed under the pinned checker.
------------------------------------------------------------------------

record Wall1OffPacketPairIncidenceEvidence
    {v : Level}
    {Vector : Set v}
    (A : AbsorptionArithmetic)
    (W : Wall1FourierShellData Vector (Scalar A))
    (L : WeightedSchurLaws
      (asWeightedKernelData (wall1PairIncidenceData W))) :
    Set (lsuc (v ⊔ lsuc lzero)) where
  field
    wall1SchurRealization :
      PairIncidenceSchurRealization
        (wall1PairIncidenceData W)
        L

    wall1NearMajorization :
      Wall1NearMajorizationInputs A W L

    wall1OffPacketResponse : Scalar A
    wall1FarShellTail : Scalar A

    wall1OffPacketBelowNearPlusTail :
      _≤_ A wall1OffPacketResponse
        (_+_ A
          (wall1ConcreteNearResponse wall1NearMajorization)
          wall1FarShellTail)

    wall1SchurOrderTransport :
      {left right : Scalar A} →
      _≤_ L left right →
      _≤_ A left right

open Wall1OffPacketPairIncidenceEvidence public

wall1EvidenceToPairIncidenceEvidence :
  ∀ {v}
    {Vector : Set v}
    (A : AbsorptionArithmetic)
    (W : Wall1FourierShellData Vector (Scalar A))
    (L : WeightedSchurLaws
      (asWeightedKernelData (wall1PairIncidenceData W))) →
  Wall1OffPacketPairIncidenceEvidence A W L →
  OffPacketPairIncidenceEvidence
    A (wall1PairIncidenceData W) L
wall1EvidenceToPairIncidenceEvidence A W L E = record
  { schurRealization = wall1SchurRealization E
  ; pairNearMajorization =
      wall1NearPairIncidenceMajorization
        A W L (wall1NearMajorization E)
  ; pairOffPacketResponse = wall1OffPacketResponse E
  ; pairFarShellTail = wall1FarShellTail E
  ; pairOffPacketBelowNearPlusTail =
      wall1OffPacketBelowNearPlusTail E
  ; pairSchurOrderTransport =
      wall1SchurOrderTransport E
  }

wall1EvidenceToOffPacketSplit :
  ∀ {v}
    {Vector : Set v}
    (A : AbsorptionArithmetic)
    (W : Wall1FourierShellData Vector (Scalar A))
    (L : WeightedSchurLaws
      (asWeightedKernelData (wall1PairIncidenceData W))) →
  Wall1OffPacketPairIncidenceEvidence A W L →
  OffPacketSchurSplitInputs A
wall1EvidenceToOffPacketSplit A W L E =
  pairIncidenceEvidenceToOffPacketSplit
    A (wall1PairIncidenceData W) L
    (wall1EvidenceToPairIncidenceEvidence A W L E)
