module DASHI.Physics.Closure.NSCompactGammaOffPacketWall1PairIncidenceBridge where

open import Agda.Primitive using (Level; lsuc)
open import Relation.Binary.PropositionalEquality using (_≡_)

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
--
-- The generic bridge deliberately asks for a concrete-kernel/pair-incidence
-- match.  For the repository's Wall-1 Fourier carrier this obligation is
-- already discharged definitionally by `fourierKernelIsPairIncidence`.
-- Therefore the only compact-Gamma-specific representation leaf left here is
-- the exact equality between the near derivative and the output energy of the
-- Wall-1 Biot--Savart kernel action.
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

record Wall1ExactNearRepresentationInputs
    {v : Level}
    {Vector : Set v}
    (A : AbsorptionArithmetic)
    (W : Wall1FourierShellData Vector (Scalar A))
    (L : WeightedSchurLaws
      (asWeightedKernelData (wall1PairIncidenceData W))) :
    Set (lsuc v) where
  field
    wall1ExactKernelAction :
      ExactKernelAction
        (asWeightedKernelData (wall1PairIncidenceData W))
        L

    wall1KernelInput : VectorIn L
    wall1ConcreteNearResponse : Scalar A

    wall1ConcreteNearResponseIsKernelAction :
      wall1ConcreteNearResponse ≡
      outputEnergy L
        (evaluateEntries wall1ExactKernelAction
          (wall1BiotSavartKernel W)
          wall1KernelInput)

open Wall1ExactNearRepresentationInputs public

wall1ExactNearPairIncidenceRepresentation :
  ∀ {v}
    {Vector : Set v}
    (A : AbsorptionArithmetic)
    (W : Wall1FourierShellData Vector (Scalar A))
    (L : WeightedSchurLaws
      (asWeightedKernelData (wall1PairIncidenceData W))) →
  Wall1ExactNearRepresentationInputs A W L →
  ExactNearPairIncidenceRepresentation
    A (wall1PairIncidenceData W) L
wall1ExactNearPairIncidenceRepresentation A W L I = record
  { exactKernelAction = wall1ExactKernelAction I
  ; exactKernelInput = wall1KernelInput I
  ; concreteKernel = wall1BiotSavartKernel W
  ; concreteKernelMatch = wall1ConcreteKernelMatch W
  ; concreteNearResponse = wall1ConcreteNearResponse I
  ; concreteNearResponseIsConcreteAction =
      wall1ConcreteNearResponseIsKernelAction I
  }

------------------------------------------------------------------------
-- Full Wall-1 evidence bundle.  The finite/uniform Schur realization remains
-- explicit because its row/column inequalities are the analytic theorem leaf;
-- the Fourier pair-incidence identity itself is no longer an obligation.
------------------------------------------------------------------------

record Wall1OffPacketPairIncidenceEvidence
    {v : Level}
    {Vector : Set v}
    (A : AbsorptionArithmetic)
    (W : Wall1FourierShellData Vector (Scalar A))
    (L : WeightedSchurLaws
      (asWeightedKernelData (wall1PairIncidenceData W))) :
    Set (lsuc v) where
  field
    wall1SchurRealization :
      PairIncidenceSchurRealization
        (wall1PairIncidenceData W)
        L

    wall1OrderReflexive :
      ReflexiveAbsorptionOrder A

    wall1NearRepresentation :
      Wall1ExactNearRepresentationInputs A W L

    wall1OffPacketResponse : Scalar A
    wall1FarShellTail : Scalar A

    wall1OffPacketBelowNearPlusTail :
      _≤_ A wall1OffPacketResponse
        (_+_ A
          (wall1ConcreteNearResponse wall1NearRepresentation)
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
  ; pairOrderReflexive = wall1OrderReflexive E
  ; pairNearRepresentation =
      wall1ExactNearPairIncidenceRepresentation
        A W L (wall1NearRepresentation E)
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
