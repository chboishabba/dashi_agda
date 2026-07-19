module DASHI.Physics.Closure.NSCompactGammaOffPacketWeightedKernelBridge where

open import Agda.Primitive using (Level; _⊔_; lsuc)

open import DASHI.Analysis.WeightedKernelSchurTest
open import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption
open import DASHI.Physics.Closure.NSCompactGammaOffPacketSchurSplit

------------------------------------------------------------------------
-- Adapter from an exact weighted finite-kernel certificate to the near-shell
-- input expected by the compact-Gamma off-packet Schur-tail composition.
--
-- The kernel scalar is definitionally the scalar of the absorption arithmetic.
-- The representation field remains explicit: an empirical coarse shell matrix
-- cannot discharge this bridge unless the concrete near response is proved to
-- be bounded by the output energy of the exact certified kernel.
------------------------------------------------------------------------

record OffPacketWeightedKernelEvidence
    {r c : Level}
    {Row : Set r}
    {Col : Set c}
    (A : AbsorptionArithmetic)
    (K : WeightedKernelData Row Col (Scalar A))
    (L : WeightedSchurLaws K) :
    Set (lsuc (r ⊔ c)) where
  field
    certificate : WeightedKernelSchurCertificate K L
    kernelInput : VectorIn L

    offPacketResponse : Scalar A
    nearShellResponse : Scalar A
    farShellTail : Scalar A

    offPacketBelowNearPlusTail :
      _≤_ A offPacketResponse
        (_+_ A nearShellResponse farShellTail)

    concreteNearResponseRepresentedByKernel :
      _≤_ A
        nearShellResponse
        (outputEnergy L (applyKernel L kernelInput))

    schurOrderTransport :
      {left right : Scalar A} →
      _≤_ L left right →
      _≤_ A left right

open OffPacketWeightedKernelEvidence public

weightedKernelEvidenceToOffPacketSplit :
  ∀ {r c}
    {Row : Set r}
    {Col : Set c}
    (A : AbsorptionArithmetic)
    (K : WeightedKernelData Row Col (Scalar A))
    (L : WeightedSchurLaws K) →
  OffPacketWeightedKernelEvidence A K L →
  OffPacketSchurSplitInputs A
weightedKernelEvidenceToOffPacketSplit A K L E = record
  { offPacketResponse = offPacketResponse E
  ; nearShellResponse = nearShellResponse E
  ; farShellTail = farShellTail E
  ; schurWeightedBudget = certifiedBudget
  ; offPacketBelowNearPlusTail = offPacketBelowNearPlusTail E
  ; nearShellBelowSchurBudget = nearBelowCertifiedBudget
  }
  where
  certifiedBudget : Scalar A
  certifiedBudget =
    _⊗_ L
      (rowConstant L)
      (_⊗_ L
        (columnConstant L)
        (inputEnergy L (kernelInput E)))

  kernelOutputBelowCertifiedBudget :
    _≤_ A
      (outputEnergy L (applyKernel L (kernelInput E)))
      certifiedBudget
  kernelOutputBelowCertifiedBudget =
    schurOrderTransport E
      (weightedKernelBound K L (certificate E) (kernelInput E))

  nearBelowCertifiedBudget :
    _≤_ A
      (nearShellResponse E)
      certifiedBudget
  nearBelowCertifiedBudget =
    ≤-trans A
      (concreteNearResponseRepresentedByKernel E)
      kernelOutputBelowCertifiedBudget
