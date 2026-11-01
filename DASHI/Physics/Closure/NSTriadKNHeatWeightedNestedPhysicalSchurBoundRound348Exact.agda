module DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedPhysicalSchurBoundRound348Exact where

------------------------------------------------------------------------
-- ROUND348 / BIDI: PHYSICAL F_s RESPONSE -> OLD CERTIFIED SCHUR BUDGET
--
-- The old compact-Gamma weighted-kernel bridge already uses the exact proof
-- shape needed here:
--
--   physical response <= certified kernel output
--   certified kernel output <= weighted Schur budget
--   ------------------------------------------------
--   physical response <= weighted Schur budget.
--
-- R345 supplies the first inequality through the old pair-incidence physical
-- majorization bridge.  R347 supplies the ordinary old WeightedKernelSchurCertificate.
-- This round only composes them, retaining the explicit transport between the
-- Schur order and the physical arithmetic order.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Analysis.WeightedKernelSchurTest as Weighted
import DASHI.Physics.Closure.NSCompactGammaReplenishmentAbsorption as Absorption
import DASHI.Physics.Closure.NSPairIncidenceSchurBridge as PairSchur
import DASHI.Physics.Closure.NSCompactGammaOffPacketPairIncidenceKernelBridge as OldBridge
import DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedPairIncidenceRealizationRound343Exact as R343
import DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedConcreteKernelMatchRound344Exact as R344
import DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedFiniteSchurCertificateRound346Exact as R346
import DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedSchurRealizationRound347Exact as R347
import DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedPhysicalResponseMajorizationRound345Exact as R345

nestedFsPhysicalResponseBelowSchurBudget :
  ∀ {Row Col : Set}
    (A : Absorption.AbsorptionArithmetic)
    (cutoff : Nat)
    (S : R343.NestedFsIncidenceSemantics Row Col (Absorption.Scalar A))
    (B : R346.NestedFsFiniteSchurInputs cutoff S)
    (L : Weighted.WeightedSchurLaws
      (PairSchur.asWeightedKernelData
        (R343.nestedFsPairIncidenceData cutoff S)))
    (R : PairSchur.PairIncidenceSchurRealization
      (R343.nestedFsPairIncidenceData cutoff S) L)
    (exactAction : Weighted.ExactKernelAction
      (PairSchur.asWeightedKernelData
        (R343.nestedFsPairIncidenceData cutoff S)) L)
    (input : Weighted.VectorIn L)
    (physicalFsResponse : Absorption.Scalar A)
    (physicalFsResponseBelowMajorantAction :
      Absorption._≤_ A physicalFsResponse
        (Weighted.outputEnergy L
          (Weighted.evaluateEntries exactAction
            (R344.nestedFsDeclaredMajorantKernel cutoff S)
            input)))
    (schurOrderTransport :
      {left right : Absorption.Scalar A} →
      Weighted._≤_ L left right →
      Absorption._≤_ A left right) →
  Absorption._≤_ A
    physicalFsResponse
    (Weighted._⊗_ L
      (Weighted.rowConstant L)
      (Weighted._⊗_ L
        (Weighted.columnConstant L)
        (Weighted.inputEnergy L input)))
nestedFsPhysicalResponseBelowSchurBudget
  A cutoff S B L R exactAction input physicalFsResponse physicalBelow schurTransport =
  Absorption.≤-trans A
    physicalBelowCertifiedKernel
    certifiedKernelBelowSchurBudget
  where
  M = R345.nestedFsPhysicalResponseMajorization
        A cutoff S L exactAction input physicalFsResponse physicalBelow

  physicalBelowCertifiedKernel :
    Absorption._≤_ A
      physicalFsResponse
      (Weighted.outputEnergy L (Weighted.applyKernel L input))
  physicalBelowCertifiedKernel =
    OldBridge.concreteNearResponseBelowCertifiedKernelOutput
      A (R343.nestedFsPairIncidenceData cutoff S) L M

  certificate =
    R347.nestedFsWeightedKernelSchurCertificate cutoff S B L R

  certifiedKernelBelowSchurBudget :
    Absorption._≤_ A
      (Weighted.outputEnergy L (Weighted.applyKernel L input))
      (Weighted._⊗_ L
        (Weighted.rowConstant L)
        (Weighted._⊗_ L
          (Weighted.columnConstant L)
          (Weighted.inputEnergy L input)))
  certifiedKernelBelowSchurBudget =
    schurTransport
      (Weighted.weightedKernelBound
        (PairSchur.asWeightedKernelData
          (R343.nestedFsPairIncidenceData cutoff S))
        L certificate input)

round348OldPhysicalToCertifiedKernelBridgeReused : Bool
round348OldPhysicalToCertifiedKernelBridgeReused = true

round348OldWeightedKernelBoundReused : Bool
round348OldWeightedKernelBoundReused = true

round348OrderTransportRemainsExplicit : Bool
round348OrderTransportRemainsExplicit = true

round348PhysicalFsSchurBoundClosedConditionally : Bool
round348PhysicalFsSchurBoundClosedConditionally = true

round348CotlarConsumptionClosed : Bool
round348CotlarConsumptionClosed = false

round348HeatSpacetimeIntegrationClosed : Bool
round348HeatSpacetimeIntegrationClosed = false

round348PackageAClosed : Bool
round348PackageAClosed = false

round348ClayPromotion : Bool
round348ClayPromotion = false

round348PhysicalFsSchurBoundClosedConditionallyIsTrue :
  round348PhysicalFsSchurBoundClosedConditionally ≡ true
round348PhysicalFsSchurBoundClosedConditionallyIsTrue = refl

round348PackageAClosedIsFalse : round348PackageAClosed ≡ false
round348PackageAClosedIsFalse = refl

round348ClayPromotionIsFalse : round348ClayPromotion ≡ false
round348ClayPromotionIsFalse = refl
