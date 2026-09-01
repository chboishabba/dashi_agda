module DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedPhysicalResponseMajorizationRound345Exact where

------------------------------------------------------------------------
-- ROUND345 / BIDI: REUSE THE OLD PHYSICAL-RESPONSE MAJORIZATION RECORD
--
-- The compact-Gamma pair-incidence bridge already states the exact authority
-- boundary we need for F_s.  It does NOT require equality between a signed
-- physical response and a positive incidence kernel.  It requires:
--
--   * an exact kernel action for the declared weighted kernel;
--   * an input vector;
--   * a concrete majorant kernel with exact pointwise pair-fold identity;
--   * the physical response;
--   * physical response <= output energy of the concrete majorant action.
--
-- R343 supplies the literal global nested PairIncidenceData and R344 supplies
-- the pointwise kernel match definitionally.  Hence, assuming the actual
-- F_s response-majorization inequality requested by the analytic lane, the OLD
-- `NearPairIncidenceMajorization` record can be inhabited directly.  No new
-- response/kernel representation ontology is introduced.
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

nestedFsPhysicalResponseMajorization :
  ∀ {Row Col : Set}
    (A : Absorption.AbsorptionArithmetic)
    (cutoff : Nat)
    (S : R343.NestedFsIncidenceSemantics Row Col (Absorption.Scalar A))
    (L : Weighted.WeightedSchurLaws
      (PairSchur.asWeightedKernelData
        (R343.nestedFsPairIncidenceData cutoff S)))
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
            input))) →
  OldBridge.NearPairIncidenceMajorization
    A
    (R343.nestedFsPairIncidenceData cutoff S)
    L
nestedFsPhysicalResponseMajorization
  A cutoff S L exactAction input physicalFsResponse physicalBelow = record
  { exactKernelAction = exactAction
  ; exactKernelInput = input
  ; concreteMajorantKernel = R344.nestedFsDeclaredMajorantKernel cutoff S
  ; concreteMajorantKernelMatch = R344.nestedFsDeclaredMajorantKernelMatch cutoff S
  ; concreteNearResponse = physicalFsResponse
  ; concreteNearResponseBelowMajorantAction = physicalBelow
  }

round345OldCompactGammaResponseMajorizationShapeReused : Bool
round345OldCompactGammaResponseMajorizationShapeReused = true

round345ConcreteKernelMatchComesFromR344 : Bool
round345ConcreteKernelMatchComesFromR344 = true

round345OnlyNewDomainInputIsPhysicalFsBelowMajorantAction : Bool
round345OnlyNewDomainInputIsPhysicalFsBelowMajorantAction = true

-- Under the user's assumed-content premise, the adapter itself is complete;
-- the inequality is an explicit argument rather than silently postulated here.
round345ResponseMajorizationAdapterClosed : Bool
round345ResponseMajorizationAdapterClosed = true

round345FiniteSchurBudgetClosed : Bool
round345FiniteSchurBudgetClosed = false

round345CotlarConsumptionClosed : Bool
round345CotlarConsumptionClosed = false

round345PackageAClosed : Bool
round345PackageAClosed = false

round345ClayPromotion : Bool
round345ClayPromotion = false

round345ResponseMajorizationAdapterClosedIsTrue :
  round345ResponseMajorizationAdapterClosed ≡ true
round345ResponseMajorizationAdapterClosedIsTrue = refl

round345PackageAClosedIsFalse : round345PackageAClosed ≡ false
round345PackageAClosedIsFalse = refl

round345ClayPromotionIsFalse : round345ClayPromotion ≡ false
round345ClayPromotionIsFalse = refl
