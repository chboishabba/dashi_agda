module DASHI.Physics.YangMills.BalabanMarkedWalkChargingCutRound354Exact where

------------------------------------------------------------------------
-- ROUND354 / DO NOT HIDE THE MARKED GEOMETRY INSIDE SUMMABILITY
--
-- R353 descends H_stab^source to the existing marked-walk compiler.  That
-- compiler's `markedWalkSummability` field still bundles two different jobs:
--
--   H_charge : each raw CMP99-marked surviving-walk majorant is converted to a
--              charged majorant which retains either discrepancy distance or
--              enough positive localisation/tree length;
--
--   H_sum    : the charged family is summable by the CMP116 localisation/tree
--              estimates.
--
-- CMP116 (1.24)--(1.29) supplies the ordinary tree/localisation summability
-- mechanism.  The additional marked charging is not obtained merely by citing
-- that source sum.  The older BalabanMarkedPolarisationResummation owner says
-- explicitly that the block-scale `markedDistanceOrLargeLocalisation` geometry
-- is the remaining CMP99/109 lemma.
--
-- This module proves the generic compiler only:
--
--   pointwise raw <= charged
--   + sum charged <= envelope
--   --------------------------------
--     sum raw <= envelope.
--
-- Thus H_charge and H_sum remain distinct physical/source payments.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; _≤ℝ_; ≤ℝ-trans)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation as Resum

record MarkedWalkChargingData (Walk : Set) : Set₁ where
  field
    survivingWalks : List Walk
    rawMarkedMajorant chargedMajorant : Walk → ℝ
    envelope : ℝ

    -- H_charge: source/block geometry, not generic summation algebra.
    rawMarkedBelowCharged : ∀ walk →
      rawMarkedMajorant walk ≤ℝ chargedMajorant walk

    -- H_sum: once the positive residual tree/localisation rate is retained,
    -- CMP116-style summation pays the charged family.
    chargedSummability :
      Resum.sumℝ chargedMajorant survivingWalks ≤ℝ envelope

open MarkedWalkChargingData public

rawMarkedSummabilityFromCharging :
  ∀ {Walk}
    (dataSet : MarkedWalkChargingData Walk) →
  Resum.sumℝ (rawMarkedMajorant dataSet) (survivingWalks dataSet)
    ≤ℝ envelope dataSet
rawMarkedSummabilityFromCharging dataSet =
  ≤ℝ-trans
    (Resum.sumℝ-mono
      (survivingWalks dataSet)
      (rawMarkedBelowCharged dataSet))
    (chargedSummability dataSet)

------------------------------------------------------------------------
-- Pareto / source accounting.
------------------------------------------------------------------------

-- First genuinely new analytic geometry in this producer family.
markedDistanceOrLargeLocalisationChargeLevel : ProofLevel
markedDistanceOrLargeLocalisationChargeLevel = conditional

-- The source contains the ordinary CMP116 summation mechanism, but its exact
-- same-carrier instantiation after H_charge remains a proof-bearing payment.
chargedCMP116SummabilityInstantiationLevel : ProofLevel
chargedCMP116SummabilityInstantiationLevel = conditional

chargingThenSummationCompilerLevel : ProofLevel
chargingThenSummationCompilerLevel = machineChecked

cmp116OrdinarySummabilityAlonePaysMarkedCharge : Bool
cmp116OrdinarySummabilityAlonePaysMarkedCharge = false

cmp116OrdinarySummabilityAlonePaysMarkedChargeIsFalse :
  cmp116OrdinarySummabilityAlonePaysMarkedCharge ≡ false
cmp116OrdinarySummabilityAlonePaysMarkedChargeIsFalse = refl

markedChargeAndSummabilityAreSamePayment : Bool
markedChargeAndSummabilityAreSamePayment = false

markedChargeAndSummabilityAreSamePaymentIsFalse :
  markedChargeAndSummabilityAreSamePayment ≡ false
markedChargeAndSummabilityAreSamePaymentIsFalse = refl

freshFiniteSumTheoremRequired : Bool
freshFiniteSumTheoremRequired = false

freshFiniteSumTheoremRequiredIsFalse :
  freshFiniteSumTheoremRequired ≡ false
freshFiniteSumTheoremRequiredIsFalse = refl

record Round354Boundary : Set where
  constructor round354-boundary
  field
    markedChargingIsLiveAnalyticLeaf : Bool
    markedChargingIsLiveAnalyticLeafIsTrue :
      markedChargingIsLiveAnalyticLeaf ≡ true

    chargedSummabilityStillNeedsSameCarrierPayment : Bool
    chargedSummabilityStillNeedsSameCarrierPaymentIsTrue :
      chargedSummabilityStillNeedsSameCarrierPayment ≡ true

    finiteSummationCompilerAlreadyOwned : Bool
    finiteSummationCompilerAlreadyOwnedIsTrue :
      finiteSummationCompilerAlreadyOwned ≡ true

canonicalRound354Boundary : Round354Boundary
canonicalRound354Boundary =
  round354-boundary
    true refl
    true refl
    true refl

round354FrontierRefinementLevel : ProofLevel
round354FrontierRefinementLevel = machineChecked

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
