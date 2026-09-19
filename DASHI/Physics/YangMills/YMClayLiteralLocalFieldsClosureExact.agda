{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayLiteralLocalFieldsClosureExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayTopDownFiveTheoremClosureExact as Five
import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound78TopDownThreeAnalyticFrontierExact as R78
import DASHI.Physics.YangMills.YangMillsClayStressOPERequirementBoundaryExact as Stress

------------------------------------------------------------------------
-- ROUND78-C LITERAL LOCAL-FIELD CLOSURE
--
-- D1/D2/D3 are producer-side mathematics for the literal stress/OPE evidence.
-- The Clay-facing C endpoint itself contains only:
--
--   * gauge-invariant local observable family,
--   * curvature-operator correspondence/locality,
--   * short-distance AF on the same Schwinger family,
--   * literal stress/OPE evidence.
--
-- This module proves that those exact data construct the existing
-- ContinuumLocalFieldOPEStressWard / Round78-C endpoint.  It removes any need
-- for a second bespoke "Level-2 conclusion" type.
------------------------------------------------------------------------

record LiteralLocalFieldClosureInputs
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S) : Set₁ where
  field
    gaugeInvariantLocalObservable : ∀ G position →
      Top.IsGaugeInvariantObservable S (Top.localObservable Y G position)
      × Top.IsLocalObservable S (Top.localObservable Y G position) position

    curvatureOperatorCorrespondence : ∀ G →
      Top.CurvatureOperatorCorrespondence S G (Top.curvatureOperator Y G)

    curvatureOperatorsGaugeInvariant : ∀ G polynomial →
      Top.IsGaugeInvariantLocalOperator S (Top.curvatureOperator Y G polynomial)

    curvatureOperatorsLocal : ∀ G polynomial position →
      Top.IsLocalOperator S (Top.curvatureOperator Y G polynomial) position

    shortDistanceAsymptoticFreedom : ∀ G →
      Top.HasShortDistanceAsymptoticFreedom S G (Top.schwinger Y G)

    literalStressOPE : Stress.LiteralClayStressOPEEvidence Y

open LiteralLocalFieldClosureInputs public

literalLocalFieldClosureBuildsFiveT4 :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  LiteralLocalFieldClosureInputs Y →
  Five.ContinuumLocalFieldOPEStressWard Y
literalLocalFieldClosureBuildsFiveT4 inputs = record
  { Five.ContinuumLocalFieldOPEStressWard.gaugeInvariantLocalObservable =
      gaugeInvariantLocalObservable inputs
  ; Five.ContinuumLocalFieldOPEStressWard.curvatureOperatorCorrespondence =
      curvatureOperatorCorrespondence inputs
  ; Five.ContinuumLocalFieldOPEStressWard.curvatureOperatorsGaugeInvariant =
      curvatureOperatorsGaugeInvariant inputs
  ; Five.ContinuumLocalFieldOPEStressWard.curvatureOperatorsLocal =
      curvatureOperatorsLocal inputs
  ; Five.ContinuumLocalFieldOPEStressWard.shortDistanceAsymptoticFreedom =
      shortDistanceAsymptoticFreedom inputs
  ; Five.ContinuumLocalFieldOPEStressWard.stressTensorAndOPE =
      Stress.stressAndOPE (literalStressOPE inputs)
  ; Five.ContinuumLocalFieldOPEStressWard.physicalOPECoefficient =
      Stress.physicalOPECoefficient (literalStressOPE inputs)
  ; Five.ContinuumLocalFieldOPEStressWard.physicalOPERemainder =
      Stress.physicalOPERemainder (literalStressOPE inputs)
  }

literalLocalFieldClosureBuildsRound78C :
  ∀ {C S} {Y : Top.LiteralYangMillsConstruction C S} →
  LiteralLocalFieldClosureInputs Y →
  R78.SameFamilyLocalFieldsOPEStressWard Y
literalLocalFieldClosureBuildsRound78C inputs = record
  { R78.SameFamilyLocalFieldsOPEStressWard.localFields =
      literalLocalFieldClosureBuildsFiveT4 inputs
  }

------------------------------------------------------------------------
-- Exact classification.
------------------------------------------------------------------------

secondLiteralStressOPEEndpointRequired : Bool
secondLiteralStressOPEEndpointRequired = false

secondLiteralStressOPEEndpointRequiredIsFalse :
  secondLiteralStressOPEEndpointRequired ≡ false
secondLiteralStressOPEEndpointRequiredIsFalse = refl

stressChargeEqualsOSHamiltonianRequiredForRound78C : Bool
stressChargeEqualsOSHamiltonianRequiredForRound78C = false

stressChargeEqualsOSHamiltonianRequiredForRound78CIsFalse :
  stressChargeEqualsOSHamiltonianRequiredForRound78C ≡ false
stressChargeEqualsOSHamiltonianRequiredForRound78CIsFalse = refl

literalLocalFieldsClosureCompilerLevel : ProofLevel
literalLocalFieldsClosureCompilerLevel = machineChecked

physicalLiteralLocalFieldsInputsLevel : ProofLevel
physicalLiteralLocalFieldsInputsLevel = conditional

clayPromotion : Bool
clayPromotion = false

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
