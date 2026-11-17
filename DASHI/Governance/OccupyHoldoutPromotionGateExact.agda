module DASHI.Governance.OccupyHoldoutPromotionGateExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Governance.OccupyDevelopmentDiagnosticsExact as Diagnostics

------------------------------------------------------------------------
-- HOLDOUT PROMOTION GATE.
--
-- The prospective holdout is a scarce validation resource. Development-only
-- diagnostics are evaluated first. Since no nontrivial lexical duration model
-- beats the intercept baseline under the frozen LOO-MAE gate, no model is
-- promoted and the holdout remains unread.
------------------------------------------------------------------------

record HoldoutPromotionBoundary : Set where
  constructor holdoutPromotionBoundary
  field
    developmentGateEvaluatedBeforeHoldout : Bool
    nontrivialModelMustBeatInterceptBaseline : Bool
    failedDevelopmentGateBlocksHoldoutConsumption : Bool
    protectedHoldoutRemainsUnread : Bool
    durationModelPromotedToProspectiveEvaluation : Bool
    coordinationBurdenEffectPromoted : Bool
    holdoutMayBeOpenedForModelSelection : Bool
    futureModelRequiresFreshDevelopmentJustification : Bool

open HoldoutPromotionBoundary public

canonicalHoldoutPromotionBoundary : HoldoutPromotionBoundary
canonicalHoldoutPromotionBoundary =
  holdoutPromotionBoundary true true true true false false false true

canonicalHoldoutPromotionReceipt : GenericReceipt.GenericReceipt
canonicalHoldoutPromotionReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "Occupy prospective-holdout promotion gate"
    "DASHI.Governance.OccupyHoldoutPromotionGateExact"
    "canonicalHoldoutPromotionBoundary"
    "freezes the rule that development-only performance must justify prospective evaluation before protected records are opened; the current lexical duration candidates all fail to beat the intercept-only development baseline"
    "the seven protected records therefore remain unread, no duration model is promoted to prospective evaluation, no coordination-burden effect is promoted, and future holdout use requires a newly justified development model under the already frozen source/provenance rules"
    "agda -i . DASHI/Governance/OccupyHoldoutPromotionGateRegression.agda"
