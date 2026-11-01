module DASHI.Reasoning.LogicalPromotionExperimentBackpropExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF
import DASHI.Reasoning.PredicateNormalFormLogicalCalculusExact as Logic
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone
import DASHI.Reasoning.BlockedImplicationExperimentBackpropExact as Backprop

------------------------------------------------------------------------
-- LOGICAL CONSEQUENCE / EMPIRICAL PROMOTION -> EXPERIMENT BACKPROP
--
-- The logical calculus classifies amplification separately from deduction. If
-- a requested downstream PNF is an empirical strengthening, this bridge turns
-- that classification into the already-existing blocked-claim design problem.
------------------------------------------------------------------------

record EmpiricalPromotionDemand
    (proposal : PNF.ProposedPromotion) : Set₁ where
  constructor empiricalPromotionDemand
  field
    authorityNeedsEvidence :
      Logic.promotionAuthority (PNF.delta proposal)
      ≡ Logic.requiresAdditionalEmpiricalEvidence
    requestedUseReference : String
    logicalClosureReference : String
    empiricalGapReference : String

open EmpiricalPromotionDemand public

record PromotionBackpropBridge
    {proposal : PNF.ProposedPromotion}
    (demand : EmpiricalPromotionDemand proposal) : Set₁ where
  constructor promotionBackpropBridge
  field
    target : Backprop.BlockedImplicationTarget
    targetAssertionIsRequestedDownstream :
      Cone.assertion (Backprop.desiredNode target)
      ≡ PNF.downstream proposal
    requirement : Backprop.MissingDesignRequirement target
    promotionDeltaReference : String
    obligationCorrespondenceReference : String
    designSlotCorrespondenceReference : String
    reauditingReference : String

open PromotionBackpropBridge public

------------------------------------------------------------------------
-- The generic costed candidate machinery is inherited unchanged. A logical
-- promotion demand therefore does not manufacture an experiment, a gain score,
-- or empirical evidence; it only identifies which backprop problem must be
-- solved.
------------------------------------------------------------------------

record PromotionExperimentMenu
    {Hidden : Set}
    {proposal : PNF.ProposedPromotion}
    {demand : EmpiricalPromotionDemand proposal}
    (bridge : PromotionBackpropBridge demand) : Set₂ where
  constructor promotionExperimentMenu
  field
    menu :
      Backprop.BackpropExperimentMenu
        {Hidden}
        (target bridge)
        (requirement bridge)
    menuReference : String
    calibrationStillRequiredReference : String

open PromotionExperimentMenu public

------------------------------------------------------------------------
-- Exact classification regressions.
------------------------------------------------------------------------

causalStrengtheningRoutesToEmpiricalBackprop :
  Logic.promotionAuthority PNF.strengthensCausalForce
  ≡ Logic.requiresAdditionalEmpiricalEvidence
causalStrengtheningRoutesToEmpiricalBackprop = refl

populationWideningRoutesToEmpiricalBackprop :
  Logic.promotionAuthority PNF.widensPopulation
  ≡ Logic.requiresAdditionalEmpiricalEvidence
populationWideningRoutesToEmpiricalBackprop = refl

quantifierStrengtheningRoutesToEmpiricalBackprop :
  Logic.promotionAuthority PNF.strengthensQuantifier
  ≡ Logic.requiresAdditionalEmpiricalEvidence
quantifierStrengtheningRoutesToEmpiricalBackprop = refl

uncertaintyDroppingRoutesToEmpiricalBackprop :
  Logic.promotionAuthority PNF.dropsUncertainty
  ≡ Logic.requiresAdditionalEmpiricalEvidence
uncertaintyDroppingRoutesToEmpiricalBackprop = refl

record LogicalPromotionBackpropBoundary : Set where
  constructor logicalPromotionBackpropBoundary
  field
    logicalDerivationCanManufactureMissingExperiment : Bool
    logicalDerivationCanManufactureMissingExperimentIsFalse :
      logicalDerivationCanManufactureMissingExperiment ≡ false
    empiricalPromotionCanNameExactBlockedDesignProblem : Bool
    empiricalPromotionCanNameExactBlockedDesignProblemIsTrue :
      empiricalPromotionCanNameExactBlockedDesignProblem ≡ true
    causalStrengtheningUsesExperimentBackprop : Bool
    causalStrengtheningUsesExperimentBackpropIsTrue :
      causalStrengtheningUsesExperimentBackprop ≡ true
    transportWideningUsesExperimentBackprop : Bool
    transportWideningUsesExperimentBackpropIsTrue :
      transportWideningUsesExperimentBackprop ≡ true
    selectedExperimentStillRequiresReaudit : Bool
    selectedExperimentStillRequiresReauditIsTrue :
      selectedExperimentStillRequiresReaudit ≡ true

canonicalLogicalPromotionBackpropBoundary : LogicalPromotionBackpropBoundary
canonicalLogicalPromotionBackpropBoundary =
  logicalPromotionBackpropBoundary false refl true refl true refl true refl true refl
