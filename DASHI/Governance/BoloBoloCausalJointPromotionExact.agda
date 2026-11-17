module DASHI.Governance.BoloBoloCausalJointPromotionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.GenericReceipt as GenericReceipt
import DASHI.Biology.CausalEffectEstimandExact as Estimand
import DASHI.Governance.BoloBoloFederationCostComparisonExact as Comparison
import DASHI.Governance.BoloBoloCausalIdentificationMaxCutExact as Causal
import DASHI.Governance.BoloBoloLongitudinalNonDominationExact as Joint

------------------------------------------------------------------------
-- CAUSAL JOINT PROMOTION MAX-CUT
--
-- DASHI methodology only.
--
-- Repeated validated comparative performance != identified causal effect.
-- A same-target non-domination receipt != evidence that the nested design
-- CAUSED the non-domination outcome.  These are distinct promotion questions.
------------------------------------------------------------------------

record CausallyIdentifiedJointCoordinationAdvantage
    (threshold : Nat)
    (model : Comparison.CounterfactualCoordinationCostModel) : Set₂ where
  constructor causally-identified-joint-coordination-advantage
  field
    jointState : Joint.JointLongitudinalNonDominationCertificate threshold model
    coordinationIdentification :
      Causal.IdentifiedBoloCoordinationCausalBridge
        Causal.canonicalBoloCoordinationCausalEstimandDemand

    JointTargetMatchesCoordinationEstimand : Set
    jointTargetMatchesCoordinationEstimandWitness :
      JointTargetMatchesCoordinationEstimand

open CausallyIdentifiedJointCoordinationAdvantage public

------------------------------------------------------------------------
-- Separate non-domination causal question.
--
-- This shares population/intervention/comparator/horizon with the coordination
-- question but changes the outcome and causal-question identity.  Therefore a
-- coordination identification receipt cannot be reused by name or scalar
-- agreement to identify the realised-control/non-domination effect.
------------------------------------------------------------------------

canonicalBoloNonDominationCausalEstimandDemand :
  Causal.BoloCoordinationCausalEstimandDemand
canonicalBoloNonDominationCausalEstimandDemand =
  Causal.bolo-coordination-causal-estimand-demand
    Estimand.trajectoryEffect
    "predeclared target population / matched governance units"
    "nested kana-bolo-tega-like governance arm"
    "flat globally coupled consensus arm"
    "predeclared realised-control/non-domination trajectory including agenda, delegation, contestability, reopening and unilateral-authority coordinates"
    "predeclared longitudinal follow-up horizon"
    "causal-question:bolo-flat-vs-nested:realised-nondomination-effect"
    true
    true
    false

record CausallyIdentifiedNonDominationEffect
    (threshold : Nat)
    (model : Comparison.CounterfactualCoordinationCostModel) : Set₂ where
  constructor causally-identified-nondomination-effect
  field
    jointState : Joint.JointLongitudinalNonDominationCertificate threshold model
    nonDominationIdentification :
      Causal.IdentifiedBoloCoordinationCausalBridge
        canonicalBoloNonDominationCausalEstimandDemand

    EffectEstimateBoundToSameEstimand : Set
    effectEstimateBoundToSameEstimandWitness :
      EffectEstimateBoundToSameEstimand

    EffectEstimateSupportsNonDominationImprovement : Set
    effectEstimateSupportsNonDominationImprovementWitness :
      EffectEstimateSupportsNonDominationImprovement

    RealizedControlOutcomeAuditMatchesEstimand : Set
    realizedControlOutcomeAuditMatchesEstimandWitness :
      RealizedControlOutcomeAuditMatchesEstimand

open CausallyIdentifiedNonDominationEffect public

------------------------------------------------------------------------
-- Strongest current joint causal target.
--
-- This does NOT mean political legitimacy, ecological viability or universal
-- political superiority. It is only the conjunction of two separately paid
-- causal claims on one target: coordination performance and realised-control /
-- non-domination outcome.
------------------------------------------------------------------------

record CausallyIdentifiedCoordinationAndNonDominationAdvantage
    (threshold : Nat)
    (model : Comparison.CounterfactualCoordinationCostModel) : Set₂ where
  constructor causally-identified-coordination-and-nondomination-advantage
  field
    coordinationAdvantage :
      CausallyIdentifiedJointCoordinationAdvantage threshold model
    nonDominationEffect :
      CausallyIdentifiedNonDominationEffect threshold model

    SameTargetAcrossCausalClaims : Set
    sameTargetAcrossCausalClaimsWitness : SameTargetAcrossCausalClaims

open CausallyIdentifiedCoordinationAndNonDominationAdvantage public

------------------------------------------------------------------------
-- Promotion boundary.
------------------------------------------------------------------------

record CausalJointPromotionBoundary : Set where
  constructor causal-joint-promotion-boundary
  field
    repeatedValidatedAssociationAutomaticallyIdentifiesCausalEffect : Bool
    coordinationCausalIdentificationRequired : Bool
    jointStateCertificateAutomaticallyProvesNonDominationCausalEffect : Bool
    nonDominationCausalEffectRequiresSeparateIdentification : Bool
    coordinationIdentificationAutomaticallyIdentifiesNonDominationEffect : Bool
    identificationGateAutomaticallyProvesEffectDirection : Bool
    nonDominationEffectEstimateMustMatchItsEstimand : Bool
    realisedControlOutcomeAuditMustMatchNonDominationEstimand : Bool
    sameTargetAcrossCausalClaimsRequired : Bool
    dualCausalAdvantageCreatesPoliticalLegitimacy : Bool
    dualCausalAdvantageProvesEcologicalOrResourceViability : Bool
    dualCausalAdvantageEstablishesUniversalPoliticalSuperiority : Bool

open CausalJointPromotionBoundary public

canonicalCausalJointPromotionBoundary : CausalJointPromotionBoundary
canonicalCausalJointPromotionBoundary =
  causal-joint-promotion-boundary
    false
    true
    false
    true
    false
    false
    true
    true
    true
    false
    false
    false

canonicalBoloCausalJointPromotionReceipt : GenericReceipt.GenericReceipt
canonicalBoloCausalJointPromotionReceipt =
  GenericReceipt.mkNonPromotingReceipt
    "bolo'bolo causal joint coordination/non-domination promotion gate"
    "DASHI.Governance.BoloBoloCausalJointPromotionExact"
    "CausallyIdentifiedJointCoordinationAdvantage / CausallyIdentifiedNonDominationEffect / CausallyIdentifiedCoordinationAndNonDominationAdvantage"
    "closes the promotion gap between repeated validated comparative observations and causal claims: coordination requires the existing target-matched causal-estimand/identification bridge, while any claim that nested governance causes better realised non-domination requires a distinct outcome-specific estimand, identification receipt, effect-direction witness and realised-control outcome audit on the same target"
    "prospective validation and repeated association do not identify causation; coordination identification does not identify non-domination by structural similarity; an identification family does not prove effect direction; even two same-target causal advantages establish neither political legitimacy, ecological/resource viability nor universal political superiority"
    "agda -i . DASHI/Governance/BoloBoloCausalJointPromotionRegression.agda"
