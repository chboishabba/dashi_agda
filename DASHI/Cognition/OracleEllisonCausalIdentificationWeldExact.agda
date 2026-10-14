module DASHI.Cognition.OracleEllisonCausalIdentificationWeldExact where

------------------------------------------------------------------------
-- CAUSAL-IDENTIFICATION WELD
--
-- Relationship, chronology, deployment and network evidence may motivate a
-- causal question, but do not by themselves identify a causal effect.  A
-- promotion must name an exact estimand and separately carry an admissible
-- identification-family gate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Biology.CausalEffectEstimandExact as Estimand
import DASHI.Biology.CausalIdentificationFamiliesExact as Identification

------------------------------------------------------------------------
-- Literal reuse of merged causal boundaries.
------------------------------------------------------------------------

identificationAndEstimandRemainSeparate :
  Estimand.CausalEffectEstimandBoundary.identificationAndEstimandAreSeparate
    Estimand.canonicalCausalEffectEstimandBoundary
  ≡ true
identificationAndEstimandRemainSeparate = refl

longitudinalOrderDoesNotIdentifyCause :
  Identification.CausalIdentificationFamiliesBoundary.longitudinalAndCausationRemainDistinct
    Identification.canonicalCausalIdentificationFamiliesBoundary
  ≡ true
longitudinalOrderDoesNotIdentifyCause = refl

familyReceiptDoesNotAutomaticallyProveEffect :
  Identification.CausalIdentificationFamiliesBoundary.familyReceiptAutomaticallyProvesCausalEffect
    Identification.canonicalCausalIdentificationFamiliesBoundary
  ≡ false
familyReceiptDoesNotAutomaticallyProveEffect = refl

------------------------------------------------------------------------
-- Case-specific causal questions.
------------------------------------------------------------------------

data CausalPromotionTarget : Set where
  ellisonNetanyahuRelationshipToPolicyInfluence : CausalPromotionTarget
  oracleDeploymentToSovereignControl : CausalPromotionTarget
  threatMaintenanceToPoliticalSurvival : CausalPromotionTarget

record CausalPromotionDemand : Set where
  constructor causal-promotion-demand
  field
    target : CausalPromotionTarget
    demandedKind : Estimand.CausalEstimandKind
    populationReference : String
    interventionReference : String
    comparatorReference : String
    outcomeReference : String
    horizonReference : String
    demandReference : String

open CausalPromotionDemand public

ellisonNetanyahuPolicyInfluenceDemand : CausalPromotionDemand
ellisonNetanyahuPolicyInfluenceDemand =
  causal-promotion-demand
    ellisonNetanyahuRelationshipToPolicyInfluence
    Estimand.trajectoryEffect
    "Israeli policy / institutional decision process under a declared scope"
    "specified Ellison-Netanyahu relationship/contact exposure"
    "declared comparator without that specified exposure"
    "specified policy or institutional outcome"
    "declared policy-decision horizon"
    "relationship evidence motivates this causal question but does not identify it"

oracleSovereignControlDemand : CausalPromotionDemand
oracleSovereignControlDemand =
  causal-promotion-demand
    oracleDeploymentToSovereignControl
    Estimand.controlledDirectEffect
    "specified Israeli security-system deployment and authority context"
    "specified Oracle capability/deployment intervention"
    "declared alternative capability/deployment comparator"
    "specified sovereign architecture/control outcome"
    "declared operational/governance horizon"
    "L2 deployment does not itself identify an L3 causal-control effect"

netanyahuPoliticalSurvivalDemand : CausalPromotionDemand
netanyahuPoliticalSurvivalDemand =
  causal-promotion-demand
    threatMaintenanceToPoliticalSurvival
    Estimand.trajectoryEffect
    "defined political tenure / electoral / coalition context"
    "specified security-threat-maintenance policy exposure"
    "declared counterfactual policy comparator"
    "specified political-survival trajectory outcome"
    "declared political horizon"
    "chronology and incentives do not identify the claimed survival effect"

------------------------------------------------------------------------
-- What would count as a paid causal promotion.
--
-- The repository's generic CausalEffectEstimand supplies population,
-- intervention, comparator, outcome and horizon internally.  We additionally
-- require its declared kind to equal the case demand and a separately admitted
-- identification-family evidence gate.  No inhabitant is fabricated here.
------------------------------------------------------------------------

record PaidCausalPromotion (demand : CausalPromotionDemand) : Set₂ where
  constructor paid-causal-promotion
  field
    estimand : Estimand.CausalEffectEstimand
    estimandKindMatchesDemand :
      Estimand.kind estimand ≡ demandedKind demand
    family : Identification.CausalIdentificationFamily
    identificationGate : Identification.IdentificationEvidenceGate family
    sameObjectReference : String
    causalPromotionReference : String

open PaidCausalPromotion public

------------------------------------------------------------------------
-- Current evidence status.
------------------------------------------------------------------------

relationshipEvidencePaysCausalPolicyInfluence : Bool
relationshipEvidencePaysCausalPolicyInfluence = false

deploymentEvidencePaysCausalSovereignControl : Bool
deploymentEvidencePaysCausalSovereignControl = false

chronologyPaysThreatMaintenancePoliticalSurvivalCausation : Bool
chronologyPaysThreatMaintenancePoliticalSurvivalCausation = false

causalPromotionRequiresExplicitEstimandAndIdentification : Bool
causalPromotionRequiresExplicitEstimandAndIdentification = true

networkProximitySubstitutesForIdentificationDesign : Bool
networkProximitySubstitutesForIdentificationDesign = false

motiveInterpretationSubstitutesForCausalEffect : Bool
motiveInterpretationSubstitutesForCausalEffect = false

record OracleEllisonCausalIdentificationBoundary : Set where
  constructor oracle-ellison-causal-identification-boundary
  field
    relationshipIsCausalEffect : Bool
    chronologyIsCausalIdentification : Bool
    deploymentIsSovereignControlEffect : Bool
    exactEstimandRequired : Bool
    identificationGateRequired : Bool
    estimandAndIdentificationRemainSeparate : Bool
    networkProximityCanReplaceDesign : Bool

canonicalOracleEllisonCausalIdentificationBoundary :
  OracleEllisonCausalIdentificationBoundary
canonicalOracleEllisonCausalIdentificationBoundary =
  oracle-ellison-causal-identification-boundary
    false false false true true true false
