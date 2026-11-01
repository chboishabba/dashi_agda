module DASHI.Law.SensibLawWoogarooEPBC20198575OperativeMeritsRulesExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- EPBC 2019/8575 — OPERATIVE PRE-REFORM MERITS RULES
--
-- Source-bounded reconstruction of the pre-24-August-2026 Part 9 rules that
-- remain the relevant starting point for the 2019 referral after applying the
-- Reform Act transition matrix.  This does not decide merits and remains for
-- counsel confirmation against the exact transition provisions.
------------------------------------------------------------------------

data RuleRole : Set where
  approvalPower : RuleRole
  conditionsPower : RuleRole
  mandatoryConsideration : RuleRole
  threatenedSpeciesConstraint : RuleRole
  irrelevantControllingMatter : RuleRole

record OperativeRule : Set where
  constructor operative-rule
  field
    provision : String
    role : RuleRole
    boundedRule : String
    sourceVersion : String
    relevantTo20198575 : Bool
    compelsRefusal : Bool

open OperativeRule public

s133 : OperativeRule
s133 = operative-rule
  "EPBC s 133"
  approvalPower
  "After receiving the assessment documentation for the controlled action, the Minister may approve the action for a controlling provision. The section also requires a written approval to specify the action, approval holder, controlling provisions, duration and conditions; refusal must be notified."
  "EPBC Act compilation C68, 28 March 2026, pre-24-August-2026 merits text"
  true
  false

s134 : OperativeRule
s134 = operative-rule
  "EPBC s 134"
  conditionsPower
  "The Minister may attach conditions where satisfied they are necessary or convenient to protect a Part 3 matter or repair/mitigate damage to it. Conditions may include protective activities, monitoring, audits, compliance with other instruments and other measures within the statutory power."
  "EPBC Act compilation C68, 28 March 2026, pre-24-August-2026 merits text"
  true
  false

s136 : OperativeRule
s136 = operative-rule
  "EPBC s 136"
  mandatoryConsideration
  "In deciding approval and conditions, the Minister must consider matters relevant to each controlling Part 3 provision and economic/social matters; must take into account ESD principles, the applicable assessment material, the Preliminary Documentation material and recommendation report, other information on relevant impacts, and relevant invited comments; and must not consider matters outside the Division."
  "EPBC Act compilation C68, 28 March 2026, with item-683 preservation of specified assessment-linked paragraphs"
  true
  false

s138 : OperativeRule
s138 = operative-rule
  "EPBC s 138"
  irrelevantControllingMatter
  "Pre-reform s 138 concerns Ramsar-wetland approval decisions. The currently source-paid controlling provisions for 2019/8575 are ss 18/18A threatened species and communities, so s 138 is not presently a controlling-matter rule for this project unless a Ramsar controlling provision is separately established."
  "EPBC Act compilation C68, 28 March 2026"
  false
  false

s139 : OperativeRule
s139 = operative-rule
  "EPBC s 139"
  threatenedSpeciesConstraint
  "For approval under ss 18/18A, the Minister must not act inconsistently with specified international biodiversity obligations or a recovery plan/threat abatement plan. If the action has, will have or is likely to have a significant impact on a particular listed threatened species or ecological community, the Minister must have regard to any approved conservation advice for that species/community."
  "EPBC Act compilation C68, 28 March 2026; substituted 2026 ss 138/139 do not apply to this 2019 referral under Reform Act item 690(1)"
  true
  false

------------------------------------------------------------------------
-- Evidence-to-rule consumers.
------------------------------------------------------------------------

data EvidenceCoordinate : Set where
  exactActionFootprint : EvidenceCoordinate
  habitatLossAndRetention : EvidenceCoordinate
  habitatQuality : EvidenceCoordinate
  speciesUse : EvidenceCoordinate
  corridorConnectivity : EvidenceCoordinate
  fragmentationAndCumulativeImpact : EvidenceCoordinate
  avoidanceAlternatives : EvidenceCoordinate
  residualImpact : EvidenceCoordinate
  offsets : EvidenceCoordinate
  approvedConservationAdvice : EvidenceCoordinate
  recoveryPlanOrThreatAbatementPlan : EvidenceCoordinate
  economicAndSocialMatter : EvidenceCoordinate

record MeritsConsumer : Set where
  constructor merits-consumer
  field
    coordinate : EvidenceCoordinate
    primaryProvision : String
    presentlySourcePaid : Bool
    missingPayment : String

open MeritsConsumer public

footprintConsumer : MeritsConsumer
footprintConsumer = merits-consumer exactActionFootprint "ss 133, 136" false
  "Exact action/cadastral polygon from the Preliminary Documentation or equivalent primary project material."

fragmentationConsumer : MeritsConsumer
fragmentationConsumer = merits-consumer fragmentationAndCumulativeImpact "s 136; s 139 where species/community significance is engaged" false
  "Exact project polygon x habitat/corridor function x severance/cumulative-impact evidence."

conservationAdviceConsumer : MeritsConsumer
conservationAdviceConsumer = merits-consumer approvedConservationAdvice "s 139(2)" false
  "Identify each applicable approved conservation advice and map its relevant habitat/significance criteria to the exact project evidence."

recoveryPlanConsumer : MeritsConsumer
recoveryPlanConsumer = merits-consumer recoveryPlanOrThreatAbatementPlan "s 139(1)" false
  "Identify any applicable recovery plan or threat abatement plan and test whether approval/conditions would be inconsistent with it."

offsetConsumer : MeritsConsumer
offsetConsumer = merits-consumer offsets "ss 134, 136, 139" false
  "Extract the actual proposed offset package and test whether it addresses the same protected-matter impact rather than merely supplying remote area."

------------------------------------------------------------------------
-- WrongType / no-overclaim boundaries.
------------------------------------------------------------------------

record MeritsBoundary : Set where
  constructor merits-boundary
  field
    controlledActionDoesNotCompelRefusal : Bool
    mandatoryConsiderationDoesNotPredetermineWeight : Bool
    conditionsPowerDoesNotProveConditionsAreSufficient : Bool
    significantImpactDoesNotByItselfCompelRefusal : Bool
    remoteOffsetAreaDoesNotByItselfReplaceLocalFunction : Bool
    currentConsolidatedTextDoesNotOverrideTransitionMapping : Bool

meritsBoundary : MeritsBoundary
meritsBoundary = merits-boundary true true true true true true

record MeritsResidual : Set where
  constructor merits-residual
  field
    question : String
    closed : Bool

currentMeritsResidual : MeritsResidual
currentMeritsResidual = merits-residual
  "Extract the 2019/8575 Preliminary Documentation and recommendation/report material, bind each primary factual proposition to the operative ss 133/134/136/139 consumer, and ask counsel whether the record supports refusal, conditioned approval, further information, or a reviewable failure to consider mandatory material."
  false
