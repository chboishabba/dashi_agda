module DASHI.Cognition.PNF.SensibLawNegligenceDutyRequirementSalienceExact where

open import DASHI.Core.Prelude

import DASHI.Cognition.PNF.SensibLawClimateDutyRouteSearchExact as Climate
import DASHI.Cognition.PNF.SensibLawNegligenceDutyWrongTypeSpecializationExact as Negligence
import DASHI.Cognition.PNF.SensibLawWrongTypeRequirementSalienceFrontierExact as Frontier

------------------------------------------------------------------------
-- NEGLIGENCE / DUTY REQUIREMENT SALIENCE
--
-- This is a DASHI synthetic scheduler calibration over already sourced duty
-- coordinates. It does not attribute the observation matrix below to any court.
-- The underlying legal-source ownership remains in the negligence/climate duty
-- modules (Donoghue, Woolcock, Mallonland, Pabai and their stable identifiers).
------------------------------------------------------------------------

data DutyInterpretation : Set where
  operationalPublicAuthorityConfiguration
  corePolicyPublicAuthorityConfiguration
  : DutyInterpretation

data DutyObservation : Set where
  dutyUnsupported dutyUnresolved dutySupported : DutyObservation

currentDutyLive : DutyInterpretation → Set
currentDutyLive operationalPublicAuthorityConfiguration = ⊤
currentDutyLive corePolicyPublicAuthorityConfiguration = ⊤

observeCurrentDuty : Climate.DutyIssue → DutyInterpretation → DutyObservation
observeCurrentDuty Climate.reasonableForeseeability operationalPublicAuthorityConfiguration = dutySupported
observeCurrentDuty Climate.reasonableForeseeability corePolicyPublicAuthorityConfiguration = dutySupported
observeCurrentDuty Climate.coreGovernmentPolicy operationalPublicAuthorityConfiguration = dutyUnsupported
observeCurrentDuty Climate.coreGovernmentPolicy corePolicyPublicAuthorityConfiguration = dutySupported
observeCurrentDuty Climate.statutoryCoherence operationalPublicAuthorityConfiguration = dutyUnresolved
observeCurrentDuty Climate.statutoryCoherence corePolicyPublicAuthorityConfiguration = dutyUnresolved
observeCurrentDuty issue operationalPublicAuthorityConfiguration = dutyUnresolved
observeCurrentDuty issue corePolicyPublicAuthorityConfiguration = dutyUnresolved

data DutyRequired : Climate.DutyIssue → Set where
  foreseeabilityRequired : DutyRequired Climate.reasonableForeseeability
  corePolicyRequired : DutyRequired Climate.coreGovernmentPolicy
  statutoryCoherenceRequired : DutyRequired Climate.statutoryCoherence

data DutyRelevant : Climate.DutyIssue → Set where
  foreseeabilityRelevant : DutyRelevant Climate.reasonableForeseeability
  corePolicyRelevant : DutyRelevant Climate.coreGovernmentPolicy
  statutoryCoherenceRelevant : DutyRelevant Climate.statutoryCoherence

data DutyAdmissible : Climate.DutyIssue → Set where
  foreseeabilityAdmissible : DutyAdmissible Climate.reasonableForeseeability
  corePolicyAdmissible : DutyAdmissible Climate.coreGovernmentPolicy
  statutoryCoherenceAdmissible : DutyAdmissible Climate.statutoryCoherence

currentDutyProblem :
  Frontier.RequirementSalienceProblem Climate.DutyIssue DutyInterpretation DutyObservation
currentDutyProblem = Frontier.requirement-salience-problem
  currentDutyLive
  observeCurrentDuty
  DutyRequired
  DutyRelevant
  DutyAdmissible
  "Synthetic duty collision: both live configurations agree on foreseeability, while they differ on the core-policy classification and leave statutory coherence unresolved."

foreseeabilityRequiredButCurrentlyNonDiscriminating :
  Frontier.NecessaryButCurrentlyNonDiscriminating
    currentDutyProblem Climate.reasonableForeseeability
foreseeabilityRequiredButCurrentlyNonDiscriminating =
  Frontier.necessary-but-currently-nondiscriminating
    foreseeabilityRequired
    foreseeabilityRelevant
    foreseeabilityAdmissible
    (Frontier.zero-current-discrimination same)
  where
    same : ∀ left right →
      currentDutyLive left → currentDutyLive right →
      observeCurrentDuty Climate.reasonableForeseeability left
      ≡ observeCurrentDuty Climate.reasonableForeseeability right
    same operationalPublicAuthorityConfiguration operationalPublicAuthorityConfiguration l r = refl
    same operationalPublicAuthorityConfiguration corePolicyPublicAuthorityConfiguration l r = refl
    same corePolicyPublicAuthorityConfiguration operationalPublicAuthorityConfiguration l r = refl
    same corePolicyPublicAuthorityConfiguration corePolicyPublicAuthorityConfiguration l r = refl

corePolicyCurrentlySplitsDutyFibre :
  Frontier.SalientRequirement currentDutyProblem Climate.coreGovernmentPolicy
corePolicyCurrentlySplitsDutyFibre = Frontier.salient-requirement
  corePolicyRequired
  corePolicyRelevant
  corePolicyAdmissible
  (Frontier.splits-current-live-fibre
    operationalPublicAuthorityConfiguration
    corePolicyPublicAuthorityConfiguration
    tt tt
    (λ ()))

statutoryCoherenceRequiredButCurrentlyNonDiscriminating :
  Frontier.NecessaryButCurrentlyNonDiscriminating
    currentDutyProblem Climate.statutoryCoherence
statutoryCoherenceRequiredButCurrentlyNonDiscriminating =
  Frontier.necessary-but-currently-nondiscriminating
    statutoryCoherenceRequired
    statutoryCoherenceRelevant
    statutoryCoherenceAdmissible
    (Frontier.zero-current-discrimination same)
  where
    same : ∀ left right →
      currentDutyLive left → currentDutyLive right →
      observeCurrentDuty Climate.statutoryCoherence left
      ≡ observeCurrentDuty Climate.statutoryCoherence right
    same operationalPublicAuthorityConfiguration operationalPublicAuthorityConfiguration l r = refl
    same operationalPublicAuthorityConfiguration corePolicyPublicAuthorityConfiguration l r = refl
    same corePolicyPublicAuthorityConfiguration operationalPublicAuthorityConfiguration l r = refl
    same corePolicyPublicAuthorityConfiguration corePolicyPublicAuthorityConfiguration l r = refl

------------------------------------------------------------------------
-- After the policy-classification question is resolved, a previously inert
-- required coordinate may become the next discriminator.
------------------------------------------------------------------------

data PostPolicyInterpretation : Set where
  policyNoStatutoryConflict
  policyStatutoryConflict
  : PostPolicyInterpretation

postPolicyLive : PostPolicyInterpretation → Set
postPolicyLive policyNoStatutoryConflict = ⊤
postPolicyLive policyStatutoryConflict = ⊤

observePostPolicy : Climate.DutyIssue → PostPolicyInterpretation → DutyObservation
observePostPolicy Climate.coreGovernmentPolicy policyNoStatutoryConflict = dutySupported
observePostPolicy Climate.coreGovernmentPolicy policyStatutoryConflict = dutySupported
observePostPolicy Climate.statutoryCoherence policyNoStatutoryConflict = dutySupported
observePostPolicy Climate.statutoryCoherence policyStatutoryConflict = dutyUnsupported
observePostPolicy Climate.reasonableForeseeability policyNoStatutoryConflict = dutySupported
observePostPolicy Climate.reasonableForeseeability policyStatutoryConflict = dutySupported
observePostPolicy issue policyNoStatutoryConflict = dutyUnresolved
observePostPolicy issue policyStatutoryConflict = dutyUnresolved

postPolicyProblem :
  Frontier.RequirementSalienceProblem Climate.DutyIssue PostPolicyInterpretation DutyObservation
postPolicyProblem = Frontier.requirement-salience-problem
  postPolicyLive
  observePostPolicy
  DutyRequired
  DutyRelevant
  DutyAdmissible
  "Synthetic post-policy collision: policy classification is held fixed and statutory coherence becomes the live discriminator."

statutoryCoherenceBecomesSalientAfterPolicyClosure :
  Frontier.SalientRequirement postPolicyProblem Climate.statutoryCoherence
statutoryCoherenceBecomesSalientAfterPolicyClosure = Frontier.salient-requirement
  statutoryCoherenceRequired
  statutoryCoherenceRelevant
  statutoryCoherenceAdmissible
  (Frontier.splits-current-live-fibre
    policyNoStatutoryConflict
    policyStatutoryConflict
    tt tt
    (λ ()))

------------------------------------------------------------------------
-- Ontological-role pins from the existing negligence specialization.
------------------------------------------------------------------------

foreseeabilityRemainsFactualFeature :
  Negligence.classifyDutyIssue Climate.reasonableForeseeability
  ≡ Negligence.factualDutyFeature
foreseeabilityRemainsFactualFeature = refl

corePolicyRemainsInstitutionalConstraint :
  Negligence.classifyDutyIssue Climate.coreGovernmentPolicy
  ≡ Negligence.institutionalDutyConstraint
corePolicyRemainsInstitutionalConstraint = refl

statutoryCoherenceRemainsDoctrinalPredicate :
  Negligence.classifyDutyIssue Climate.statutoryCoherence
  ≡ Negligence.doctrinalDutyPredicate
statutoryCoherenceRemainsDoctrinalPredicate = refl

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ForeseeabilityAgreementMeansForeseeabilityNotRequired : Set where
data CorePolicySalienceMeansCorePolicyIsCategoricalNoDutyRule : Set where
data StatutoryCoherenceSalienceMeansConflictExists : Set where

data DutySalienceOrderIsNegligenceElementOrder : Set where

foreseeabilityAgreementDoesNotEraseRequirement :
  ForeseeabilityAgreementMeansForeseeabilityNotRequired → ⊥
foreseeabilityAgreementDoesNotEraseRequirement ()

corePolicySalienceDoesNotCreateCategoricalRule :
  CorePolicySalienceMeansCorePolicyIsCategoricalNoDutyRule → ⊥
corePolicySalienceDoesNotCreateCategoricalRule ()

statutorySalienceDoesNotDecideConflict :
  StatutoryCoherenceSalienceMeansConflictExists → ⊥
statutorySalienceDoesNotDecideConflict ()

salienceOrderDoesNotReplaceNegligenceDoctrine : DutySalienceOrderIsNegligenceElementOrder → ⊥
salienceOrderDoesNotReplaceNegligenceDoctrine ()
