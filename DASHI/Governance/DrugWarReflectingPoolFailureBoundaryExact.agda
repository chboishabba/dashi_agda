module DASHI.Governance.DrugWarReflectingPoolFailureBoundaryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Governance.TraumaMemorySublationBoundary as Reflection
import DASHI.Governance.BritishColumbiaDecriminalizationBundleExact as BC
import DASHI.Governance.TrumpDrugPolicyPsychedelicClassificationBidiExact as TrumpPolicy

------------------------------------------------------------------------
-- WAR-ON-DRUGS FAILURE x REFLECTING-POOL BOUNDARY
--
-- "Failed" is goal-relative: a policy regime can only be called failed after
-- specifying the intended objective and the observed outcome/cost surface.
-- The reflecting-pool connection is structural and candidate-only: unresolved
-- internal/systemic conditions may be narrated through a salient external
-- carrier/enemy, but such externalisation is not inferred from enforcement
-- rhetoric alone.
------------------------------------------------------------------------

data DrugPolicyGoal : Set where
  reduceOverdoseMortality
  reduceProblematicUse
  reduceIllicitSupply
  reduceViolence
  improveTreatmentAccess
  reduceCriminalJusticeHarm
  improveHousingAndSocialStability
  : DrugPolicyGoal

data GoalOutcome : Set where
  goalImproved
  goalUnchanged
  goalWorsened
  goalMixedOrUnresolved
  : GoalOutcome

data PolicyCostAxis : Set where
  policingCost
  incarcerationCost
  displacementCost
  treatmentOpportunityCost
  stigmaCost
  housingInstabilityCost
  : PolicyCostAxis

record GoalRelativeFailureAssessment : Set where
  constructor goalRelativeFailureAssessment
  field
    goal : DrugPolicyGoal
    outcome : GoalOutcome
    policyPeriodReference : String
    outcomeEvidenceReference : String
    comparisonReference : String
    counterfactualReference : String
    causalAttributionInstalled : Bool
    causalAttributionInstalledIsFalse : causalAttributionInstalled ≡ false

open GoalRelativeFailureAssessment public

------------------------------------------------------------------------
-- Reflection/externalisation is a candidate semantic reading.
------------------------------------------------------------------------

data DrugPolicyNarrativeCarrier : Set where
  externalCartelCarrier
  illicitDealerCarrier
  criminalizedUserCarrier
  domesticStructuralConditionCarrier
  treatmentSystemCapacityCarrier
  housingPovertyConditionCarrier
  : DrugPolicyNarrativeCarrier

record ExternalisingDrugNarrativeCandidate : Set where
  constructor externalisingDrugNarrativeCandidate
  field
    salientCarrier : DrugPolicyNarrativeCarrier
    unresolvedInternalConditionsRetained : Bool
    unresolvedInternalConditionsRetainedIsTrue :
      unresolvedInternalConditionsRetained ≡ true
    externalCarrierIsCompleteCause : Bool
    externalCarrierIsCompleteCauseIsFalse :
      externalCarrierIsCompleteCause ≡ false
    motiveOrScapegoatingInferredAsFact : Bool
    motiveOrScapegoatingInferredAsFactIsFalse :
      motiveOrScapegoatingInferredAsFact ≡ false
    narrativeReference : String

open ExternalisingDrugNarrativeCandidate public

canonicalExternalisingCandidate : ExternalisingDrugNarrativeCandidate
canonicalExternalisingCandidate = externalisingDrugNarrativeCandidate
  externalCartelCarrier
  true refl
  false refl
  false refl
  "candidate asymmetric-reflection reading: external drug enemy is salient while domestic demand, treatment capacity, housing, poverty, regulation and market conditions remain causally open"

reflectionBoundary : Reflection.TraumaMemorySublationBoundary
reflectionBoundary = Reflection.canonicalTraumaMemorySublationBoundary

bcBundleBoundary : BC.BCBundleBoundary
bcBundleBoundary = BC.canonicalBCBundleBoundary

trumpPolicyBoundary : TrumpPolicy.TrumpDrugPolicyClassificationBoundary
trumpPolicyBoundary = TrumpPolicy.canonicalTrumpDrugPolicyClassificationBoundary

------------------------------------------------------------------------
-- Failure and reflection do not collapse into one another.
------------------------------------------------------------------------

data PunitiveFailurePromotesScapegoatingMotive : Set where

data ExternalisingNarrativePromotesPolicyFailure : Set where

data DecriminalizationLabelPromotesSuccessfulAlternative : Set where

punitiveFailureDoesNotPromoteScapegoatingMotive :
  PunitiveFailurePromotesScapegoatingMotive → ⊥
punitiveFailureDoesNotPromoteScapegoatingMotive ()

externalisingNarrativeDoesNotPromoteFailure :
  ExternalisingNarrativePromotesPolicyFailure → ⊥
externalisingNarrativeDoesNotPromoteFailure ()

decriminalizationLabelDoesNotPromoteSuccess :
  DecriminalizationLabelPromotesSuccessfulAlternative → ⊥
decriminalizationLabelDoesNotPromoteSuccess ()

record DrugWarReflectingPoolBoundary : Set where
  constructor drugWarReflectingPoolBoundary
  field
    warOnDrugsFailureMustBeGoalRelative : Bool
    warOnDrugsFailureMustBeGoalRelativeIsTrue :
      warOnDrugsFailureMustBeGoalRelative ≡ true
    enforcementNarrativeMayBeInspectedForExternalisingReflection : Bool
    enforcementNarrativeMayBeInspectedForExternalisingReflectionIsTrue :
      enforcementNarrativeMayBeInspectedForExternalisingReflection ≡ true
    enforcementRhetoricProvesScapegoatingMotive : Bool
    enforcementRhetoricProvesScapegoatingMotiveIsFalse :
      enforcementRhetoricProvesScapegoatingMotive ≡ false
    punitivePolicyFailureAutomaticallyProvesDecriminalizationSuccess : Bool
    punitivePolicyFailureAutomaticallyProvesDecriminalizationSuccessIsFalse :
      punitivePolicyFailureAutomaticallyProvesDecriminalizationSuccess ≡ false
    underprovisionedReformIsNotACompleteAlternativeWorld : Bool
    underprovisionedReformIsNotACompleteAlternativeWorldIsTrue :
      underprovisionedReformIsNotACompleteAlternativeWorld ≡ true

canonicalDrugWarReflectingPoolBoundary : DrugWarReflectingPoolBoundary
canonicalDrugWarReflectingPoolBoundary =
  drugWarReflectingPoolBoundary
    true refl
    true refl
    false refl
    false refl
    true refl
