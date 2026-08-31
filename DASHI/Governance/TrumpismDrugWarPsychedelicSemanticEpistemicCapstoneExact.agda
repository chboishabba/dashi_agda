module DASHI.Governance.TrumpismDrugWarPsychedelicSemanticEpistemicCapstoneExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.SemanticEpistemicInterpretationExact as SemEpi
import DASHI.Governance.TrumpDrugPolicyPsychedelicClassificationBidiExact as TrumpPolicy
import DASHI.Governance.DrugWarReflectingPoolFailureBoundaryExact as DrugWar
import DASHI.Governance.DrugGovernanceIntersectionalAuthorityExact as Intersectional
import DASHI.Governance.VeteranPsychedelicTraumaAccessBoundaryExact as Veteran
import DASHI.Governance.PsychedelicIndigenousAuthorityIntersectionalExact as Indigenous
import DASHI.Biology.KluverFormConstantPsychedelicBoundaryExact as Kluver

------------------------------------------------------------------------
-- TRUMPISM / DRUG WAR / PSYCHEDELIC SEMANTIC:EPISTEMIC CAPSTONE
--
-- The capstone treats "Trumpism" as a candidate interpretation of a bundle of
-- policy/narrative/classification observations, never as an essence recovered
-- from one act or one actor.  It asks what evidence would support stronger
-- readings about punitive restoration, therapeutic exception, status-conditioned
-- deservingness, externalising reflection, market extraction, or Indigenous
-- authority exclusion/recognition.
------------------------------------------------------------------------

data CrossObservation : Set where
  punitiveNationalDrugStrategyObservation
  psychedelicAccelerationObservation
  veteranTrialPriorityObservation
  reflectingExternalEnemyNarrativeObservation
  indigenousAuthorityBoundaryObservation
  recurrentGeometricPhenomenologyObservation
  : CrossObservation

data CrossMeaning : Set where
  candidatePunitiveRestorationMeaning
  candidateTherapeuticReclassificationMeaning
  candidateStatusConditionedDeservingnessMeaning
  candidateExternalisingReflectionMeaning
  candidateWarOnDrugsGoalFailureMeaning
  candidateCommercialExtractionMeaning
  candidateIndigenousEpistemicJusticeMeaning
  candidatePluralTrumpismContradictionMeaning
  : CrossMeaning

meaningScale : CrossMeaning → SemEpi.InterpretationScale
meaningScale candidatePunitiveRestorationMeaning = SemEpi.institutionalGovernanceScale
meaningScale candidateTherapeuticReclassificationMeaning = SemEpi.institutionalGovernanceScale
meaningScale candidateStatusConditionedDeservingnessMeaning = SemEpi.incentiveStructureScale
meaningScale candidateExternalisingReflectionMeaning = SemEpi.politicalEconomyScale
meaningScale candidateWarOnDrugsGoalFailureMeaning = SemEpi.institutionalGovernanceScale
meaningScale candidateCommercialExtractionMeaning = SemEpi.politicalEconomyScale
meaningScale candidateIndigenousEpistemicJusticeMeaning = SemEpi.politicalEconomyScale
meaningScale candidatePluralTrumpismContradictionMeaning = SemEpi.politicalEconomyScale

data Candidate : CrossObservation → CrossMeaning → Set where
  punitiveRestorationCandidate :
    Candidate punitiveNationalDrugStrategyObservation candidatePunitiveRestorationMeaning
  therapeuticReclassificationCandidate :
    Candidate psychedelicAccelerationObservation candidateTherapeuticReclassificationMeaning
  veteranDeservingnessCandidate :
    Candidate veteranTrialPriorityObservation candidateStatusConditionedDeservingnessMeaning
  externalisingReflectionCandidate :
    Candidate reflectingExternalEnemyNarrativeObservation candidateExternalisingReflectionMeaning
  warFailureCandidate :
    Candidate punitiveNationalDrugStrategyObservation candidateWarOnDrugsGoalFailureMeaning
  commercialExtractionCandidate :
    Candidate psychedelicAccelerationObservation candidateCommercialExtractionMeaning
  indigenousJusticeCandidate :
    Candidate indigenousAuthorityBoundaryObservation candidateIndigenousEpistemicJusticeMeaning
  trumpismContradictionFromPunitive :
    Candidate punitiveNationalDrugStrategyObservation candidatePluralTrumpismContradictionMeaning
  trumpismContradictionFromTherapeutic :
    Candidate psychedelicAccelerationObservation candidatePluralTrumpismContradictionMeaning

------------------------------------------------------------------------
-- Different interpretations require different evidence.  These are deliberately
-- not reducible to one ideological classifier.
------------------------------------------------------------------------

data Requires : CrossMeaning → SemEpi.SystemEvidenceDemand → Set where
  punitiveNeedsRule :
    Requires candidatePunitiveRestorationMeaning SemEpi.regulatoryRuleDemand
  punitiveNeedsEnforcement :
    Requires candidatePunitiveRestorationMeaning SemEpi.enforcementPracticeDemand
  punitiveNeedsHistory :
    Requires candidatePunitiveRestorationMeaning SemEpi.causalMediationDemand

  therapeuticNeedsRule :
    Requires candidateTherapeuticReclassificationMeaning SemEpi.regulatoryRuleDemand
  therapeuticNeedsAccess :
    Requires candidateTherapeuticReclassificationMeaning SemEpi.populationTransportDemand

  deservingnessNeedsComparison :
    Requires candidateStatusConditionedDeservingnessMeaning SemEpi.comparativeInstitutionalDemand
  deservingnessNeedsMediation :
    Requires candidateStatusConditionedDeservingnessMeaning SemEpi.causalMediationDemand

  reflectionNeedsHistory :
    Requires candidateExternalisingReflectionMeaning SemEpi.causalMediationDemand
  reflectionNeedsCounterfactual :
    Requires candidateExternalisingReflectionMeaning SemEpi.counterfactualInstitutionalDemand

  failureNeedsRecurrence :
    Requires candidateWarOnDrugsGoalFailureMeaning SemEpi.recurrenceDemand
  failureNeedsComparison :
    Requires candidateWarOnDrugsGoalFailureMeaning SemEpi.comparativeInstitutionalDemand
  failureNeedsCounterfactual :
    Requires candidateWarOnDrugsGoalFailureMeaning SemEpi.counterfactualInstitutionalDemand

  extractionNeedsOwnership :
    Requires candidateCommercialExtractionMeaning SemEpi.ownershipMarketStructureDemand
  extractionNeedsExternality :
    Requires candidateCommercialExtractionMeaning SemEpi.externalityAllocationDemand

  indigenousJusticeNeedsOwnership :
    Requires candidateIndigenousEpistemicJusticeMeaning SemEpi.ownershipMarketStructureDemand
  indigenousJusticeNeedsExternality :
    Requires candidateIndigenousEpistemicJusticeMeaning SemEpi.externalityAllocationDemand
  indigenousJusticeNeedsComparison :
    Requires candidateIndigenousEpistemicJusticeMeaning SemEpi.comparativeInstitutionalDemand

  trumpismNeedsPolicyBundle :
    Requires candidatePluralTrumpismContradictionMeaning SemEpi.regulatoryRuleDemand
  trumpismNeedsEnforcement :
    Requires candidatePluralTrumpismContradictionMeaning SemEpi.enforcementPracticeDemand
  trumpismNeedsComparativeAccess :
    Requires candidatePluralTrumpismContradictionMeaning SemEpi.comparativeInstitutionalDemand
  trumpismNeedsHistoricalMediation :
    Requires candidatePluralTrumpismContradictionMeaning SemEpi.causalMediationDemand

problem : SemEpi.SemanticEpistemicProblem
problem = SemEpi.semanticEpistemicProblem
  CrossObservation
  CrossMeaning
  Candidate
  meaningScale
  Requires
  (λ
    { punitiveNationalDrugStrategyObservation → "2026 punitive/enforcement National Drug Control Strategy surface"
    ; psychedelicAccelerationObservation → "2026 psychedelic research/access acceleration surface"
    ; veteranTrialPriorityObservation → "2026 veteran-priority psychedelic trial surface"
    ; reflectingExternalEnemyNarrativeObservation → "candidate externalising/asymmetric-reflection drug narrative surface"
    ; indigenousAuthorityBoundaryObservation → "Indigenous provenance/governance/protocol/permission/sovereignty boundary"
    ; recurrentGeometricPhenomenologyObservation → "Klüver recurrent geometric phenomenology surface"
    })
  (λ
    { candidatePunitiveRestorationMeaning → "candidate punitive-restoration governance meaning"
    ; candidateTherapeuticReclassificationMeaning → "candidate therapeutic reclassification meaning"
    ; candidateStatusConditionedDeservingnessMeaning → "candidate status-conditioned deservingness/access meaning"
    ; candidateExternalisingReflectionMeaning → "candidate externalising/asymmetric-reflection meaning"
    ; candidateWarOnDrugsGoalFailureMeaning → "candidate goal-relative War-on-Drugs failure meaning"
    ; candidateCommercialExtractionMeaning → "candidate commercialization/extraction meaning"
    ; candidateIndigenousEpistemicJusticeMeaning → "candidate Indigenous epistemic-justice/sovereignty meaning"
    ; candidatePluralTrumpismContradictionMeaning → "candidate plural Trump-era governance contradiction/tension meaning"
    })
  "cross-domain semantic:epistemic interpretations require separate policy, outcome, access, historical, authority and comparative evidence"

------------------------------------------------------------------------
-- Reuse canonical boundaries rather than flattening them.
------------------------------------------------------------------------

trumpPolicyBoundary : TrumpPolicy.TrumpDrugPolicyClassificationBoundary
trumpPolicyBoundary = TrumpPolicy.canonicalTrumpDrugPolicyClassificationBoundary

drugWarBoundary : DrugWar.DrugWarReflectingPoolBoundary
drugWarBoundary = DrugWar.canonicalDrugWarReflectingPoolBoundary

intersectionalBoundary : Intersectional.DrugGovernanceIntersectionalBoundary
intersectionalBoundary = Intersectional.canonicalDrugGovernanceIntersectionalBoundary

veteranBoundary : Veteran.VeteranPsychedelicTraumaAccessBoundary
veteranBoundary = Veteran.canonicalVeteranPsychedelicTraumaAccessBoundary

indigenousBoundary : Indigenous.PsychedelicIndigenousIntersectionalBoundary
indigenousBoundary = Indigenous.canonicalPsychedelicIndigenousIntersectionalBoundary

kluverBoundary : Kluver.KluverPsychedelicBoundary
kluverBoundary = Kluver.canonicalKluverPsychedelicBoundary

------------------------------------------------------------------------
-- Explicit non-identifications.
------------------------------------------------------------------------

data TrumpPolicyBundlePromotesTrumpismEssence : Set where

data VeteranTrialPromotesDrugWarSuccess : Set where

data PsychedelicGeometryPromotesPoliticalMeaning : Set where

data IndigenousAuthorityPromotesAntiBiomedicalConclusion : Set where

policyBundleDoesNotPromoteTrumpismEssence :
  TrumpPolicyBundlePromotesTrumpismEssence → ⊥
policyBundleDoesNotPromoteTrumpismEssence ()

veteranTrialDoesNotPromoteDrugWarSuccess : VeteranTrialPromotesDrugWarSuccess → ⊥
veteranTrialDoesNotPromoteDrugWarSuccess ()

geometryDoesNotPromotePoliticalMeaning :
  PsychedelicGeometryPromotesPoliticalMeaning → ⊥
geometryDoesNotPromotePoliticalMeaning ()

indigenousAuthorityDoesNotPromoteAntiBiomedicalConclusion :
  IndigenousAuthorityPromotesAntiBiomedicalConclusion → ⊥
indigenousAuthorityDoesNotPromoteAntiBiomedicalConclusion ()

record TrumpismDrugWarPsychedelicCapstoneBoundary : Set where
  constructor trumpismDrugWarPsychedelicCapstoneBoundary
  field
    punitiveAndTherapeuticDrugRoutesCanCoexist : Bool
    punitiveAndTherapeuticDrugRoutesCanCoexistIsTrue :
      punitiveAndTherapeuticDrugRoutesCanCoexist ≡ true
    coexistenceCanGenerateAComparativeGovernanceQuestion : Bool
    coexistenceCanGenerateAComparativeGovernanceQuestionIsTrue :
      coexistenceCanGenerateAComparativeGovernanceQuestion ≡ true
    oneContradictionSurfaceDefinesTrumpism : Bool
    oneContradictionSurfaceDefinesTrumpismIsFalse :
      oneContradictionSurfaceDefinesTrumpism ≡ false
    veteransIndigenousCommunitiesAndCriminalizedUsersShareIdenticalAuthorityPosition : Bool
    veteransIndigenousCommunitiesAndCriminalizedUsersShareIdenticalAuthorityPositionIsFalse :
      veteransIndigenousCommunitiesAndCriminalizedUsersShareIdenticalAuthorityPosition ≡ false
    recurringPsychedelicGeometryClosesCulturalMeaning : Bool
    recurringPsychedelicGeometryClosesCulturalMeaningIsFalse :
      recurringPsychedelicGeometryClosesCulturalMeaning ≡ false

canonicalTrumpismDrugWarPsychedelicCapstoneBoundary :
  TrumpismDrugWarPsychedelicCapstoneBoundary
canonicalTrumpismDrugWarPsychedelicCapstoneBoundary =
  trumpismDrugWarPsychedelicCapstoneBoundary
    true refl
    true refl
    false refl
    false refl
    false refl
