module DASHI.Wikimedia.IbrahimScienceKnowledgePluralityBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Empty using (⊥)

import DASHI.Reasoning.MultiObserverScienceQuotient as Science
import DASHI.Core.SituatedFormalisationBoundaryExact as Situated
import DASHI.IndigenousKnowledgeTwoEyedValidation as IKValidation
import DASHI.Wikimedia.IbrahimEnglishPluralKnowledgeFunnelBridgeExact as Plural
import DASHI.Wikimedia.IbrahimKnowledgeCoverageRoadmapExact as Roadmap
import DASHI.Wikimedia.IbrahimKnowledgeCoverageRoadmapBrownExtensionExact as BrownRoadmap

------------------------------------------------------------------------
-- SCIENCE <-> KNOWLEDGE PLURALITY BRIDGE
--
-- This pays roadmap rank 2 at the parent-architecture level. It does not claim
-- a universal theory of knowledge. Science is represented as one structured
-- knowledge-producing family with explicit observer/method/review gates.
-- Formal proof, situated knowledge, Indigenous/community knowledge and
-- institutional records remain distinct source/authority roles.
------------------------------------------------------------------------

data KnowledgeRole : Set where
  empiricalScientific : KnowledgeRole
  formalDeductive : KnowledgeRole
  situatedAffectedSubject : KnowledgeRole
  indigenousCommunity : KnowledgeRole
  institutionalRecord : KnowledgeRole
  historicalSource : KnowledgeRole
  interpretiveCritical : KnowledgeRole

record KnowledgeRoleSurface : Set where
  constructor knowledge-role-surface
  field
    role : KnowledgeRole
    existingDashiSurface : String
    requiredCoordinates : String
    mayContributeToSharedInquiry : Bool
    automaticallyDominatesOtherRoles : Bool
    automaticallyCreatesAuthority : Bool
open KnowledgeRoleSurface public

scienceSurface : KnowledgeRoleSurface
scienceSurface = knowledge-role-surface empiricalScientific
  "MultiObserverScienceQuotient and domain science owners"
  "observer/instrument/model/reviewer role; observation kernel; calibration; fusion residual; admissibility; independent review; replication"
  true false false

formalSurface : KnowledgeRoleSurface
formalSurface = knowledge-role-surface formalDeductive
  "Agda/Lean theorem owners and proof/certification status machinery"
  "statement identity; assumptions; proof term; kernel/certification status; source role when imported"
  true false false

situatedSurface : KnowledgeRoleSurface
situatedSurface = knowledge-role-surface situatedAffectedSubject
  "SituatedFormalisationBoundaryExact; Alice Brown voice/agency/observer plurality; intersectional non-factorability"
  "observer position; affected-subject relation; question/projection/relevance authority; provenance; contestability"
  true false false

indigenousSurface : KnowledgeRoleSurface
indigenousSurface = knowledge-role-surface indigenousCommunity
  "IndigenousKnowledgeStoryTwoEyedSeeingBidiExact; IndigenousKnowledgeTwoEyedValidation; Kimmerer/Two-Eyed/Country owners"
  "Country/place; community/custodial relation; consent/access; story/practice; provenance; interpretation permission; benefit sharing"
  true false false

institutionSurface : KnowledgeRoleSurface
institutionSurface = knowledge-role-surface institutionalRecord
  "governance/legal/education/health institutional record owners"
  "institution identity; jurisdiction/scope; record-production method; affected observers; contestability; authority role"
  true false false

historicalSurface : KnowledgeRoleSurface
historicalSurface = knowledge-role-surface historicalSource
  "source provenance, reception-history, archaeology/history and document-lineage owners"
  "document/object identity; date/revision; author/producer; custody/provenance; context; interpretive uncertainty"
  true false false

criticalSurface : KnowledgeRoleSurface
criticalSurface = knowledge-role-surface interpretiveCritical
  "Hegel/Žižek/Lacan/Irigaray/feminist/dialectical source-bounded owners"
  "source genealogy; interpretive role; grammar; target claim; disagreement/residual; non-identity with empirical authority"
  true false false

------------------------------------------------------------------------
-- Parent relation: knowledge roles can be coordinated without one role being
-- the ontology parent or epistemic master of the others.
------------------------------------------------------------------------

record PluralKnowledgeParent : Set where
  constructor plural-knowledge-parent
  field
    scienceIncluded : Bool
    formalProofIncluded : Bool
    situatedKnowledgeIncluded : Bool
    indigenousCommunityKnowledgeIncluded : Bool
    institutionalRecordsIncluded : Bool
    historicalSourcesIncluded : Bool
    criticalInterpretationIncluded : Bool
    observerRoleRetained : Bool
    methodRoleRetained : Bool
    provenanceRetained : Bool
    authorityCoordinateRetained : Bool
    disagreementMayRemainOpen : Bool
    oneRoleOwnsUniversalPriority : Bool
open PluralKnowledgeParent public

canonicalPluralKnowledgeParent : PluralKnowledgeParent
canonicalPluralKnowledgeParent = plural-knowledge-parent
  true true true true true true true true true true true true false

------------------------------------------------------------------------
-- Existing scientific guardrails are inherited directly.
------------------------------------------------------------------------

scienceBoundary : Science.MultiObserverScienceBoundary
scienceBoundary = Science.canonicalMultiObserverScienceBoundary

scienceDoesNotCloseTruth :
  Science.MultiObserverScienceBoundary.scienceTruthClosure scienceBoundary ≡ false
scienceDoesNotCloseTruth = refl

scienceHasNoObserverNeutralCompleteSlice :
  Science.MultiObserverScienceBoundary.observerNeutralCompleteSlice scienceBoundary ≡ false
scienceHasNoObserverNeutralCompleteSlice = refl

situatedBoundary : Situated.SituatedFormalisationBoundary
situatedBoundary = Situated.canonicalSituatedFormalisationBoundary

formalCarrierNotPositionless :
  Situated.SituatedFormalisationBoundary.formalCarrierIsEpistemicallyPositionless
    situatedBoundary
  ≡ false
formalCarrierNotPositionless = refl

------------------------------------------------------------------------
-- Indigenous/Two-Eyed non-factorability is part of parent admission.
------------------------------------------------------------------------

data ScientificResultCreatesIndigenousProvenance : Set where
data ScientificResultCreatesCommunityConsent : Set where
data SharedObservationFusesKnowledgeHistories : Set where

scientificResultDoesNotCreateIndigenousProvenance : ScientificResultCreatesIndigenousProvenance → ⊥
scientificResultDoesNotCreateIndigenousProvenance ()

scientificResultDoesNotCreateCommunityConsent : ScientificResultCreatesCommunityConsent → ⊥
scientificResultDoesNotCreateCommunityConsent ()

sharedObservationDoesNotFuseKnowledgeHistories : SharedObservationFusesKnowledgeHistories → ⊥
sharedObservationDoesNotFuseKnowledgeHistories ()

------------------------------------------------------------------------
-- Brown lesson: authority within inquiry is coordinate-wise, not scalar.
------------------------------------------------------------------------

record ScienceKnowledgeBrownAdmission : Set where
  constructor science-knowledge-brown-admission
  field
    affectedVoiceRetainedWhenRelevant : Bool
    parentInstitutionObserverSeparated : Bool
    feedbackEqualsConstitutiveAuthority : Bool
    institutionalRecordEqualsWholeSystem : Bool
    authorityAssignedByInquiryCoordinate : Bool
open ScienceKnowledgeBrownAdmission public

canonicalScienceKnowledgeBrownAdmission : ScienceKnowledgeBrownAdmission
canonicalScienceKnowledgeBrownAdmission = science-knowledge-brown-admission
  true true false false true

brownRoadmapPolicy : BrownRoadmap.BrownExtendedRoadmapPolicy
brownRoadmapPolicy = BrownRoadmap.canonicalBrownExtendedRoadmapPolicy

------------------------------------------------------------------------
-- Completion reading for roadmap rank 2.
------------------------------------------------------------------------

record ScienceKnowledgePluralityReceipt : Set where
  constructor science-knowledge-plurality-receipt
  field
    knowledgeParentPresent : Bool
    scienceRepresentedAsKnowledgeRole : Bool
    formalProofRepresentedSeparately : Bool
    situatedObserverRepresented : Bool
    indigenousCommunityKnowledgeRepresented : Bool
    institutionalRecordRepresented : Bool
    provenanceAndAuthoritySeparated : Bool
    scienceEqualsAllKnowledge : Bool
    scientificValidationCreatesUniversalAuthority : Bool
    firstLinkOrQidCreatesEpistemicPriority : Bool
open ScienceKnowledgePluralityReceipt public

canonicalScienceKnowledgePluralityReceipt : ScienceKnowledgePluralityReceipt
canonicalScienceKnowledgePluralityReceipt = science-knowledge-plurality-receipt
  true true true true true true true false false false

selectedRoadmapLeaf : Roadmap.RoadmapLeaf
selectedRoadmapLeaf = Roadmap.scienceKnowledgePlurality

------------------------------------------------------------------------
-- Firewalls.
------------------------------------------------------------------------

data ScienceEqualsKnowledge : Set where
data FormalProofEqualsEmpiricalObservation : Set where
data InstitutionalRecordEqualsAffectedSubjectKnowledge : Set where
data IndigenousKnowledgeNeedsScientificPromotionToExist : Set where
data EpistemicPluralityMeansAllClaimsEqual : Set where

scienceDoesNotEqualAllKnowledge : ScienceEqualsKnowledge → ⊥
scienceDoesNotEqualAllKnowledge ()

proofDoesNotEqualObservation : FormalProofEqualsEmpiricalObservation → ⊥
proofDoesNotEqualObservation ()

institutionRecordDoesNotReplaceAffectedKnowledge : InstitutionalRecordEqualsAffectedSubjectKnowledge → ⊥
institutionRecordDoesNotReplaceAffectedKnowledge ()

indigenousKnowledgeDoesNotNeedScientificPromotion : IndigenousKnowledgeNeedsScientificPromotionToExist → ⊥
indigenousKnowledgeDoesNotNeedScientificPromotion ()

pluralityDoesNotMeanAllClaimsEqual : EpistemicPluralityMeansAllClaimsEqual → ⊥
pluralityDoesNotMeanAllClaimsEqual ()
