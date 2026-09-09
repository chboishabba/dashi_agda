module DASHI.Law.SensibLawWoogarooPreservationSourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Law.SensibLawWoogarooPreservationLegalCutsetExact as Cutset
import DASHI.Cognition.PNF.SensibLawLegalClaimProvenanceLineageExact as Lineage

------------------------------------------------------------------------
-- WOOGAROO PRESERVATION SOURCE ATLAS
--
-- Source identity is kept distinct from repository application.  These source
-- entries establish who/what said what and where.  They do not themselves
-- prove that any Queensland or Commonwealth statutory test is satisfied.
------------------------------------------------------------------------

qldNatureConservationAct : Source.AttributedSource
qldNatureConservationAct = Source.mkNoDOISource
  "Queensland Parliament"
  "Nature Conservation Act 1992 (Qld)"
  "Queensland legislation"
  "1992"
  "https://www.legislation.qld.gov.au/view/html/inforce/current/act-1992-020"
  Source.governmentSource
  "Primary legal authority for critical habitat, nature-refuge, interim-conservation-order and enforcement mechanisms; exact section application remains a separate DASHI reconstruction/application step."
  Source.publicAttribution

epbcAct : Source.AttributedSource
epbcAct = Source.mkNoDOISource
  "Commonwealth Parliament"
  "Environment Protection and Biodiversity Conservation Act 1999 (Cth)"
  "Federal Register of Legislation"
  "1999"
  "https://www.legislation.gov.au/C2004A00485/latest/text"
  Source.governmentSource
  "Primary legal authority for threatened-species/community controlled-action, approval and injunction mechanisms."
  Source.publicAttribution

scenicPreliminaryDocumentation : Source.AttributedSource
scenicPreliminaryDocumentation = Source.mkNoDOISource
  "Springfield City Group Pty Ltd / EPBC public portal"
  "Scenic Precinct, Springfield, Queensland — EPBC 2020/8651 Preliminary Documentation"
  "EPBC Act Public Portal"
  "2025"
  "https://epbcpublicportal.environment.gov.au/_entity/sharepointdocumentlocation/b5c4d2d2-dfeb-ee11-a1fe-000d3acb1769/2ab10dab-d681-4911-b881-cc99413f07b6?file=2020-8651-Draft-PD.pdf"
  Source.governmentSource
  "Project-specific source for referred-action identity, controlling provisions and ecological impact evidence; proponent/ecology assertions remain distinct from legal findings."
  Source.publicAttribution

springviewCouncilDecision : Source.AttributedSource
springviewCouncilDecision = Source.mkNoDOISource
  "Ipswich City Council"
  "Approval for Springview Village 2 and 3 Precinct Plan"
  "Ipswich City Council"
  "2024"
  "https://www.ipswich.qld.gov.au/News-Articles-Folder/2024/Approval-for-Springview-Village-2-and-3-Precinct-Plan"
  Source.governmentSource
  "Council source recording approval, mapped koala habitat across the proposal area, the asserted exempted-development status, and retained/open-space amendments."
  Source.publicAttribution

springviewDevelopmentIRecord : Source.AttributedSource
springviewDevelopmentIRecord = Source.mkNoDOISource
  "Ipswich City Council"
  "6243/2023/LAP — Springview Village 2 and Village 3 Precinct Plan"
  "Development.i"
  "2024"
  "https://developmenti.ipswich.qld.gov.au/Home/ApplicationDetailsView?appNo=6243%2F2023%2FLAP&type=plan_development_apps"
  Source.governmentSource
  "Primary local-government procedural record showing the application as decided/approved; does not itself establish Commonwealth approval or permanent habitat protection."
  Source.publicAttribution

woogarooPreservationSources : List Source.AttributedSource
woogarooPreservationSources =
  qldNatureConservationAct ∷
  epbcAct ∷
  scenicPreliminaryDocumentation ∷
  springviewCouncilDecision ∷
  springviewDevelopmentIRecord ∷
  []

woogarooPreservationAtlas : Source.AttributedSourceAtlas
woogarooPreservationAtlas = Source.mkSourceAtlas
  "Woogaroo Forest preservation legal/ecological source atlas"
  "DASHI.Law.SensibLawWoogarooPreservationSourceAtlasExact"
  woogarooPreservationSources
  "Primary legislation and primary/public project records needed to test legal mechanisms capable of restraining or preventing habitat loss."

------------------------------------------------------------------------
-- Exact source propositions currently safe to carry.
------------------------------------------------------------------------

data SourceProposition : Set where
  scenicControlledActionThreatenedSpecies : SourceProposition
  scenicKoalaControllingProvision : SourceProposition
  scenicGreyHeadedFlyingFoxControllingProvision : SourceProposition
  scenicSwiftParrotControllingProvision : SourceProposition
  scenicRegentHoneyeaterControllingProvision : SourceProposition
  scenicCommentPeriodExtended : SourceProposition
  springviewAreaMappedKoalaHabitat : SourceProposition
  springviewCouncilApproved : SourceProposition
  springviewCouncilStatesExemptedDevelopment : SourceProposition

data PropositionStatus : Set where
  externalRecordPaid : PropositionStatus
  repositoryApplicationOpen : PropositionStatus
  externalAdjudicationOpen : PropositionStatus

record AttributedWoogarooFact : Set where
  constructor attributed-woogaroo-fact
  field
    proposition : SourceProposition
    source : Source.AttributedSource
    exactLocator : String
    boundedStatement : String
    status : PropositionStatus
    sourceIdentityImportsTruth : Bool
    sourceIdentityImportsTruthIsFalse : sourceIdentityImportsTruth ≡ false

open AttributedWoogarooFact public

scenicControlledActionFact : AttributedWoogarooFact
scenicControlledActionFact = attributed-woogaroo-fact
  scenicControlledActionThreatenedSpecies
  scenicPreliminaryDocumentation
  "Invitation for Public Comment / controlling provisions"
  "The Scenic Precinct proposal was determined a controlled action under the EPBC Act, assessed by Preliminary Documentation, with listed threatened species and communities as controlling provisions."
  externalRecordPaid
  false refl

scenicKoalaFact : AttributedWoogarooFact
scenicKoalaFact = attributed-woogaroo-fact
  scenicKoalaControllingProvision
  scenicPreliminaryDocumentation
  "Invitation for Public Comment / controlling provisions"
  "The federal project material names the koala among the listed threatened species relevant to the Scenic controlled action."
  externalRecordPaid
  false refl

scenicFlyingFoxFact : AttributedWoogarooFact
scenicFlyingFoxFact = attributed-woogaroo-fact
  scenicGreyHeadedFlyingFoxControllingProvision
  scenicPreliminaryDocumentation
  "Invitation for Public Comment / controlling provisions"
  "The federal project material names the grey-headed flying-fox among the listed threatened species relevant to the Scenic controlled action."
  externalRecordPaid
  false refl

scenicSwiftParrotFact : AttributedWoogarooFact
scenicSwiftParrotFact = attributed-woogaroo-fact
  scenicSwiftParrotControllingProvision
  scenicPreliminaryDocumentation
  "Invitation for Public Comment / controlling provisions"
  "The federal project material names the swift parrot among the listed threatened species relevant to the Scenic controlled action."
  externalRecordPaid
  false refl

scenicRegentHoneyeaterFact : AttributedWoogarooFact
scenicRegentHoneyeaterFact = attributed-woogaroo-fact
  scenicRegentHoneyeaterControllingProvision
  scenicPreliminaryDocumentation
  "Invitation for Public Comment / controlling provisions"
  "The federal project material names the regent honeyeater among the listed threatened species relevant to the Scenic controlled action."
  externalRecordPaid
  false refl

scenicExtensionFact : AttributedWoogarooFact
scenicExtensionFact = attributed-woogaroo-fact
  scenicCommentPeriodExtended
  scenicPreliminaryDocumentation
  "Invitation for Public Comment"
  "The public-comment period was extended to January 2026 because a security setting may have blocked an unknown number of submissions."
  externalRecordPaid
  false refl

springviewKoalaMapFact : AttributedWoogarooFact
springviewKoalaMapFact = attributed-woogaroo-fact
  springviewAreaMappedKoalaHabitat
  springviewCouncilDecision
  "Council public statement"
  "Ipswich City Council stated that the entire Springview Village 2/3 proposal area is mapped for koala habitat."
  externalRecordPaid
  false refl

springviewApprovalFact : AttributedWoogarooFact
springviewApprovalFact = attributed-woogaroo-fact
  springviewCouncilApproved
  springviewDevelopmentIRecord
  "Application 6243/2023/LAP — Stage/Decision"
  "Council's Development.i record lists the Springview Village 2/3 precinct-plan application as decided and approved."
  externalRecordPaid
  false refl

springviewExemptionFact : AttributedWoogarooFact
springviewExemptionFact = attributed-woogaroo-fact
  springviewCouncilStatesExemptedDevelopment
  springviewCouncilDecision
  "Council public statement"
  "Council stated that, despite the whole proposal area being mapped koala habitat, the development was considered exempted development under the relevant legislation."
  externalRecordPaid
  false refl

------------------------------------------------------------------------
-- Consumer-indexed legal application.  Source-paid facts may be relevant to a
-- statutory test without themselves satisfying that test.
------------------------------------------------------------------------

data StatutoryConsumer : Set where
  ncaS13CriticalHabitatConsumer : StatutoryConsumer
  ncaS49NatureRefugeConsumer : StatutoryConsumer
  ncaS102InterimOrderConsumer : StatutoryConsumer
  epbcS18SignificantImpactConsumer : StatutoryConsumer
  epbcPart9RefusalConsumer : StatutoryConsumer
  qldKoalaPlanningConstraintConsumer : StatutoryConsumer

data RelevanceState : Set where
  directlyRelevant : RelevanceState
  potentiallyRelevant : RelevanceState
  notEnoughByItself : RelevanceState

record FactConsumerApplication : Set where
  constructor fact-consumer-application
  field
    fact : AttributedWoogarooFact
    consumer : StatutoryConsumer
    relevance : RelevanceState
    applicationStatement : String
    sourceFactAutomaticallyPaysConsumer : Bool
    sourceFactAutomaticallyPaysConsumerIsFalse :
      sourceFactAutomaticallyPaysConsumer ≡ false

open FactConsumerApplication public

scenicKoalaToEPBC : FactConsumerApplication
scenicKoalaToEPBC = fact-consumer-application
  scenicKoalaFact
  epbcS18SignificantImpactConsumer
  directlyRelevant
  "The koala controlling-provision fact belongs in the Scenic s 18/18A impact analysis, but the mere naming of a controlling provision does not itself prove the final significant-impact conclusion."
  false refl

scenicBirdsToRefusal : FactConsumerApplication
scenicBirdsToRefusal = fact-consumer-application
  scenicSwiftParrotFact
  epbcPart9RefusalConsumer
  directlyRelevant
  "Swift-parrot evidence belongs in the Part 9 approval/refusal decision record; its legal weight depends on the complete assessment material and applicable statutory decision constraints."
  false refl

springviewKoalaToNCA13 : FactConsumerApplication
springviewKoalaToNCA13 = fact-consumer-application
  springviewKoalaMapFact
  ncaS13CriticalHabitatConsumer
  potentiallyRelevant
  "Mapped koala habitat is evidence relevant to the Queensland critical-habitat inquiry, but mapped habitat does not by itself establish that the habitat is essential for conservation of a viable population as required by the s 13 consumer."
  false refl

springviewExemptionToPlanning : FactConsumerApplication
springviewExemptionToPlanning = fact-consumer-application
  springviewExemptionFact
  qldKoalaPlanningConstraintConsumer
  directlyRelevant
  "The asserted exemption is a live defeater/exception coordinate for ordinary koala-planning protection and must be source-tested rather than erased by the fact that koala habitat is mapped."
  false refl

------------------------------------------------------------------------
-- Intersectional / WrongType non-factorability: a coarse habitat label cannot
-- recover the complete legal outcome because exemptions, jurisdiction,
-- statutory definition, procedural state and decision-maker discretion are
-- separate coordinates.
------------------------------------------------------------------------

data FineLegalState : Set where
  mappedHabitatExemptPlanningState : FineLegalState
  mappedHabitatNonExemptPlanningState : FineLegalState

data HabitatSurface : Set where
  mappedKoalaHabitatSurface : HabitatSurface

data PlanningLegalOutcome : Set where
  ordinaryKoalaConstraintAvailable : PlanningLegalOutcome
  ordinaryKoalaConstraintDefeatedByExemption : PlanningLegalOutcome

habitatObserver : FineLegalState → HabitatSurface
habitatObserver _ = mappedKoalaHabitatSurface

planningOutcome : FineLegalState → PlanningLegalOutcome
planningOutcome mappedHabitatExemptPlanningState = ordinaryKoalaConstraintDefeatedByExemption
planningOutcome mappedHabitatNonExemptPlanningState = ordinaryKoalaConstraintAvailable

planningOutcomeDiffers :
  planningOutcome mappedHabitatExemptPlanningState ≡
  planningOutcome mappedHabitatNonExemptPlanningState → ⊥
planningOutcomeDiffers ()

mappedHabitatCannotRecoverPlanningOutcome :
  INF.FactorsThrough habitatObserver planningOutcome → ⊥
mappedHabitatCannotRecoverPlanningOutcome =
  INF.witnessRulesOutEveryFlatFactorisation
    (INF.nonFactorabilityWitness
      mappedHabitatExemptPlanningState
      mappedHabitatNonExemptPlanningState
      refl
      planningOutcomeDiffers)

------------------------------------------------------------------------
-- Procedural-delay firewall.  The sourced Scenic event recovered here is a
-- public-comment extension, not a development-refusal or habitat-protection
-- event.  Any other claimed project delay remains source-open until its exact
-- carrier is attached.
------------------------------------------------------------------------

data CommentExtensionEqualsProjectRefusal : Set where
data CommentExtensionEqualsPermanentProtection : Set where

data UnsourcedDelayMayBePromotedToPrimaryRecord : Set where

commentExtensionDoesNotEqualRefusal : CommentExtensionEqualsProjectRefusal → ⊥
commentExtensionDoesNotEqualRefusal ()

commentExtensionDoesNotEqualPermanentProtection :
  CommentExtensionEqualsPermanentProtection → ⊥
commentExtensionDoesNotEqualPermanentProtection ()

unsourcedDelayCannotBePromotedToPrimaryRecord :
  UnsourcedDelayMayBePromotedToPrimaryRecord → ⊥
unsourcedDelayCannotBePromotedToPrimaryRecord ()

record PreservationSourceAtlasBoundary : Set where
  constructor preservation-source-atlas-boundary
  field
    sourceIdentitySeparatedFromApplication : Bool
    proponentMaterialSeparatedFromLegalFinding : Bool
    habitatMappingSeparatedFromCriticalHabitatFinding : Bool
    planningApprovalSeparatedFromFederalApproval : Bool
    proceduralExtensionSeparatedFromProtection : Bool
    exemptionsRetainedAsLegalCoordinates : Bool
    attributionCreatesLegalAuthority : Bool

canonicalPreservationSourceAtlasBoundary : PreservationSourceAtlasBoundary
canonicalPreservationSourceAtlasBoundary =
  preservation-source-atlas-boundary
    true true true true true true false
