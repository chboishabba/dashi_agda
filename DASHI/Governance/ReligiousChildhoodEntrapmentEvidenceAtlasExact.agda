module DASHI.Governance.ReligiousChildhoodEntrapmentEvidenceAtlasExact where

------------------------------------------------------------------------
-- RELIGIOUS-CHILDHOOD ENTRAPMENT EVIDENCE ATLAS
--
-- This module narrows the remaining empirical seam in the John-paper lane.
-- It does NOT promote ordinary religious upbringing to coercion or trauma.
-- Instead it records source-specific evidence for particular coordinates:
-- family relational cost, religious conflict, parental warmth, hell fear,
-- authority/submission, exit/deidentification, and developmental timing.
--
-- SOURCES / BOUNDED ROLES
--
-- Charles E. Stokes; Mark D. Regnerus,
-- "When faith divides family: religious discord and adolescent reports of
-- parent-child relations", Social Science Research 38(1):155-167 (2009),
-- DOI 10.1016/j.ssresearch.2008.05.002.
-- Bounded role: adolescent parent-child religious discord is associated with
-- lower reported relationship quality, especially when parents value religion
-- more highly than adolescents. Association != coercion or entrapment.
--
-- Justin J. Hendricks; Sam A. Hardy; Emily M. Taylor; David C. Dollahite,
-- "Does Leaving Faith Mean Leaving Family? Longitudinal Associations Between
-- Religious Identification and Parent-Child Relationships Across Adolescence
-- and Emerging Adulthood", Journal for the Scientific Study of Religion
-- 63:23-41 (2024), DOI 10.1111/jssr.12876.
-- Bounded role: longitudinal evidence that adolescent deconversion can predict
-- poorer parent-child relationship quality; not a theorem that all families
-- penalise refusal or that religion itself causes the change.
--
-- Justin Hendricks; Sam A. Hardy; Michael A. Goodman;
-- Emily de Schweinitz Taylor,
-- "Longitudinal Associations and Interactions of Adolescent Religious
-- Deidentification and Parental Sanctification on Parent-Adolescent
-- Relationships", International Journal for the Psychology of Religion
-- (2025), DOI 10.1080/10508619.2025.2521897.
-- Bounded role: N=1,391 parent-child dyads; deidentification associated with
-- increased religious conflict and short-term decreases in adolescent-reported
-- parental warmth. Parental sanctification was also associated with warmth and
-- only partially with increased conflict: the source is not one-directional.
--
-- Patricia Richards; Ashleigh McKinzie; Jasmine Underwood,
-- "From Embodied Contradictions to Self-Authorship: Survivors of Abuse Leaving
-- Evangelical Churches", Qualitative Sociology 49:293-316 (2026),
-- DOI 10.1007/s11133-025-09629-6.
-- Bounded role: qualitative interviews with 33 adult survivors of abuse in
-- white evangelical contexts; documents retrospective childhood hell fear,
-- authority/submission, restricted self-trust and difficult exit in this
-- selected survivor population. It is not a Catholic-childhood prevalence
-- estimate and not evidence about ordinary religious formation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

record SourceReceipt : Set where
  constructor sourceReceipt
  field
    authors : String
    title : String
    venue : String
    year : Nat
    doi : String
    boundedRole : String

open SourceReceipt public

data EvidenceFacet : Set where
  familyRelationshipQuality : EvidenceFacet
  religiousConflict : EvidenceFacet
  parentalWarmth : EvidenceFacet
  deidentificationExit : EvidenceFacet
  hellFear : EvidenceFacet
  authoritySubmission : EvidenceFacet
  restrictedSelfTrust : EvidenceFacet
  developmentalTiming : EvidenceFacet

data PopulationMatch : Set where
  adolescentReligiousFamilies : PopulationMatch
  adolescentDeidentificationLongitudinal : PopulationMatch
  evangelicalAbuseSurvivorsRetrospective : PopulationMatch
  catholicChildhoodDirect : PopulationMatch

data EvidenceMode : Set where
  longitudinalAssociation : EvidenceMode
  crossSectionalAssociation : EvidenceMode
  qualitativeMechanism : EvidenceMode
  directPopulationInstantiation : EvidenceMode

record FacetEvidence : Set where
  constructor facetEvidence
  field
    source : SourceReceipt
    facet : EvidenceFacet
    population : PopulationMatch
    mode : EvidenceMode
    supportsFacetInPopulation : Bool
    establishesCoercion : Bool
    establishesEntrapment : Bool
    establishesCatholicChildhoodGeneralisation : Bool

open FacetEvidence public

stokesRegnerus : SourceReceipt
stokesRegnerus = sourceReceipt
  "Charles E. Stokes; Mark D. Regnerus"
  "When faith divides family: religious discord and adolescent reports of parent-child relations"
  "Social Science Research 38(1):155-167"
  2009
  "10.1016/j.ssresearch.2008.05.002"
  "adolescent religious discord and reported parent-child relationship quality; association only"

hendricksHardyTaylorDollahite2024 : SourceReceipt
hendricksHardyTaylorDollahite2024 = sourceReceipt
  "Justin J. Hendricks; Sam A. Hardy; Emily M. Taylor; David C. Dollahite"
  "Does Leaving Faith Mean Leaving Family? Longitudinal Associations Between Religious Identification and Parent-Child Relationships Across Adolescence and Emerging Adulthood"
  "Journal for the Scientific Study of Religion 63:23-41"
  2024
  "10.1111/jssr.12876"
  "longitudinal deconversion / parent-child relationship evidence; no universal coercion inference"

hendricksHardyGoodmanTaylor2025 : SourceReceipt
hendricksHardyGoodmanTaylor2025 = sourceReceipt
  "Justin Hendricks; Sam A. Hardy; Michael A. Goodman; Emily de Schweinitz Taylor"
  "Longitudinal Associations and Interactions of Adolescent Religious Deidentification and Parental Sanctification on Parent-Adolescent Relationships"
  "International Journal for the Psychology of Religion"
  2025
  "10.1080/10508619.2025.2521897"
  "N=1,391 parent-child dyads; deidentification, religious conflict and parental warmth; mixed-direction parental-sanctification findings retained"

richardsMcKinzieUnderwood2026 : SourceReceipt
richardsMcKinzieUnderwood2026 = sourceReceipt
  "Patricia Richards; Ashleigh McKinzie; Jasmine Underwood"
  "From Embodied Contradictions to Self-Authorship: Survivors of Abuse Leaving Evangelical Churches"
  "Qualitative Sociology 49:293-316"
  2026
  "10.1007/s11133-025-09629-6"
  "selected adult abuse-survivor interviews in white evangelical contexts; retrospective hell-fear / authority / exit mechanisms, not Catholic-childhood prevalence"

religiousDiscordRelationshipEvidence : FacetEvidence
religiousDiscordRelationshipEvidence = facetEvidence
  stokesRegnerus familyRelationshipQuality adolescentReligiousFamilies
  crossSectionalAssociation true false false false

deconversionRelationshipEvidence : FacetEvidence
deconversionRelationshipEvidence = facetEvidence
  hendricksHardyTaylorDollahite2024 deidentificationExit
  adolescentDeidentificationLongitudinal longitudinalAssociation
  true false false false

religiousConflictEvidence : FacetEvidence
religiousConflictEvidence = facetEvidence
  hendricksHardyGoodmanTaylor2025 religiousConflict
  adolescentDeidentificationLongitudinal longitudinalAssociation
  true false false false

parentalWarmthEvidence : FacetEvidence
parentalWarmthEvidence = facetEvidence
  hendricksHardyGoodmanTaylor2025 parentalWarmth
  adolescentDeidentificationLongitudinal longitudinalAssociation
  true false false false

hellFearMechanismEvidence : FacetEvidence
hellFearMechanismEvidence = facetEvidence
  richardsMcKinzieUnderwood2026 hellFear
  evangelicalAbuseSurvivorsRetrospective qualitativeMechanism
  true false false false

authoritySubmissionMechanismEvidence : FacetEvidence
authoritySubmissionMechanismEvidence = facetEvidence
  richardsMcKinzieUnderwood2026 authoritySubmission
  evangelicalAbuseSurvivorsRetrospective qualitativeMechanism
  true false false false

restrictedSelfTrustMechanismEvidence : FacetEvidence
restrictedSelfTrustMechanismEvidence = facetEvidence
  richardsMcKinzieUnderwood2026 restrictedSelfTrust
  evangelicalAbuseSurvivorsRetrospective qualitativeMechanism
  true false false false

------------------------------------------------------------------------
-- The atlas therefore closes several mechanism/family-relation coordinates,
-- but intentionally leaves the exact Catholic-childhood instantiation open.
------------------------------------------------------------------------

data PartialFacetEvidencePromotesCompleteCatholicInstantiation : Set where

data ReligiousDiscordPromotesCoercion : Set where

data SurvivorMechanismPromotesPopulationPrevalence : Set where

partialFacetEvidenceDoesNotCompleteCatholicInstantiation :
  PartialFacetEvidencePromotesCompleteCatholicInstantiation → ⊥
partialFacetEvidenceDoesNotCompleteCatholicInstantiation ()

religiousDiscordDoesNotPromoteCoercion : ReligiousDiscordPromotesCoercion → ⊥
religiousDiscordDoesNotPromoteCoercion ()

survivorMechanismDoesNotPromotePopulationPrevalence :
  SurvivorMechanismPromotesPopulationPrevalence → ⊥
survivorMechanismDoesNotPromotePopulationPrevalence ()

record ReligiousChildhoodEvidenceBoundary : Set where
  constructor religiousChildhoodEvidenceBoundary
  field
    familyRelationalCostCoordinateHasEvidence : Bool
    adolescentExitConflictCoordinateHasEvidence : Bool
    hellFearMechanismHasSelectedPopulationEvidence : Bool
    authoritySubmissionHasSelectedPopulationEvidence : Bool
    catholicChildhoodDirectInstantiationInstalled : Bool
    ordinaryReligiousFormationEqualsEntrapment : Bool
    associationEqualsCoercion : Bool
    survivorSampleEqualsPopulationPrevalence : Bool

canonicalReligiousChildhoodEvidenceBoundary : ReligiousChildhoodEvidenceBoundary
canonicalReligiousChildhoodEvidenceBoundary =
  religiousChildhoodEvidenceBoundary true true true true false false false false
