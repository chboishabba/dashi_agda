module DASHI.Education.DigitalESDEducationSustainabilityLiteratureMapExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball

------------------------------------------------------------------------
-- DIGITAL-ESD EDUCATION/SUSTAINABILITY LITERATURE OBSERVER MAP
--
-- These sources observe different objects. They are not flattened into a
-- single "digital sustainability evidence" bucket:
--   1. technology used as a pedagogical tool for sustainability learning;
--   2. technology itself treated as a sustainability object/problem;
--   3. sustainability embedded inside computing/technology education;
--   4. environmental footprint of educational digital infrastructure/GenAI.
--
-- All four are acquisition candidates/source-role payments only. Inclusion in
-- the manuscript evidence synthesis still requires the structured-search,
-- eligibility and extraction workflow declared elsewhere.
------------------------------------------------------------------------

data LiteratureObserver : Set where
  technologyAsPedagogicalTool : LiteratureObserver
  technologyAsSustainabilityObject : LiteratureObserver
  sustainabilityInsideComputingEducation : LiteratureObserver
  educationalDigitalInfrastructureFootprint : LiteratureObserver

canonicalLiteratureObserverFamily : List LiteratureObserver
canonicalLiteratureObserverFamily =
  technologyAsPedagogicalTool
  ∷ technologyAsSustainabilityObject
  ∷ sustainabilityInsideComputingEducation
  ∷ educationalDigitalInfrastructureFootprint
  ∷ []

hajjHassanDigitalToolsReviewSource : Attr.AttributedSource
hajjHassanDigitalToolsReviewSource =
  Attr.mkDOISource
    "Mira Hajj-Hassan; Rawad Chaker; Anne-Marie Cederqvist"
    "Environmental Education: A Systematic Review on the Use of Digital Tools for Fostering Sustainability Awareness"
    "Sustainability 16(9), 3733"
    "2024"
    "10.3390/su16093733"
    "https://doi.org/10.3390/su16093733"
    Attr.academicArticleSource
    "Systematic-review source on digital tools used to foster environmental/sustainability awareness across K-12 and higher-education studies. It observes technology primarily as pedagogical means; it does not establish the sustainability of the technologies themselves."
    Attr.publicAttribution

andersenCompulsoryTechnologyESDSource : Attr.AttributedSource
andersenCompulsoryTechnologyESDSource =
  Attr.mkDOISource
    "Lars Bo Andersen; Aabo Jette Frydendahl; Sanne Lisborg; Jesper Juellund Jensen; Jakob Damgaard Laursen; Claes Weise Schiermer Mørkeberg; Camilla Balslev Nielsen; Vibeke Schrøder"
    "Technology education for sustainable development– a scoping review"
    "International Journal of Technology and Design Education 36, 1425-1443"
    "2026"
    "10.1007/s10798-025-10043-w"
    "https://doi.org/10.1007/s10798-025-10043-w"
    Attr.academicArticleSource
    "Compulsory-education scoping review mapping digital technologies both as tools/solutions for sustainable development and as objects/problems that can themselves challenge sustainability. Population and review scope remain compulsory education; no automatic transfer to higher education or Alice Brown's context."
    Attr.publicAttribution

petersComputingEducationReviewSource : Attr.AttributedSource
petersComputingEducationReviewSource =
  Attr.mkDOISource
    "Anne-Kathrin Peters; Rafael Capilla; Vlad Constantin Coroamă; Rogardt Heldal; Patricia Lago; Ola Leifler; Ana Moreira; João Paulo Fernandes; Birgit Penzenstadler; Jari Porras; Colin C. Venters"
    "Sustainability in Computing Education: A Systematic Literature Review"
    "ACM Transactions on Computing Education 24(1), Article 13"
    "2024"
    "10.1145/3639060"
    "https://doi.org/10.1145/3639060"
    Attr.academicArticleSource
    "Systematic literature review of sustainability in computing education: 572 publications screened across six digital libraries plus snowballing, 89 primary studies analysed. It supports a computing-curriculum/pedagogy evidence map and reports limited empirical maturity; it does not establish effects for general digital education or this proposed manuscript population."
    Attr.publicAttribution

radovanGenAIEducationEnvironmentSource : Attr.AttributedSource
radovanGenAIEducationEnvironmentSource =
  Attr.mkDOISource
    "Marko Radovan; Tadej Košmerl; Danijela Makovec Radovan"
    "Environmental Impacts of Generative AI in Education: A Systematic Review of Educational and Technical Evidence"
    "Sustainability 18(14), 7213"
    "2026"
    "10.3390/su18147213"
    "https://doi.org/10.3390/su18147213"
    Attr.academicArticleSource
    "Education-specific GenAI environmental-impact review covering electricity, greenhouse-gas emissions, water use, hardware manufacture and e-waste evidence/measurement approaches. It is evidence about GenAI-related infrastructure impacts, not an impact inventory for the proposed digital-ESD intervention."
    Attr.publicAttribution

canonicalLiteratureMapSourceAtlas : Attr.AttributedSourceAtlas
canonicalLiteratureMapSourceAtlas =
  Attr.mkSourceAtlas
    "digital ESD education/sustainability observer-map sources"
    "DASHI.Education.DigitalESDEducationSustainabilityLiteratureMapExact"
    ( hajjHassanDigitalToolsReviewSource
    ∷ andersenCompulsoryTechnologyESDSource
    ∷ petersComputingEducationReviewSource
    ∷ radovanGenAIEducationEnvironmentSource
    ∷ []
    )
    "Four distinct literature observers are retained without flattening tool-for-ESD, technology-as-object, computing-curriculum sustainability, and educational-infrastructure footprint into one evidence role. Acquisition does not equal manuscript inclusion."

hajjHassanSourceRoleReceipt :
  Snowball.SourceRoleSnowballReceipt hajjHassanDigitalToolsReviewSource
hajjHassanSourceRoleReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt hajjHassanDigitalToolsReviewSource

andersenSourceRoleReceipt :
  Snowball.SourceRoleSnowballReceipt andersenCompulsoryTechnologyESDSource
andersenSourceRoleReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt andersenCompulsoryTechnologyESDSource

petersSourceRoleReceipt :
  Snowball.SourceRoleSnowballReceipt petersComputingEducationReviewSource
petersSourceRoleReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt petersComputingEducationReviewSource

radovanSourceRoleReceipt :
  Snowball.SourceRoleSnowballReceipt radovanGenAIEducationEnvironmentSource
radovanSourceRoleReceipt =
  Snowball.canonicalSourceRoleSnowballReceipt radovanGenAIEducationEnvironmentSource

record DigitalESDLiteratureMap : Set where
  constructor digital-esd-literature-map
  field
    attributedSources : Attr.AttributedSourceAtlas
    observerFamily : List LiteratureObserver

    digitalToolEnvironmentalEducationReviewPaid : Bool
    digitalToolEnvironmentalEducationReviewPaidIsTrue :
      digitalToolEnvironmentalEducationReviewPaid ≡ true

    compulsoryEducationScopingReviewPaid : Bool
    compulsoryEducationScopingReviewPaidIsTrue :
      compulsoryEducationScopingReviewPaid ≡ true

    computingEducationSystematicReviewPaid : Bool
    computingEducationSystematicReviewPaidIsTrue :
      computingEducationSystematicReviewPaid ≡ true

    genAIEducationEnvironmentalReviewPaid : Bool
    genAIEducationEnvironmentalReviewPaidIsTrue :
      genAIEducationEnvironmentalReviewPaid ≡ true

    observerRolesRemainDistinct : Bool
    observerRolesRemainDistinctIsTrue : observerRolesRemainDistinct ≡ true

    acquiredSourcesAreCandidateForSynthesis : Bool
    acquiredSourcesAreCandidateForSynthesisIsTrue :
      acquiredSourcesAreCandidateForSynthesis ≡ true

    acquiredSourcesAreIncludedStudies : Bool
    acquiredSourcesAreIncludedStudiesIsFalse :
      acquiredSourcesAreIncludedStudies ≡ false

    populationTransferIsAutomatic : Bool
    populationTransferIsAutomaticIsFalse : populationTransferIsAutomatic ≡ false

    citationImportsProof : Bool
    citationImportsProofIsFalse : citationImportsProof ≡ false

    citationCreatesAuthority : Bool
    citationCreatesAuthorityIsFalse : citationCreatesAuthority ≡ false

open DigitalESDLiteratureMap public

canonicalDigitalESDLiteratureMap : DigitalESDLiteratureMap
canonicalDigitalESDLiteratureMap =
  digital-esd-literature-map
    canonicalLiteratureMapSourceAtlas
    canonicalLiteratureObserverFamily
    true refl
    true refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- No-promotion / population / observer boundaries.
------------------------------------------------------------------------

data TechnologyUsedForSustainabilityTeachingProvesSustainableTechnology : Set where

data CompulsoryEducationEvidenceAutomaticallyTransfersToHigherEducation : Set where

data SourceAcquisitionCreatesPaperInclusion : Set where

data ComputingEducationReviewDeterminesGeneralDigitalEducation : Set where

data GenAIReviewPaysAllDigitalInfrastructureImpact : Set where

data LiteratureObserversMayBeFlattenedWithoutResidual : Set where

technologyUsedForSustainabilityTeachingDoesNotProveSustainableTechnology :
  TechnologyUsedForSustainabilityTeachingProvesSustainableTechnology → ⊥
technologyUsedForSustainabilityTeachingDoesNotProveSustainableTechnology ()

compulsoryEducationEvidenceDoesNotAutomaticallyTransferToHigherEducation :
  CompulsoryEducationEvidenceAutomaticallyTransfersToHigherEducation → ⊥
compulsoryEducationEvidenceDoesNotAutomaticallyTransferToHigherEducation ()

sourceAcquisitionDoesNotCreatePaperInclusion :
  SourceAcquisitionCreatesPaperInclusion → ⊥
sourceAcquisitionDoesNotCreatePaperInclusion ()

computingEducationReviewDoesNotDetermineGeneralDigitalEducation :
  ComputingEducationReviewDeterminesGeneralDigitalEducation → ⊥
computingEducationReviewDoesNotDetermineGeneralDigitalEducation ()

genAIReviewDoesNotPayAllDigitalInfrastructureImpact :
  GenAIReviewPaysAllDigitalInfrastructureImpact → ⊥
genAIReviewDoesNotPayAllDigitalInfrastructureImpact ()

literatureObserversMustRetainResidualDifferences :
  LiteratureObserversMayBeFlattenedWithoutResidual → ⊥
literatureObserversMustRetainResidualDifferences ()
