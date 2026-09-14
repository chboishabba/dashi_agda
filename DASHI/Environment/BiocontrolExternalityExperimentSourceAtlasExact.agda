module DASHI.Environment.BiocontrolExternalityExperimentSourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Source rows are deliberately narrow.  They record what a source is used for
-- in this formalisation; they do not import proof or authority.
------------------------------------------------------------------------

data SourceKind : Set where
  institutionalWebPage managementGuide literatureSource : SourceKind

record AttributedBiocontrolSource : Set where
  constructor attributedBiocontrolSource
  field
    authorOrInstitution : String
    title : String
    publication : String
    locator : String
    sourceKind : SourceKind
    formalisationRelationship : String
    citationImportsProof : Bool
    citationImportsProofIsFalse : citationImportsProof ≡ false
    citationCreatesDeploymentAuthority : Bool
    citationCreatesDeploymentAuthorityIsFalse : citationCreatesDeploymentAuthority ≡ false

open AttributedBiocontrolSource public

csiroHyacinthSource : AttributedBiocontrolSource
csiroHyacinthSource = attributedBiocontrolSource
  "CSIRO"
  "Water hyacinth"
  "CSIRO biological control resource"
  "https://ento.csiro.au/biocontrol/hyacinth.html"
  institutionalWebPage
  "historical Australian water-hyacinth biological-control programme and agent context"
  false refl false refl

australianManagementGuideSource : AttributedBiocontrolSource
australianManagementGuideSource = attributedBiocontrolSource
  "Commonwealth of Australia / contributing weed-management agencies"
  "Weed Management Guide - Water Hyacinth"
  "Weed of National Significance management guide"
  "user-supplied PDF; compiled by Andrew Petroeschevsky with listed contributors"
  managementGuide
  "control options; Neochetina damage/sinking mechanism; decomposition/dissolved-oxygen warning; integrated control; seedbank and nutrient context"
  false refl false refl

record SourceAtlasBoundary : Set where
  constructor sourceAtlasBoundary
  field
    sourceIdentityRetained : Bool
    sourceIdentityRetainedIsTrue : sourceIdentityRetained ≡ true
    formalisationRoleRetained : Bool
    formalisationRoleRetainedIsTrue : formalisationRoleRetained ≡ true
    sourceRoleEqualsEmpiricalProof : Bool
    sourceRoleEqualsEmpiricalProofIsFalse : sourceRoleEqualsEmpiricalProof ≡ false

canonicalSourceAtlasBoundary : SourceAtlasBoundary
canonicalSourceAtlasBoundary = sourceAtlasBoundary true refl true refl false refl
