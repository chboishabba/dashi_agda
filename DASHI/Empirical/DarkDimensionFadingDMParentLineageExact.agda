module DASHI.Empirical.DarkDimensionFadingDMParentLineageExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- FADING-DARK-MATTER PARENT / REANALYSIS LINEAGE
--
-- The 2021 Agrawal-Obied-Vafa model is a source-identified predecessor of the
-- 2025/26 Bedroya-Obied-Vafa-Wu reanalysis.  This records the genealogy while
-- refusing to turn model lineage into implementation, normalization or
-- numerical-manifest identity.
------------------------------------------------------------------------

parentSource : Source.AttributedSource
parentSource =
  Source.mkDOISource
    "Prateek Agrawal; Georges Obied; Cumrun Vafa"
    "H0 Tension, Swampland Conjectures and the Epoch of Fading Dark Matter"
    "Physical Review D 103, 043523"
    "2021"
    "10.1103/PhysRevD.103.043523"
    "https://doi.org/10.1103/PhysRevD.103.043523"
    Source.academicArticleSource
    "primary predecessor source for the fading-dark-matter proposal, its piecewise mass law, two-exponential quintessence potential, and modified CLASS plus MontePython analysis; citation imports neither the 2026 implementation nor normalization custody"
    Source.publicAttribution

parentArXiv : String
parentArXiv = "1906.08261"

childSource : Source.AttributedSource
childSource =
  Source.mkDOISource
    "Alek Bedroya; Georges Obied; Cumrun Vafa; David H. Wu"
    "Evolving Dark Sector and the Dark Dimension Scenario"
    "Physical Review D"
    "2026"
    "10.1103/1rsq-cv2m"
    "https://doi.org/10.1103/1rsq-cv2m"
    Source.academicArticleSource
    "source for the later dark-dimension reanalysis of the fading-dark-sector proposal using a locally exponential potential and mass law with CLASS and Cobaya; similarity/reanalysis does not establish same implementation or parameter manifest"
    Source.publicAttribution

childArXiv : String
childArXiv = "2507.03090"

parentMassLaw : String
parentMassLaw =
  "m(phi)=m0 before phi0; m(phi)=m0 exp[-cTilde (phi-phi0)] after phi0"

parentPotentialLaw : String
parentPotentialLaw =
  "V(phi)=B exp(-b phi)+C exp(-c phi), with B exp(-b phi0)=C exp(-c phi0), b~50"

childLocalMassLaw : String
childLocalMassLaw = "m_DM=m0 exp(-cPrime phi)"

childLocalPotentialLaw : String
childLocalPotentialLaw = "V=V0 exp(-c phi)"

record FadingDMParentLineageStatus : Set where
  constructor fadingDMParentLineageStatus
  field
    parentModelIdentified : Bool
    childReanalysisRelationshipLocated : Bool
    parentModifiedCLASSMontePythonLocated : Bool
    childCLASSCobayaLocated : Bool
    parentMassLawLocated : Bool
    parentPotentialLawLocated : Bool
    childLocalMassLawLocated : Bool
    childLocalPotentialLawLocated : Bool
    exactImplementationInheritanceDemonstrated : Bool
    normalizationInheritanceSameObject : Bool
    numericalManifestIdentityDemonstrated : Bool
    parentChainLocatedByCurrentSearch : Bool

open FadingDMParentLineageStatus public

canonicalFadingDMParentLineageStatus : FadingDMParentLineageStatus
canonicalFadingDMParentLineageStatus =
  fadingDMParentLineageStatus
    true true true true true true true true
    false false false false

parentImplementationInheritanceStillOpen :
  exactImplementationInheritanceDemonstrated canonicalFadingDMParentLineageStatus
  ≡ false
parentImplementationInheritanceStillOpen = refl

parentNormalizationInheritanceStillOpen :
  normalizationInheritanceSameObject canonicalFadingDMParentLineageStatus
  ≡ false
parentNormalizationInheritanceStillOpen = refl

parentNumericalManifestIdentityStillOpen :
  numericalManifestIdentityDemonstrated canonicalFadingDMParentLineageStatus
  ≡ false
parentNumericalManifestIdentityStillOpen = refl

parentChainStillUnlocatedByCurrentSearch :
  parentChainLocatedByCurrentSearch canonicalFadingDMParentLineageStatus ≡ false
parentChainStillUnlocatedByCurrentSearch = refl

------------------------------------------------------------------------
-- WrongType / same-object firewalls.
------------------------------------------------------------------------

data ParentLineageEqualsImplementationIdentity : Set where

data ParentNormalizationPaysChildNormalization : Set where

data SameProposalFamilyMeansSameNumericalManifest : Set where

data ParentMassLawEqualsChildLocalMassLaw : Set where

data ParentPotentialLawEqualsChildLocalPotentialLaw : Set where

parentLineageDoesNotEqualImplementationIdentity :
  ParentLineageEqualsImplementationIdentity → ⊥
parentLineageDoesNotEqualImplementationIdentity ()

parentNormalizationDoesNotAutoPayChildNormalization :
  ParentNormalizationPaysChildNormalization → ⊥
parentNormalizationDoesNotAutoPayChildNormalization ()

sameProposalFamilyDoesNotMeanSameNumericalManifest :
  SameProposalFamilyMeansSameNumericalManifest → ⊥
sameProposalFamilyDoesNotMeanSameNumericalManifest ()

parentMassLawDiffersFromChildLocalMassLaw :
  ParentMassLawEqualsChildLocalMassLaw → ⊥
parentMassLawDiffersFromChildLocalMassLaw ()

parentPotentialLawDiffersFromChildLocalPotentialLaw :
  ParentPotentialLawEqualsChildLocalPotentialLaw → ⊥
parentPotentialLawDiffersFromChildLocalPotentialLaw ()
