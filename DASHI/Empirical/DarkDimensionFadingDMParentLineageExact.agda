module DASHI.Empirical.DarkDimensionFadingDMParentLineageExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source

------------------------------------------------------------------------
-- FADING-DARK-MATTER PARENT / REANALYSIS LINEAGE
--
-- 2018: quintessence-potential parameterization ancestor.
-- 2021: fading-dark-matter parent proposal / analysis.
-- 2025/26: dark-dimension reanalysis using a locally exponential realization.
--
-- These edge types are intentionally different.  Parameterization ancestry and
-- proposal lineage import neither implementation identity nor numerical-manifest
-- custody downstream.
------------------------------------------------------------------------

potentialAncestorSource : Source.AttributedSource
potentialAncestorSource =
  Source.mkDOISource
    "Prateek Agrawal; Georges Obied; Paul J. Steinhardt; Cumrun Vafa"
    "On the Cosmological Implications of the String Swampland"
    "Physics Letters B 784, 271-276"
    "2018"
    "10.1016/j.physletb.2018.07.040"
    "https://doi.org/10.1016/j.physletb.2018.07.040"
    Source.academicArticleSource
    "source identified by the 2021 fading-dark-matter paper as the prior quintessence-potential parameterization; this lineage edge does not make the 2018 work the source of the later fading-DM coupling, code, or numerical manifest"
    Source.publicAttribution

potentialAncestorArXiv : String
potentialAncestorArXiv = "1806.09718"

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
    potentialParameterizationAncestorIdentified : Bool
    parentStatesSamePotentialParameterization : Bool
    ancestorImplementationInheritanceDemonstrated : Bool
    ancestorNumericalManifestIdentityDemonstrated : Bool
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
    true true false false
    true true true true true true true true
    false false false false

ancestorImplementationInheritanceStillOpen :
  ancestorImplementationInheritanceDemonstrated canonicalFadingDMParentLineageStatus
  ≡ false
ancestorImplementationInheritanceStillOpen = refl

ancestorNumericalManifestIdentityStillOpen :
  ancestorNumericalManifestIdentityDemonstrated canonicalFadingDMParentLineageStatus
  ≡ false
ancestorNumericalManifestIdentityStillOpen = refl

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

data PotentialAncestorEqualsFadingDMImplementationAncestor : Set where

data AncestorParameterizationPaysParentManifest : Set where

data ParentLineageEqualsImplementationIdentity : Set where

data ParentNormalizationPaysChildNormalization : Set where

data SameProposalFamilyMeansSameNumericalManifest : Set where

data ParentMassLawEqualsChildLocalMassLaw : Set where

data ParentPotentialLawEqualsChildLocalPotentialLaw : Set where

potentialAncestorDoesNotEqualFadingDMImplementationAncestor :
  PotentialAncestorEqualsFadingDMImplementationAncestor → ⊥
potentialAncestorDoesNotEqualFadingDMImplementationAncestor ()

ancestorParameterizationDoesNotAutoPayParentManifest :
  AncestorParameterizationPaysParentManifest → ⊥
ancestorParameterizationDoesNotAutoPayParentManifest ()

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
