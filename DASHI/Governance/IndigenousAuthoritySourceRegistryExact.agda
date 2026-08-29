module DASHI.Governance.IndigenousAuthoritySourceRegistryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- INDIGENOUS AUTHORITY / DATA GOVERNANCE SOURCE REGISTRY
--
-- Identifier discipline follows Docs/SourceAttributionPolicy.md:
-- verified DOI where one is attached to the cited work; otherwise ISBN or
-- stable institutional source.  Source role != authorship of DASHI's theorem.
-- OCAP is specifically a First Nations framework and is not generalized to all
-- Indigenous peoples.
------------------------------------------------------------------------

record SourceReference : Set where
  constructor sourceReference
  field
    authors : String
    title : String
    venue : String
    year : Nat
    identifierKind : String
    identifier : String
    sourceClass : String
    boundedRole : String

open SourceReference public

care2020 : SourceReference
care2020 = sourceReference
  "Stephanie Russo Carroll et al."
  "The CARE Principles for Indigenous Data Governance"
  "Data Science Journal 19:43"
  2020
  "DOI"
  "10.5334/dsj-2020-043"
  "peer-reviewed Indigenous data-governance principles"
  "Collective Benefit, Authority to Control, Responsibility and Ethics; supports relational governance of data use and self-determination, not a DASHI-specific authorization algebra"

ocapFNIGC : SourceReference
ocapFNIGC = sourceReference
  "First Nations Information Governance Centre"
  "The First Nations Principles of OCAP®"
  "FNIGC institutional framework"
  2022
  "stable institutional source"
  "fnigc.ca/ocap-training and FNIGC OCAP brochure"
  "First Nations institutional data-governance framework"
  "Ownership, Control, Access and Possession; specifically First Nations, including control across research/information-management stages; no DOI asserted"

localContextsTK : SourceReference
localContextsTK = sourceReference
  "Local Contexts"
  "Traditional Knowledge Labels"
  "Local Contexts institutional framework"
  2026
  "stable institutional source"
  "localcontexts.org/labels/traditional-knowledge-labels"
  "Indigenous cultural-authority / provenance-protocol-permission framework"
  "Provenance, Protocol and Permission label families and community-specific rules for access/use; current institutional source date used only as registry snapshot, not origin-date claim"

smith2022 : SourceReference
smith2022 = sourceReference
  "Linda Tuhiwai Smith"
  "Decolonizing Methodologies: Research and Indigenous Peoples"
  "Bloomsbury Academic, third edition"
  2022
  "ISBN"
  "9781350346086"
  "Indigenous-authored scholarly monograph"
  "source for imperialism/research critique and the constructive Indigenous research-agenda distinction; no DOI asserted for this edition"

moretonRobinson2015 : SourceReference
moretonRobinson2015 = sourceReference
  "Aileen Moreton-Robinson"
  "The White Possessive: Property, Power, and Indigenous Sovereignty"
  "University of Minnesota Press"
  2015
  "DOI"
  "10.5749/minnesota/9780816692149.001.0001"
  "Indigenous-authored scholarly monograph"
  "source for white possession / Indigenous sovereignty analysis and the distinction between settler legal-symbolic recognition and Indigenous sovereignty; print ISBN for DOI edition 9780816692149"

whyte2021 : SourceReference
whyte2021 = sourceReference
  "Kyle Powys Whyte"
  "Time as Kinship"
  "The Cambridge Companion to Environmental Humanities, pp. 39-55"
  2021
  "DOI"
  "10.1017/9781009039369.005"
  "Indigenous-authored scholarly chapter"
  "source for kinship rather than merely linear narration of time and inseparability of justice from climate experience; does not imply mathematical linear time is invalid"

record IndigenousAuthoritySourceBoundary : Set where
  constructor indigenousAuthoritySourceBoundary
  field
    ocapGeneralizedToAllIndigenousPeoples : Bool
    ocapGeneralizedToAllIndigenousPeoplesIsFalse :
      ocapGeneralizedToAllIndigenousPeoples ≡ false
    governanceFrameworkTransfersCommunityAuthorityToDASHI : Bool
    governanceFrameworkTransfersCommunityAuthorityToDASHIIsFalse :
      governanceFrameworkTransfersCommunityAuthorityToDASHI ≡ false
    scholarlyCitationTransfersSovereignty : Bool
    scholarlyCitationTransfersSovereigntyIsFalse :
      scholarlyCitationTransfersSovereignty ≡ false
    sourceCitationTransfersTheoremAuthorship : Bool
    sourceCitationTransfersTheoremAuthorshipIsFalse :
      sourceCitationTransfersTheoremAuthorship ≡ false

canonicalIndigenousAuthoritySourceBoundary : IndigenousAuthoritySourceBoundary
canonicalIndigenousAuthoritySourceBoundary =
  indigenousAuthoritySourceBoundary false refl false refl false refl false refl
