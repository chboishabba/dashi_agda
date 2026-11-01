module DASHI.Governance.ConsentTemporalExternalitySourceAtlasExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- SOURCE ATLAS: CONSENT / BENEFIT SHARING / TEMPORAL EXTERNALITIES
--
-- Attribution discipline:
--   source proposition / legal-institutional rule / assessment finding
--   != DASHI finite theorem
--   != universal Indigenous practice
--   != automatic legal applicability in every jurisdiction.
--
-- Stable institutional sources use institutional identifiers/URLs rather than
-- invented DOIs. Peer-reviewed sources use verified DOI where available.
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

undrip2007 : SourceReference
undrip2007 = sourceReference
  "United Nations General Assembly"
  "United Nations Declaration on the Rights of Indigenous Peoples"
  "UNGA Resolution 61/295"
  2007
  "UN resolution"
  "A/RES/61/295"
  "international declaration"
  "Articles 18, 19 and 32 calibrate participation and free, prior and informed consent in decisions/measures affecting Indigenous Peoples; does not itself define DASHI consent algebra"

unpfiiFPIC2023 : SourceReference
unpfiiFPIC2023 = sourceReference
  "United Nations Secretariat"
  "Implementing free, prior and informed consent in the context of Indigenous Peoples"
  "UN Permanent Forum on Indigenous Issues"
  2023
  "UN document symbol"
  "E/C.19/2023/6"
  "institutional implementation guidance"
  "current implementation-oriented FPIC calibration; used for scope/process distinctions, not theorem authorship"

care2020 : SourceReference
care2020 = sourceReference
  "Stephanie Russo Carroll et al."
  "The CARE Principles for Indigenous Data Governance"
  "Data Science Journal 19:43"
  2020
  "DOI"
  "10.5334/dsj-2020-043"
  "peer-reviewed Indigenous data-governance principles"
  "Collective Benefit, Authority to Control, Responsibility and Ethics; calibrates benefit/authority/responsibility/ethics as non-collapsible governance coordinates"

nagoya2010 : SourceReference
nagoya2010 = sourceReference
  "Convention on Biological Diversity"
  "Nagoya Protocol on Access to Genetic Resources and the Fair and Equitable Sharing of Benefits Arising from their Utilization"
  "Convention on Biological Diversity"
  2010
  "international protocol"
  "CBD Nagoya Protocol, Articles 5, 7, 12, 13 and 16"
  "international access-and-benefit-sharing instrument"
  "calibrates prior informed consent or approval/involvement, mutually agreed terms and fair/equitable benefit sharing as distinct obligations, subject to applicable domestic law"

gbf2022 : SourceReference
gbf2022 = sourceReference
  "Convention on Biological Diversity Conference of the Parties"
  "Kunming-Montreal Global Biodiversity Framework"
  "CBD COP15 Decision 15/4"
  2022
  "COP decision"
  "CBD/COP/DEC/15/4"
  "global biodiversity policy framework"
  "Targets 21-22 and implementation section calibrate FPIC, rights, participation/representation and access to justice; Goal C calibrates fair/equitable benefit sharing"

ipccAR6WGII2022 : SourceReference
ipccAR6WGII2022 = sourceReference
  "Intergovernmental Panel on Climate Change"
  "Climate Change 2022: Impacts, Adaptation and Vulnerability"
  "IPCC Sixth Assessment Report, Working Group II"
  2022
  "assessment report"
  "AR6 WGII, Chapter 18 / Cross-Chapter Box INDIG and Technical Summary"
  "authoritative climate assessment"
  "calibrates FPIC as necessary but not sufficient for Indigenous knowledge production, Indigenous self-determination/leadership, maladaptation risk and intergenerational context; does not supply DASHI non-factorability proofs"

ipbesTransformative2024 : SourceReference
ipbesTransformative2024 = sourceReference
  "IPBES"
  "Thematic Assessment Report on the Underlying Causes of Biodiversity Loss and the Determinants of Transformative Change"
  "Intergovernmental Science-Policy Platform on Biodiversity and Ecosystem Services"
  2024
  "DOI"
  "10.5281/zenodo.11382215"
  "intergovernmental biodiversity assessment"
  "current transformative-change assessment context; Indigenous/local knowledge dialogue procedures include approval/consent and withdrawal practices for contributed information, without transferring final assessment authorship"

wipoGRATK2024 : SourceReference
wipoGRATK2024 = sourceReference
  "World Intellectual Property Organization"
  "WIPO Treaty on Intellectual Property, Genetic Resources and Associated Traditional Knowledge"
  "WIPO"
  2024
  "international treaty"
  "adopted 24 May 2024"
  "international intellectual-property treaty"
  "calibrates patent-source disclosure for genetic resources and associated traditional knowledge; disclosure is not encoded as consent, benefit sharing, ownership or community authority"

record SourceAttributionBoundary : Set where
  constructor source-attribution-boundary
  field
    sourceMotivationEqualsDASHITheoremAuthorship : Bool
    sourceMotivationEqualsDASHITheoremAuthorshipIsFalse :
      sourceMotivationEqualsDASHITheoremAuthorship ≡ false
    oneInstitutionalFrameworkIsUniversalIndigenousLaw : Bool
    oneInstitutionalFrameworkIsUniversalIndigenousLawIsFalse :
      oneInstitutionalFrameworkIsUniversalIndigenousLaw ≡ false
    patentDisclosureEqualsConsent : Bool
    patentDisclosureEqualsConsentIsFalse : patentDisclosureEqualsConsent ≡ false
    consentEqualsBenefitSharing : Bool
    consentEqualsBenefitSharingIsFalse : consentEqualsBenefitSharing ≡ false
    assessmentFindingCreatesCommunityAuthority : Bool
    assessmentFindingCreatesCommunityAuthorityIsFalse :
      assessmentFindingCreatesCommunityAuthority ≡ false
    citedInternationalInstrumentAutomaticallyAppliesAsDomesticLaw : Bool
    citedInternationalInstrumentAutomaticallyAppliesAsDomesticLawIsFalse :
      citedInternationalInstrumentAutomaticallyAppliesAsDomesticLaw ≡ false

canonicalSourceAttributionBoundary : SourceAttributionBoundary
canonicalSourceAttributionBoundary =
  source-attribution-boundary false refl false refl false refl false refl false refl false refl
