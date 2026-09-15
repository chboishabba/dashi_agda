module DASHI.Biology.Protein.TRPA1SourceAttributionEnvelopeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Biology.Protein.TRPA1SingleResidueThermalAdaptationExact as TRPA1

------------------------------------------------------------------------
-- REPOSITORY-NATIVE SOURCE ATTRIBUTION ENVELOPE FOR THE ORIGINAL TRPA1 TASK
--
-- Feng et al.'s biological propositions remain owned by the existing TRPA1
-- formalisation.  This owner upgrades only the source/identity layer using the
-- same AttributedSourceCore + ExternalIdentityDemand machinery used elsewhere.
-- DOI / PMID / PMCID / canonical URL identify manifestations; none imports
-- proof, biological truth, universal mechanism, or same-object protein state.
------------------------------------------------------------------------

feng2026Source : Attribution.AttributedSource
feng2026Source = Attribution.mkDOISource
  "Tian-Yu Feng; Wenqi Dong; Dong Zheng; Lei Han; Jiatong Chen; Xuanye Wu; Xiancui Lu; Shilong Yang; Wei-Guo Du"
  "A single-point mutation in TRPA1 drives heat resilience in oviparous embryos"
  "Science Advances 12(36):eaee3948"
  "2026"
  "10.1126/sciadv.aee3948"
  "https://www.science.org/doi/10.1126/sciadv.aee3948"
  Attribution.academicArticleSource
  "primary source for the bounded TRPA1 residue/gating, embryo-intervention, and Ca2+-SP1-CADM1/MDGA1 propositions already formalised by the existing TRPA1 owner; citation imports neither proof nor universal authority"
  Attribution.publicAttribution

feng2026SourceRoleReceipt : Snowball.SourceRoleSnowballReceipt feng2026Source
feng2026SourceRoleReceipt = Snowball.canonicalSourceRoleSnowballReceipt feng2026Source

articleDOI : Identity.ExternalIdentityDemand
articleDOI = Identity.mkOptionalIdentityDemand
  "TRPA1 original protein task attribution envelope"
  "Feng et al. 2026 DOI"
  "A single-point mutation in TRPA1 drives heat resilience in oviparous embryos"
  Identity.doi
  (Identity.verified "Science Advances / PubMed" "10.1126/sciadv.aee3948")

articlePMID : Identity.ExternalIdentityDemand
articlePMID = Identity.mkOptionalIdentityDemand
  "TRPA1 original protein task attribution envelope"
  "Feng et al. 2026 PubMed identifier"
  "A single-point mutation in TRPA1 drives heat resilience in oviparous embryos"
  Identity.officialIdentifier
  (Identity.verified "PubMed indexed 2026-09" "42685214")

articlePMCID : Identity.ExternalIdentityDemand
articlePMCID = Identity.mkOptionalIdentityDemand
  "TRPA1 original protein task attribution envelope"
  "Feng et al. 2026 PubMed Central identifier"
  "A single-point mutation in TRPA1 drives heat resilience in oviparous embryos"
  Identity.officialIdentifier
  (Identity.verified "PubMed Central indexed 2026-09" "PMC13537265")

articleCanonicalURL : Identity.ExternalIdentityDemand
articleCanonicalURL = Identity.mkOptionalIdentityDemand
  "TRPA1 original protein task attribution envelope"
  "Feng et al. 2026 canonical article link"
  "A single-point mutation in TRPA1 drives heat resilience in oviparous embryos"
  Identity.canonicalURL
  (Identity.verified
    "Science Advances"
    "https://www.science.org/doi/10.1126/sciadv.aee3948")

articleQID : Identity.ExternalIdentityDemand
articleQID = Identity.mkOptionalIdentityDemand
  "TRPA1 original protein task attribution envelope"
  "Feng et al. 2026 exact article Wikidata identity"
  "A single-point mutation in TRPA1 drives heat resilience in oviparous embryos"
  Identity.wikidataQid
  (Identity.unresolved "exact article-level Wikidata QID unresolved; no neighbouring protein/person QID substituted")

identityDemands : List Identity.ExternalIdentityDemand
identityDemands = articleDOI ∷ articlePMID ∷ articlePMCID ∷ articleCanonicalURL ∷ articleQID ∷ []

------------------------------------------------------------------------
-- Existing biological theorem surface remains the donor.
------------------------------------------------------------------------

thermalAdaptationBoundary : TRPA1.TRPA1ThermalAdaptationBoundary
thermalAdaptationBoundary = TRPA1.canonicalTRPA1ThermalAdaptationBoundary

thermalGateReceipt : TRPA1.SingleResidueThermalGateReceipt
thermalGateReceipt = TRPA1.feng2026ThermalGateReceipt

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data IdentityCreatesBiologicalClaim : Set where
data PMIDCreatesMechanism : Set where
data PMCIDCreatesSameObjectProteinState : Set where
data CitationImportsProofOrAuthority : Set where

identityDoesNotCreateBiologicalClaim : IdentityCreatesBiologicalClaim → ⊥
identityDoesNotCreateBiologicalClaim ()

pmidDoesNotCreateMechanism : PMIDCreatesMechanism → ⊥
pmidDoesNotCreateMechanism ()

pmcidDoesNotCreateSameObjectState : PMCIDCreatesSameObjectProteinState → ⊥
pmcidDoesNotCreateSameObjectState ()

citationDoesNotImportProofOrAuthority : CitationImportsProofOrAuthority → ⊥
citationDoesNotImportProofOrAuthority ()

record TRPA1SourceAttributionBoundary : Set where
  constructor trpa1-source-attribution-boundary
  field
    doiRetained : Bool
    pmidRetained : Bool
    pmcidRetained : Bool
    canonicalScienceLinkRetained : Bool
    articleQidExplicitlyUnresolved : Bool
    reusesAttributedSourceCore : Bool
    existingFengBiologyRetainedAsDonor : Bool
    identityCreatesBiologicalClaim : Bool
    citationImportsProofOrAuthority : Bool
open TRPA1SourceAttributionBoundary public

canonicalTRPA1SourceAttributionBoundary : TRPA1SourceAttributionBoundary
canonicalTRPA1SourceAttributionBoundary = trpa1-source-attribution-boundary
  true true true true true true true false false
