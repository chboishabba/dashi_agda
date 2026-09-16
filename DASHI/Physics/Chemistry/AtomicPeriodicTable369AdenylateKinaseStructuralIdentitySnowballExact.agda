module DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseStructuralIdentitySnowballExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Wikimedia.SnowballExternalIdentityAvailabilityExact as Identity
import DASHI.Physics.Chemistry.AtomicPeriodicTable369AdenylateKinaseConformationalEmpiricalExact as Empirical

------------------------------------------------------------------------
-- STRUCTURAL-IDENTITY SNOWBALL FOR THE ADK CALIBRATION LANE
--
-- PDB deposition identity, publication identity, protein identity and enzyme-
-- class identity are kept as separate coordinates.  A shared UniProt accession
-- pays a same-protein navigation coordinate; it does not identify experimental
-- condition, conformation, article, PDB deposition or dynamics mechanism.
------------------------------------------------------------------------

open4AKESource : Attribution.AttributedSource
open4AKESource =
  Attribution.mkDOISource
    "Protein Data Bank / 4AKE deposition"
    "E. coli adenylate kinase open unligated structure 4AKE"
    "Protein Data Bank structural deposition"
    "1996"
    "10.2210/pdb4AKE/pdb"
    "https://www.rcsb.org/structure/4AKE"
    (Attribution.namedSourceKind "Protein Data Bank structure deposition")
    "pays the 4AKE structural-manifestation identity and deposition metadata retained by the existing empirical AdK owner; it does not pay dynamics, transition rates or a universal conformational mechanism"
    Attribution.publicAttribution

closed1AKESource : Attribution.AttributedSource
closed1AKESource =
  Attribution.mkDOISource
    "Protein Data Bank / 1AKE deposition"
    "E. coli adenylate kinase Ap5A-bound closed structure 1AKE"
    "Protein Data Bank structural deposition"
    "1992"
    "10.2210/pdb1AKE/pdb"
    "https://www.rcsb.org/structure/1AKE"
    (Attribution.namedSourceKind "Protein Data Bank structure deposition")
    "pays the 1AKE structural-manifestation identity and deposition metadata retained by the existing empirical AdK owner; it does not pay a universal catalytic transition state or complete dynamics mechanism"
    Attribution.publicAttribution

muller1996Source : Attribution.AttributedSource
muller1996Source =
  Attribution.mkDOISource
    "Muller et al."
    "Adenylate kinase motions during catalysis"
    "Structure"
    "1996"
    "10.1016/S0969-2126(96)00018-4"
    "https://doi.org/10.1016/S0969-2126(96)00018-4"
    Attribution.academicArticleSource
    "primary structural research source for the same-polypeptide-chain open/closed comparison already owned by the empirical AdK fixture"
    Attribution.publicAttribution

mullerSchulz1992Source : Attribution.AttributedSource
mullerSchulz1992Source =
  Attribution.mkDOISource
    "Muller and Schulz"
    "Structure of the complex between adenylate kinase from Escherichia coli and the inhibitor Ap5A refined at 1.9 A resolution"
    "Journal of Molecular Biology"
    "1992"
    "10.1016/0022-2836(92)90582-5"
    "https://doi.org/10.1016/0022-2836(92)90582-5"
    Attribution.academicArticleSource
    "primary structural research source associated with the 1AKE closed inhibitor-bound structure"
    Attribution.publicAttribution

open4AKESnowball : Snowball.SourceRoleSnowballReceipt open4AKESource
open4AKESnowball = Snowball.canonicalSourceRoleSnowballReceipt open4AKESource

closed1AKESnowball : Snowball.SourceRoleSnowballReceipt closed1AKESource
closed1AKESnowball = Snowball.canonicalSourceRoleSnowballReceipt closed1AKESource

muller1996Snowball : Snowball.SourceRoleSnowballReceipt muller1996Source
muller1996Snowball = Snowball.canonicalSourceRoleSnowballReceipt muller1996Source

mullerSchulz1992Snowball : Snowball.SourceRoleSnowballReceipt mullerSchulz1992Source
mullerSchulz1992Snowball = Snowball.canonicalSourceRoleSnowballReceipt mullerSchulz1992Source

------------------------------------------------------------------------
-- Stable external-identity coordinates.
------------------------------------------------------------------------

openPdbDoi : Identity.ExternalIdentityDemand
openPdbDoi =
  Identity.mkOptionalIdentityDemand
    "AdK structural identity snowball"
    "4AKE deposition DOI"
    "4AKE"
    Identity.doi
    (Identity.verified "PDB DOI retained by empirical AdK owner" "10.2210/pdb4AKE/pdb")

closedPdbDoi : Identity.ExternalIdentityDemand
closedPdbDoi =
  Identity.mkOptionalIdentityDemand
    "AdK structural identity snowball"
    "1AKE deposition DOI"
    "1AKE"
    Identity.doi
    (Identity.verified "PDB DOI retained by empirical AdK owner" "10.2210/pdb1AKE/pdb")

openPdbOfficialId : Identity.ExternalIdentityDemand
openPdbOfficialId =
  Identity.mkOptionalIdentityDemand
    "AdK structural identity snowball"
    "open PDB entry"
    "4AKE"
    Identity.officialIdentifier
    (Identity.verified "Protein Data Bank" "4AKE")

closedPdbOfficialId : Identity.ExternalIdentityDemand
closedPdbOfficialId =
  Identity.mkOptionalIdentityDemand
    "AdK structural identity snowball"
    "closed PDB entry"
    "1AKE"
    Identity.officialIdentifier
    (Identity.verified "Protein Data Bank" "1AKE")

adkUniProt : Identity.ExternalIdentityDemand
adkUniProt =
  Identity.mkOptionalIdentityDemand
    "AdK structural identity snowball"
    "E. coli K-12 adenylate kinase protein identity"
    "KAD_ECOLI"
    Identity.officialIdentifier
    (Identity.verified "UniProt" "P69441")

adkQid : Identity.ExternalIdentityDemand
adkQid =
  Identity.mkOptionalIdentityDemand
    "AdK structural identity snowball"
    "adenylate kinase entity identity"
    "adenylate kinase"
    Identity.wikidataQid
    (Identity.verified "Wikidata identity retained by empirical AdK owner" "Q356240")

openPdbObjectQid : Identity.ExternalIdentityDemand
openPdbObjectQid =
  Identity.mkOptionalIdentityDemand
    "AdK structural identity snowball"
    "4AKE exact PDB-object Wikidata identity"
    "4AKE"
    Identity.wikidataQid
    (Identity.unresolved "exact PDB-object QID not verified; enzyme-class Q356240 is not substituted")

closedPdbObjectQid : Identity.ExternalIdentityDemand
closedPdbObjectQid =
  Identity.mkOptionalIdentityDemand
    "AdK structural identity snowball"
    "1AKE exact PDB-object Wikidata identity"
    "1AKE"
    Identity.wikidataQid
    (Identity.unresolved "exact PDB-object QID not verified; enzyme-class Q356240 is not substituted")

muller1996Doi : Identity.ExternalIdentityDemand
muller1996Doi =
  Identity.mkOptionalIdentityDemand
    "AdK structural identity snowball"
    "Muller et al. 1996 article DOI"
    "Adenylate kinase motions during catalysis"
    Identity.doi
    (Identity.verified "primary article DOI retained by empirical AdK owner" "10.1016/S0969-2126(96)00018-4")

mullerSchulz1992Doi : Identity.ExternalIdentityDemand
mullerSchulz1992Doi =
  Identity.mkOptionalIdentityDemand
    "AdK structural identity snowball"
    "Muller and Schulz 1992 article DOI"
    "E. coli adenylate kinase-Ap5A complex"
    Identity.doi
    (Identity.verified "primary article DOI retained by empirical AdK owner" "10.1016/0022-2836(92)90582-5")

muller1996Qid : Identity.ExternalIdentityDemand
muller1996Qid =
  Identity.mkOptionalIdentityDemand
    "AdK structural identity snowball"
    "Muller et al. 1996 exact article QID"
    "Adenylate kinase motions during catalysis"
    Identity.wikidataQid
    (Identity.unresolved "exact article-level QID unresolved")

mullerSchulz1992Qid : Identity.ExternalIdentityDemand
mullerSchulz1992Qid =
  Identity.mkOptionalIdentityDemand
    "AdK structural identity snowball"
    "Muller and Schulz 1992 exact article QID"
    "E. coli adenylate kinase-Ap5A complex"
    Identity.wikidataQid
    (Identity.unresolved "exact article-level QID unresolved")

------------------------------------------------------------------------
-- Same-object / WrongType firewalls.
------------------------------------------------------------------------

data PdbDoiCreatesDynamicMechanism : Set where
data SharedUniProtImpliesSameExperimentalCondition : Set where
data AdkQidCreatesPdbObjectIdentity : Set where
data PdbEntryIdentityCreatesArticleIdentity : Set where

depositionIdentityDoesNotCreateDynamics : PdbDoiCreatesDynamicMechanism → ⊥
depositionIdentityDoesNotCreateDynamics ()

sharedProteinIdentityDoesNotCollapseCondition : SharedUniProtImpliesSameExperimentalCondition → ⊥
sharedProteinIdentityDoesNotCollapseCondition ()

enzymeQidDoesNotCreatePdbObjectIdentity : AdkQidCreatesPdbObjectIdentity → ⊥
enzymeQidDoesNotCreatePdbObjectIdentity ()

pdbIdentityDoesNotCreateArticleIdentity : PdbEntryIdentityCreatesArticleIdentity → ⊥
pdbIdentityDoesNotCreateArticleIdentity ()

-- Reuse the existing empirical same-sequence fixture; this module owns only
-- identity/provenance refinement, not the biological separating-pair theorem.
empiricalSameSequenceDonor : Empirical.AdKPrimarySequence
empiricalSameSequenceDonor = Empirical.eColiAdKSequence

record AdKStructuralIdentitySnowballBoundary : Set where
  constructor adk-structural-identity-snowball-boundary
  field
    openPdbDoiRetained : Bool
    closedPdbDoiRetained : Bool
    openPdbOfficialIdRetained : Bool
    closedPdbOfficialIdRetained : Bool
    uniprotIdentityRetained : Bool
    adkQidRetained : Bool
    primaryArticleDoisRetained : Bool
    openPdbObjectQidResolved : Bool
    closedPdbObjectQidResolved : Bool
    primaryArticleQidsResolved : Bool
    pdbDoiCreatesDynamicMechanism : Bool
    sharedUniProtImpliesSameExperimentalCondition : Bool
    adkQidCreatesPdbObjectIdentity : Bool
    pdbEntryIdentityCreatesArticleIdentity : Bool

canonicalAdKStructuralIdentitySnowballBoundary : AdKStructuralIdentitySnowballBoundary
canonicalAdKStructuralIdentitySnowballBoundary =
  adk-structural-identity-snowball-boundary
    true true true true true true true
    false false false
    false false false false
