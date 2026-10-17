module DASHI.Biology.BH4XPollenationKineticAdjudicationExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as Receipt
import DASHI.Core.XPollenationExact as X
import DASHI.Biology.BH4FluxCandidateRankingExact as Ranking
import DASHI.Biology.Molecular.BH4ExecutedPanelReactionReceiptExact as Panel

------------------------------------------------------------------------
-- BH4 CONSUMER OF THE GENERIC XPOLLENATION ABI
--
-- The twelve finite Rhea columns are the scientific consumer surface.  Typed
-- neighbourhoods may enrich a column with ChEBI/UniProt/PDB/SABIO/source/QID
-- coordinates, and the exact neighbourhood bytes may be published through the
-- existing ITIR logical-artifact/IPFS pipeline.  None of those coordinates pays
-- the four kinetic-to-flux gates owned by BH4FluxCandidateRankingExact.
------------------------------------------------------------------------

finiteReactionNeighbourhoodCount : Nat
finiteReactionNeighbourhoodCount = 12

finiteReactionIds : List String
finiteReactionIds = Panel.finitePanelReactionIds

rhea19897 : X.ExternalCoordinate
rhea19897 = X.external-coordinate X.rhea "RHEA:19897"

nos2 : X.ExternalCoordinate
nos2 = X.external-coordinate X.uniprot "P35228"

nos3 : X.ExternalCoordinate
nos3 = X.external-coordinate X.uniprot "P29474"

pcbd1Rhea : X.ExternalCoordinate
pcbd1Rhea = X.external-coordinate X.rhea "RHEA:11920"

pcbd1 : X.ExternalCoordinate
pcbd1 = X.external-coordinate X.uniprot "P61457"

nos2CatalysisEdge : X.XPollenationEdge
nos2CatalysisEdge =
  X.xpollenation-edge
    "bh4:RHEA:19897:UniProt:P35228"
    rhea19897
    X.catalysedBy
    nos2
    "Rhea/UniProt exact panel crosswalk"
    "Rhea 142 / UniProtKB 2026_03"
    "BH4 executed panel reaction + UniProt certificate"
    X.identityPaid
    false false false false

nos3CatalysisEdge : X.XPollenationEdge
nos3CatalysisEdge =
  X.xpollenation-edge
    "bh4:RHEA:19897:UniProt:P29474"
    rhea19897
    X.catalysedBy
    nos3
    "Rhea/UniProt exact panel crosswalk"
    "Rhea 142 / UniProtKB 2026_03"
    "BH4 executed panel reaction + UniProt certificate"
    X.identityPaid
    false false false false

pcbd1CatalysisEdge : X.XPollenationEdge
pcbd1CatalysisEdge =
  X.xpollenation-edge
    "bh4:RHEA:11920:UniProt:P61457"
    pcbd1Rhea
    X.catalysedBy
    pcbd1
    "Rhea/UniProt exact panel crosswalk"
    "Rhea 142 / UniProtKB 2026_03"
    "BH4 executed panel reaction + UniProt certificate"
    X.identityPaid
    false false false false

record BH4XPollenationCandidate : Set where
  constructor bh4-xpollenation-candidate
  field
    reactionId : String
    neighbourhoodArtifactRef : String
    neighbourhoodContentDigest : String
    neighbourhoodCid : String
    relationEvidence : List X.XPollenationEdge
    paymentGates : Ranking.FluxCandidatePaymentGates
    candidateOnly : Bool
    createsFluxBound : Bool

open BH4XPollenationCandidate public

-- A representative NOS neighbourhood is deliberately still unpaid at the
-- kinetic boundary.  NOS2 and NOS3 are separate edges because the shared Rhea
-- column does not collapse isoform, assay or compartment context.
canonicalNOSNeighbourhoodCandidate : BH4XPollenationCandidate
canonicalNOSNeighbourhoodCandidate =
  bh4-xpollenation-candidate
    "RHEA:19897"
    "xpollenation:bh4:RHEA-19897@pending#neighbourhood"
    "pending-content-digest"
    "pending-ipfs-cid"
    (nos2CatalysisEdge ∷ nos3CatalysisEdge ∷ [])
    Ranking.canonicalUnpaidFluxCandidateGates
    true
    false

record BH4XPollenationBoundary : Set where
  constructor bh4-xpollenation-boundary
  field
    neighbourhoodCreatesFluxBound : Bool
    neighbourhoodCreatesFluxBoundIsFalse : neighbourhoodCreatesFluxBound ≡ false
    rheaReactionCollapsesIsoformContext : Bool
    rheaReactionCollapsesIsoformContextIsFalse :
      rheaReactionCollapsesIsoformContext ≡ false
    sabioAssociationCreatesFluxPayment : Bool
    sabioAssociationCreatesFluxPaymentIsFalse :
      sabioAssociationCreatesFluxPayment ≡ false
    qidAdjacencyCreatesAssayApplicability : Bool
    qidAdjacencyCreatesAssayApplicabilityIsFalse :
      qidAdjacencyCreatesAssayApplicability ≡ false
    cidIdentityCreatesKineticAdmissibility : Bool
    cidIdentityCreatesKineticAdmissibilityIsFalse :
      cidIdentityCreatesKineticAdmissibility ≡ false
    oeisMatchCreatesBiochemicalIdentity : Bool
    oeisMatchCreatesBiochemicalIdentityIsFalse :
      oeisMatchCreatesBiochemicalIdentity ≡ false

open BH4XPollenationBoundary public

canonicalBH4XPollenationBoundary : BH4XPollenationBoundary
canonicalBH4XPollenationBoundary =
  bh4-xpollenation-boundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl

canonicalBH4XPollenationReceipt : Receipt.GenericReceipt
canonicalBH4XPollenationReceipt =
  Receipt.mkNonPromotingReceipt
    "BH4 xPollenation kinetic-adjudication bridge"
    "DASHI.Biology.BH4XPollenationKineticAdjudicationExact"
    "12 finite Rhea columns -> typed ChEBI/UniProt/PDB/SABIO/PMID/DOI/QID neighbourhoods -> ITIR logical artifact / CID coordinates -> existing four-gate BH4 flux adjudication"
    "lets immutable, replayable cross-domain neighbourhood evidence prioritize and explain kinetic candidates without inventing another reaction, review, transport or flux-payment calculus"
    "Rhea identity does not collapse isoforms; SABIO association is not flux payment; QID adjacency is not assay applicability; CID is byte identity not kinetic admissibility; OEIS numerical matches do not create biochemical identity"
    "agda -i . DASHI/Biology/BH4XPollenationRegression.agda"
