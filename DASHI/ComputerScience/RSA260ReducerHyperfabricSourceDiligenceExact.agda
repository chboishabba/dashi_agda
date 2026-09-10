module DASHI.ComputerScience.RSA260ReducerHyperfabricSourceDiligenceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.EmpiricalSourceDiligenceAdmissionExact as Diligence
import DASHI.Interop.SourceDiligenceProofSearchBridgeExact as SearchBridge

------------------------------------------------------------------------
-- REDUCER-HYPERFABRIC SOURCE DILIGENCE / SNOWBALL ATTRIBUTION
--
-- Identity coordinates remain separate from proposition payment:
--   author/title/publication/DOI/canonical URL
--   Wikidata QID concept coordinates
--   OEIS sequence coordinates when genuinely applicable
--   implementation source/blob
--   execution receipt
--   mathematical admission.
------------------------------------------------------------------------

data IdentifierApplicability : Set where
  identifierRecorded : String → IdentifierApplicability
  identifierNotApplicable : IdentifierApplicability
  identifierUnresolved : IdentifierApplicability

fourColourNearLinearPrimary : Source.AttributedSource
fourColourNearLinearPrimary =
  Source.mkDOISource
    "Yuta Inoue; Ken-ichi Kawarabayashi; Atsuyuki Miyashita; Bojan Mohar; Carsten Thomassen; Mikkel Thorup"
    "The Four Color Theorem with Linearly Many Reducible Configurations and Near-Linear Time Coloring"
    "arXiv:2603.24880v2"
    "2026"
    "10.48550/arXiv.2603.24880"
    "https://arxiv.org/abs/2603.24880"
    Source.academicArticleSource
    "primary theorem/algorithm source for linearly many compatible local reductions and constant-factor recursive shrink; not an RSA theorem"
    Source.publicAttribution

coppersmithBlockWiedemannPrimary : Source.AttributedSource
coppersmithBlockWiedemannPrimary =
  Source.mkDOISource
    "Don Coppersmith"
    "Solving homogeneous linear equations over GF(2) via block Wiedemann algorithm"
    "Mathematics of Computation 62(205)"
    "1994"
    "10.1090/S0025-5718-1994-1192970-7"
    "https://doi.org/10.1090/S0025-5718-1994-1192970-7"
    Source.academicArticleSource
    "algorithm-lineage source for Block Wiedemann; does not supply the RSA-260 production matrix or the new symmetry reducer"
    Source.publicAttribution

record ConceptIdentityCoordinates : Set where
  constructor concept-identity-coordinates
  field
    graphColouringQID : IdentifierApplicability
    fourColourTheoremQID : IdentifierApplicability
    reducerHyperfabricQID : IdentifierApplicability
    nearLinearReductionOEIS : IdentifierApplicability
    ternaryAddressCountOEIS : IdentifierApplicability
open ConceptIdentityCoordinates public

currentConceptIdentityCoordinates : ConceptIdentityCoordinates
currentConceptIdentityCoordinates = concept-identity-coordinates
  (identifierRecorded "Q504843")
  (identifierRecorded "Q184410")
  identifierUnresolved
  identifierNotApplicable
  identifierNotApplicable

------------------------------------------------------------------------
-- Primary-source diligence receipt for the transferred colouring claim.
------------------------------------------------------------------------

fourColourTransferDiligence : Diligence.SourceDiligence
fourColourTransferDiligence =
  Diligence.source-diligence
    "The 2026 near-linear Four-Color work reports linearly many mutually compatible local reductions enabling constant-factor recursive shrink and O(n log n) coloring."
    fourColourNearLinearPrimary
    Diligence.primaryProposition
    true refl
    "direct inspection of the primary arXiv record/text"
    Diligence.primaryLocated
    "arXiv:2603.24880v2 abstract/theorem-level algorithm description"
    "2026-03-25 initial arXiv submission; v2 retained by the source coordinate"
    "same arXiv work identified by title/authors/arXiv id/DOI"
    "claim bounded to the planar/fixed-surface colouring algorithm stated by the paper"
    "transfer uses the batch-compatible-reduction architecture only; no RSA complexity theorem imported"
    "search retained for contradictory/qualifying statements about reducer compatibility and runtime scope"
    "DASHI interpretation: local reducers -> compatible family -> recursive shrink -> lift; interpretation is not a source proposition"
    "applicability to RSA requires independent operator/consumer equivariance receipts"

------------------------------------------------------------------------
-- Snowball acquisition/payment discipline.
------------------------------------------------------------------------

record SnowballAttributionBoundary : Set where
  constructor snowball-attribution-boundary
  field
    acquisitionMayProceedOutOfDependencyOrder : Bool
    paymentMayProceedOutOfDependencyOrder : Bool
    primarySourceSearchRequiredForEmpiricalPromotion : Bool
    DOIIsIdentityCoordinateNotProof : Bool
    QIDIsIdentityCoordinateNotProof : Bool
    OEISOnlyUsedForActualSequenceClaims : Bool
    sourceAuthorshipEqualsImplementationAuthorship : Bool
    implementationExecutionEqualsMathematicalAdmission : Bool
    searchHitEqualsFactAdmission : Bool
open SnowballAttributionBoundary public

canonicalSnowballAttributionBoundary : SnowballAttributionBoundary
canonicalSnowballAttributionBoundary = snowball-attribution-boundary
  true false true true true true false false false

sourceDiligenceBoundary : Diligence.EmpiricalSourceDiligenceBoundary
sourceDiligenceBoundary = Diligence.canonicalEmpiricalSourceDiligenceBoundary

proofSearchBoundary : SearchBridge.SourceDiligenceProofSearchBoundary
proofSearchBoundary = SearchBridge.canonicalSourceDiligenceProofSearchBoundary

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data DOIImpliesProof : Set where
data QIDImpliesAuthority : Set where
data OEISAdjacencyImpliesSequenceIdentity : Set where
data ColouringSourceImpliesRSAReduction : Set where
data ImplementationAuthorImpliesTheoremAuthor : Set where

doiDoesNotImportProof : DOIImpliesProof → ⊥
doiDoesNotImportProof ()

qidDoesNotCreateAuthority : QIDImpliesAuthority → ⊥
qidDoesNotCreateAuthority ()

oeisAdjacencyDoesNotCreateSequenceIdentity : OEISAdjacencyImpliesSequenceIdentity → ⊥
oeisAdjacencyDoesNotCreateSequenceIdentity ()

colouringSourceDoesNotCreateRSAReduction : ColouringSourceImpliesRSAReduction → ⊥
colouringSourceDoesNotCreateRSAReduction ()

implementationAuthorshipDoesNotCreateTheoremAuthorship : ImplementationAuthorImpliesTheoremAuthor → ⊥
implementationAuthorshipDoesNotCreateTheoremAuthor ()
