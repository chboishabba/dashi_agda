module DASHI.ComputerScience.RSA260GNFSComponentProvenanceExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as SnowballAttribution
import DASHI.Core.SnowballOSINTAcquisitionInvariantExact as OSINT

------------------------------------------------------------------------
-- RSA-260 GNFS COMPONENT-LEVEL PROVENANCE
--
-- Consumer: distinguish algorithm ancestry, upstream software ownership,
-- downstream modification ownership, and execution role for each pipeline
-- component.  Similar role or inherited interface never implies same author,
-- same code, same revision, or semantic equivalence.
------------------------------------------------------------------------

data GNFSStage : Set where
  polynomialSelectionStage1 : GNFSStage
  polynomialSelectionStage2 : GNFSStage
  latticeSieving : GNFSStage
  filtering : GNFSStage
  sparseLinearAlgebra : GNFSStage
  squareRoot : GNFSStage

data ComponentRelation : Set where
  algorithmDescribedBy : ComponentRelation
  upstreamSoftwareImplements : ComponentRelation
  downstreamImplementationDerivedFrom : ComponentRelation
  downstreamImplementationModified : ComponentRelation
  downstreamImplementationNew : ComponentRelation
  downstreamProgramUntouched : ComponentRelation
  executedInReportedRun : ComponentRelation

data AttributionStrength : Set where
  primaryProjectStatement : AttributionStrength
  firstPartyExecutionAccount : AttributionStrength
  primaryResearchPublication : AttributionStrength
  secondaryOnly : AttributionStrength
  unresolvedStrength : AttributionStrength

record ComponentProvenanceEdge : Set where
  constructor component-provenance-edge
  field
    stage : GNFSStage
    relation : ComponentRelation
    subject : String
    object : String
    sourceReference : String
    strength : AttributionStrength
    exactSourceRevisionKnown : Bool
    independentExecutionReproduced : Bool
    semanticEquivalenceProved : Bool
open ComponentProvenanceEdge public

------------------------------------------------------------------------
-- Primary / project sources.
------------------------------------------------------------------------

cadoProjectSource : Attribution.AttributedSource
cadoProjectSource =
  Attribution.mkNoDOISource
    "The CADO-NFS Development Team"
    "CADO-NFS, An Implementation of the Number Field Sieve Algorithm"
    "official CADO-NFS project documentation"
    "2026"
    "https://cado-nfs.gitlabpages.inria.fr/"
    Attribution.institutionalSource
    "primary software-provenance carrier: identifies CADO-NFS as an implementation of NFS and documents stage algorithms including polynomial selection, lattice sieving, filtering, block Wiedemann linear algebra, and square root"
    Attribution.publicAttribution

luRSA260Source : Attribution.AttributedSource
luRSA260Source =
  Attribution.mkNoDOISource
    "Eric Lu"
    "Factoring RSA-260"
    "Cognition"
    "2026"
    "https://cognition.com/blog/factoring-rsa-260"
    Attribution.practitionerSource
    "first-party execution/modification account: identifies which CADO-NFS pipeline components were GPU-adapted, optimized, newly implemented, or left untouched for the RSA-260 work"
    Attribution.publicAttribution

coppersmithBlockWiedemannSource : Attribution.AttributedSource
coppersmithBlockWiedemannSource =
  Attribution.mkDOISource
    "Don Coppersmith"
    "Solving homogeneous linear equations over GF(2) via block Wiedemann algorithm"
    "Mathematics of Computation 62(205), 333-350"
    "1994"
    "10.1090/S0025-5718-1994-1192970-7"
    "https://research.ibm.com/publications/solving-homogeneous-linear-equations-over-gf2-via-block-wiedemann-algorithm"
    Attribution.academicArticleSource
    "primary algorithm source for block Wiedemann over GF(2); does not identify any CADO implementation or RSA-260 execution"
    Attribution.publicAttribution

cavallarFilteringSource : Attribution.AttributedSource
cavallarFilteringSource =
  Attribution.mkDOISource
    "Stefania Cavallar"
    "Strategies in Filtering in the Number Field Sieve"
    "Algorithmic Number Theory Symposium / LNCS"
    "2000"
    "10.1007/10722028_11"
    "https://ir.cwi.nl/pub/2078"
    Attribution.academicArticleSource
    "primary research carrier for NFS filtering strategies; does not identify the exact CADO or RSA-260 filtering implementation"
    Attribution.publicAttribution

msieveSource : Attribution.AttributedSource
msieveSource =
  Attribution.mkNoDOISource
    "Jason Papadopoulos / Msieve contributors"
    "Msieve NFS polynomial-selection documentation"
    "Msieve source repository documentation"
    "2026"
    "https://github.com/upiter/msieve/blob/master/Readme.nfs"
    Attribution.practitionerSource
    "software/procedure provenance for Msieve NFS polynomial selection, including stage-1 GPU support; Lu separately reports components from msieve in the RSA-260 GPU-adapted CADO stage-1 polyselect"
    Attribution.publicAttribution

cadoSnowball : SnowballAttribution.SourceRoleSnowballReceipt cadoProjectSource
cadoSnowball = SnowballAttribution.canonicalSourceRoleSnowballReceipt cadoProjectSource

luSnowball : SnowballAttribution.SourceRoleSnowballReceipt luRSA260Source
luSnowball = SnowballAttribution.canonicalSourceRoleSnowballReceipt luRSA260Source

------------------------------------------------------------------------
-- Exact currently supported component edges.
------------------------------------------------------------------------

stage1CadoImplementation : ComponentProvenanceEdge
stage1CadoImplementation =
  component-provenance-edge
    polynomialSelectionStage1 upstreamSoftwareImplements
    "CADO-NFS stage-1 polynomial selection"
    "NFS polynomial selection algorithms documented by the CADO project"
    "https://cado-nfs.gitlabpages.inria.fr/"
    primaryProjectStatement
    false false false

stage1RSA260Modification : ComponentProvenanceEdge
stage1RSA260Modification =
  component-provenance-edge
    polynomialSelectionStage1 downstreamImplementationModified
    "RSA-260 GPU-adapted stage-1 polyselect"
    "CADO-NFS stage-1 polyselect, with components from msieve"
    "Eric Lu, Factoring RSA-260, 2026-09-09"
    firstPartyExecutionAccount
    false false false

stage1MsieveContribution : ComponentProvenanceEdge
stage1MsieveContribution =
  component-provenance-edge
    polynomialSelectionStage1 downstreamImplementationDerivedFrom
    "RSA-260 GPU-adapted stage-1 polyselect"
    "components from msieve"
    "Eric Lu, Factoring RSA-260; Msieve Readme.nfs supplies upstream software context"
    firstPartyExecutionAccount
    false false false

stage2Untouched : ComponentProvenanceEdge
stage2Untouched =
  component-provenance-edge
    polynomialSelectionStage2 downstreamProgramUntouched
    "RSA-260 polyselect_ropt"
    "CADO-NFS polyselect_ropt"
    "Eric Lu, Factoring RSA-260, 2026-09-09"
    firstPartyExecutionAccount
    false false false

lasCadoImplementation : ComponentProvenanceEdge
lasCadoImplementation =
  component-provenance-edge
    latticeSieving upstreamSoftwareImplements
    "CADO-NFS las"
    "lattice sieving"
    "https://cado-nfs.gitlabpages.inria.fr/"
    primaryProjectStatement
    false false false

lasRSA260Modification : ComponentProvenanceEdge
lasRSA260Modification =
  component-provenance-edge
    latticeSieving downstreamImplementationDerivedFrom
    "RSA-260 GPU-optimized lattice siever"
    "CADO-NFS las"
    "Eric Lu, Factoring RSA-260, 2026-09-09"
    firstPartyExecutionAccount
    false false false

filteringAlgorithmSource : ComponentProvenanceEdge
filteringAlgorithmSource =
  component-provenance-edge
    filtering algorithmDescribedBy
    "NFS filtering"
    "Stefania Cavallar, Strategies in Filtering in the Number Field Sieve"
    "doi:10.1007/10722028_11"
    primaryResearchPublication
    false false false

filteringRSA260Modification : ComponentProvenanceEdge
filteringRSA260Modification =
  component-provenance-edge
    filtering downstreamImplementationModified
    "RSA-260 filtering/merge/replay path"
    "CADO-NFS dup/purge and merge/replay programs"
    "Eric Lu, Factoring RSA-260, 2026-09-09"
    firstPartyExecutionAccount
    false false false

blockWiedemannAlgorithmSource : ComponentProvenanceEdge
blockWiedemannAlgorithmSource =
  component-provenance-edge
    sparseLinearAlgebra algorithmDescribedBy
    "block Wiedemann over GF(2)"
    "Don Coppersmith, 1994"
    "doi:10.1090/S0025-5718-1994-1192970-7"
    primaryResearchPublication
    false false false

blockWiedemannCadoImplementation : ComponentProvenanceEdge
blockWiedemannCadoImplementation =
  component-provenance-edge
    sparseLinearAlgebra upstreamSoftwareImplements
    "CADO-NFS linear algebra"
    "block Wiedemann"
    "https://cado-nfs.gitlabpages.inria.fr/"
    primaryProjectStatement
    false false false

blockWiedemannRSA260Implementation : ComponentProvenanceEdge
blockWiedemannRSA260Implementation =
  component-provenance-edge
    sparseLinearAlgebra downstreamImplementationNew
    "RSA-260 GPU-optimized block Wiedemann implementation"
    "block Wiedemann role in the CADO-NFS pipeline"
    "Eric Lu, Factoring RSA-260, 2026-09-09"
    firstPartyExecutionAccount
    false false false

sqrtCadoImplementation : ComponentProvenanceEdge
sqrtCadoImplementation =
  component-provenance-edge
    squareRoot upstreamSoftwareImplements
    "CADO-NFS square-root stage"
    "NFS square-root step"
    "https://cado-nfs.gitlabpages.inria.fr/"
    primaryProjectStatement
    false false false

sqrtRSA260Modification : ComponentProvenanceEdge
sqrtRSA260Modification =
  component-provenance-edge
    squareRoot downstreamImplementationModified
    "RSA-260 GPU-accelerated sqrt"
    "CADO-NFS square-root stage"
    "Eric Lu, Factoring RSA-260, 2026-09-09"
    firstPartyExecutionAccount
    false false false

------------------------------------------------------------------------
-- Source-role / WrongType firewalls.
------------------------------------------------------------------------

data AlgorithmSourceImpliesSoftwareAuthorship : Set where
data UpstreamSoftwareImpliesDownstreamModificationAuthorship : Set where
data DerivedFromImpliesSemanticEquivalence : Set where
data UntouchedProgramImpliesWholePipelineUnmodified : Set where
data ComponentFromMsieveImpliesWholeStageIsMsieve : Set where
data NewGPUImplementationImpliesNewAlgorithm : Set where
data ProjectDocsIdentifyExecutedRevision : Set where
data FirstPartyRunAccountIsIndependentReproduction : Set where

algorithmSourceDoesNotCreateSoftwareAuthorship :
  AlgorithmSourceImpliesSoftwareAuthorship → ⊥
algorithmSourceDoesNotCreateSoftwareAuthorship ()

upstreamDoesNotOwnDownstreamModifications :
  UpstreamSoftwareImpliesDownstreamModificationAuthorship → ⊥
upstreamDoesNotOwnDownstreamModifications ()

derivationDoesNotProveSemanticEquivalence :
  DerivedFromImpliesSemanticEquivalence → ⊥
derivationDoesNotProveSemanticEquivalence ()

untouchedPartDoesNotMakePipelineUntouched :
  UntouchedProgramImpliesWholePipelineUnmodified → ⊥
untouchedPartDoesNotMakePipelineUntouched ()

msieveComponentsDoNotMakeWholeStageMsieve :
  ComponentFromMsieveImpliesWholeStageIsMsieve → ⊥
msieveComponentsDoNotMakeWholeStageMsieve ()

newImplementationDoesNotMeanNewAlgorithm :
  NewGPUImplementationImpliesNewAlgorithm → ⊥
newImplementationDoesNotMeanNewAlgorithm ()

projectDocsDoNotIdentifyExecutedRevision :
  ProjectDocsIdentifyExecutedRevision → ⊥
projectDocsDoNotIdentifyExecutedRevision ()

firstPartyAccountDoesNotBecomeIndependentReproduction :
  FirstPartyRunAccountIsIndependentReproduction → ⊥
firstPartyAccountDoesNotBecomeIndependentReproduction ()

------------------------------------------------------------------------
-- Current component-level residual frontier.
------------------------------------------------------------------------

record RSA260ComponentProvenanceBoundary : Set where
  constructor rsa260-component-provenance-boundary
  field
    stageRolesSeparated : Bool
    upstreamAndDownstreamAuthorshipSeparated : Bool
    msieveContributionRetainedAtComponentScope : Bool
    exactCadoUpstreamRevisionKnown : Bool
    exactModifiedSourceRevisionPubliclyBound : Bool
    componentSemanticEquivalenceProved : Bool
    independentExecutionReproduced : Bool
    exactBinaryOrContainerDigestKnown : Bool
open RSA260ComponentProvenanceBoundary public

canonicalRSA260ComponentProvenanceBoundary : RSA260ComponentProvenanceBoundary
canonicalRSA260ComponentProvenanceBoundary =
  rsa260-component-provenance-boundary
    true true true false false false false false
